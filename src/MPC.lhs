> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE RankNTypes #-}
> module MPC where
> import Control.Monad
> import Data.Bits
> import qualified Data.Maybe as M
> import qualified Control.Concurrent.Chan as C
> import qualified Control.Concurrent.Async as A
> import System.Random (randomIO)
> import Control.Monad.Reader

Lines that start with > are code blocks compiled and type-checked by Haskell
compiler. Lines that start with < are also code blocks, but compiler ignores
them; these are good to show examples, or snippets that may not possibly
compile. Normal lines are just text for you to read.

First, let's define a Domain-Specific Language where we will be expressing
our computations. It's going to be an imperative language where you have
special operations "send message m to party p", receive message, generate a
random value. These three things are the only ways our programs are allowed to
interact with the outside world. Programs are also allowed to do any arbitrary
computations locally.

> class (Monad m, Eq p) => Algo p m | m -> p where

Since it's an imperative DSL, we define a monad for it. We make it a typeclass
to keep it abstract, and not dependent on a concrete implementation (Haskell's
typeclass is like interface in Java). So the programs in this DSL can say
things like "send message to party P1", but they can't rely on what it could
mean.

>   send :: p -> String -> m ()

This action is for sending messages. It takes two parameters: destination
party, and String message to send, and empty tuple (), i.e. nothing.

>   recv :: m (p, String)

This action receives any message that some other party may have sent us. If
there's no messages, it blocks until they arrive.

>   rand :: m Bool

And the last function to generate randomness. For simplicity, we can assume it
generates exactly one bit. If you want more, call this multiple times.

Now, we can practice writing code in this new model. Let's make an algorithm
that picks n random bits and sends them (rendered as String with "True" and
"False") to some party.

> sendRandBits :: Algo p m => p -> Int -> m ()
> sendRandBits party n = do
>   bits <- replicateM n rand
>   -- ^repeat rand n times, collect results into a list
>   send party (show bits)
>   -- ^render bits as a string, send the result to party

This algorithm is not very useful. Since the other party could generate
thouse bits itself, and we're not returning the bits for use outside of this
algorithm. Let's try to something better:

> establishSharedRandomness :: Algo p m => p -> Int -> m [Bool]
> establishSharedRandomness party n = do
>   bits <- replicateM n rand
>   send party (show bits)
>   (party', bits') <- recv
>   -- party' here is the sender of the message we got, bits' is the message
>   -- they sent us. Normally, we would need to check if party' equals party,
>   -- i.e. that it's the one we expect the message from, but let's (for
>   -- simplicity) ignore it for now and assume that there exists only one
>   -- party other than us.
>   let bits'' = read bits'
>   return (zipWith xor bits bits'')
>   -- ^xor the lists and return the result

So now if we had two parties P1 and P2, we could run

< establishSharedRandomness P2 8

as P1, and

< establishSharedRandomness P1 8

as P2 (inside some evaluation system that passes messages between them — more
on this in the following) to have both of them generate 8 bits, send them to
each other and return the xor of two bitstrings.

In order to actually run simulations of these algorithms interacting with each
other, we will need to create a specific instance of Algo monad, that will
define what the send, recv and rand mean exactly. And then we will need to
make something that can take a bunch of Algo monads that specify algorithms
of multiple parties, connect them and run together. Note that we are making
this simulator just to define the semantics, specify what is a protocol and
what it means to execute a protocol, and maybe play around with definitions to
understand them better, not to actually implement things in real life (it's not
a goal for this code).

One way to implement the execution of parties is multithreading. We can pass
messages in this case through a channel. First, we define the data that each
thread will use to communicate with others:

> data ThreadData p = ThreadData
>   { self :: p
>     -- ^Our own identifier
>   , recvQueue :: C.Chan (p, String)
>     -- ^Inbox for received messages. p here will be the sender party identifier
>   , sendQueues :: [(p, C.Chan (p, String))]
>     -- ^Inboxes of other threads. List of channels where this thread should
>     -- put messages it sends to other threads
>   }

Now we finally show how we can implement Algo monad operations inside IO
monad. IO is the Haskell's builtin monad that allows *anything*, i.e. any type
of I/O operations like reading files, talking to network, creating threads,
IPC. Since we said we will implement interaction netween our parties as IPC, IO
is the perfect choice for us.

> type AlgoIO p = ReaderT (ThreadData p) IO

The above might be confusing, but it's purely technical, you can just ignore it
at first reading. It says that AlgoIO is just like IO monad, but it also has an
immutable ThreadData attached to it which AlgoIO actions can access. Now, we
show how send, recv and rand are implemented in AlgoIO.

> instance (Eq p) => Algo p (AlgoIO p) where
>   send p m = ReaderT $ \t -> do
>     let dest = M.fromJust (lookup p (sendQueues t))
>     -- ^Find the destination queue in the list (panic if it's not there)
>     C.writeChan dest (self t, m)
>     -- ^Write (our name, message) into the channel
>   recv = ReaderT $ \t -> do
>     C.readChan (recvQueue t)
>     -- ^Just produce the first value from the inbox queue
>   rand = ReaderT $ \_ -> do
>     randomIO
>     -- ^This function is polymorphic over the return type, i.e. it
>     -- produces a random value of any type that you want (which is derived
>     -- automatically).

Nice! We're almost good to go. The code above is enough to run one party. Now,
let's make a function that runs two parties together, letting them talk to each
other. Since it's only two parties, let's assume without loss of generality
that their names are Alice and Bob.

> data Party2Names = Alice | Bob
>   deriving (Eq)
>
> run2P
>   :: (forall m. Algo Party2Names m => m a) -- ^First party (Alice) algorithm
>   -> (forall m. Algo Party2Names m => m b) -- ^Second party (Bob) algorithm
>   -> IO (a, b) -- ^The values their algorithms output when they halt
> run2P aAlg bAlg = do
>   -- |First, we create two channels and make a destinations list out of them
>   aChan <- C.newChan
>   bChan <- C.newChan
>   let dest = [(Alice, aChan), (Bob, bChan)]
>   -- |Now, create the inner states that the algorithms will be using
>   let aData = ThreadData { self = Alice, recvQueue = aChan, sendQueues = dest }
>   let bData = ThreadData { self =   Bob, recvQueue = bChan, sendQueues = dest }
>   -- |Everything's ready to start the threads. The concurrently function
>   -- takes two IO actions, runs them in parallel, collects the return values
>   -- are returns them as a (a, b) pair.
>   A.concurrently (runReaderT aAlg aData) (runReaderT bAlg bData)

Now you can actually simualte a protocol between the establishSharedRandomness
algorithms talking to each other which we've implemented above.

> establishSharedRandomnessProtocol :: IO ([Bool], [Bool])
> establishSharedRandomnessProtocol = run2P alice bob
>   where
>     alice :: Algo Party2Names m => m [Bool]
>     alice = establishSharedRandomness Bob 8
>     bob :: Algo Party2Names m => m [Bool]
>     bob = establishSharedRandomness Alice 8

In this concrete case the algorithms of both Alice and Bob are implemented
using establishSharedRandomness function only because the protocol is highly
symmetrical. In principle, nothing prevents the things that you pass to run2P
to do some completely different actions (and indeed, in many real protocols it
will be the case). It's up to the person who implements Algo actions to ensure
there's no deadlocking (say, when both parties are waiting for each other's
message) or infinite loops of whatever.

Now, if you open `stack ghci' and type

< establishSharedRandomnessProtocol

in the prompt, you will see the outputs of the two parties in this protocol.
