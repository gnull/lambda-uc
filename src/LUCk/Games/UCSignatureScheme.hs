module LUCk.Games.UCSignatureScheme where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity
import Data.List (find)

import LUCk.Types
import LUCk.Syntax
import LUCk.Syntax.Async.Eval

import LUCk.UC
import LUCk.UC.Core
import LUCk.UC.Flatten

import Data.Type.Equality

import LUCk.Games.SignatureScheme (SpSignatureScheme, SignatureScheme(..))

import qualified Data.Map as Map

type Message = String
type Pk = String
type Sk = String
type Sign = String

data SignReq
  = KGen
  | Sign Message
  | Ver Pk Message Sign

data SignResp
  = RespKGen Pk
  | RespSign Sign
  | RespVer Bool
  | RespErr

data Started = Started

data SignSid = SignSid
  { signSidSigner :: Pid
  , signSid' :: String
  }

type SignatureScheme' = SignatureScheme String String String String

data UnexpectedSenderEx = UnexpectedSenderEx

signatureIF :: SingleSidIdeal' SignSid
                               (HListPort SignatureScheme' Started)
                               (HListPort SignReq SignResp)
                               '[]
signatureIF (Sid (SignSid {signSidSigner} )) = process' InitStatusIndexRetAbsent $ M.do
    m <- tryRerun $ myRecvOne InList2
    (scheme, sk, pk) <- initHelper
    state <- xcatch (processReq scheme sk pk m Map.empty) $ handleOne $ M.do
      send pingAddr $ PidMess "" ()
      xreturn Map.empty
    loopHelper scheme sk pk state

  where

    pingAddr = InList0
    advAddr = InList1
    callerAddr = InList2

    initHelper = M.do
      send advAddr $ Started
      scheme <- tryRerun $ myRecvOne advAddr
      (sk, pk) <- xlift $ sigKey scheme
      xreturn (scheme, sk, pk)

    loopHelper scheme sk pk state = M.do
      state' <- tryRerun $ M.do
        m <- myRecvOne InList2
        processReq scheme sk pk m state
      loopHelper scheme sk pk state'

    processReq scheme sk pk (PidMess pid req) state = case req of
      KGen -> M.do
        send callerAddr $ PidMess pid $ RespKGen pk
        xreturn state
      Sign m -> M.do
        sig <- xlift $ sigSign scheme sk m
        let resp = case (m, sig, pk) `Map.lookup` state == Just False
                        || pid /= signSidSigner
                   of
              True -> RespErr
              False -> RespSign sig
        send callerAddr $ PidMess pid resp
        xreturn $ Map.insert (m, sig, pk) True state
      Ver pk' m sig -> M.do
        let resp = case (pk' == pk, (m, sig, pk') `Map.lookup` state) of
                (True, Just True) -> True
                (True, Nothing) -> False
                -- ^This condition needs to be modified if we include corruptions
                (_, Just b) -> b
                (_, Nothing) -> sigVer scheme pk' m sig
        send callerAddr $ PidMess pid $ RespVer resp
        xreturn $ Map.insert (m, sig, pk') resp state

    myRecvOne :: PortInList x y ports
              -> AsyncExT '[UnexpectedSenderEx :@ NextSend] ports NextRecv NextSend y
    myRecvOne = recvOneEx Here UnexpectedSenderEx

    handleOne :: AsyncT ports i j a
              -> InList '[e' :@ i] (e :@ b) -> e -> AsyncT ports b j a
    handleOne f Here = \_ -> f
    handleOne _ (There contra) = case contra of {}

    tryRerun :: AsyncExT '[UnexpectedSenderEx :@ NextSend]
                         (PidMess () :> PidMess Void : ports)
                         NextRecv i a
             -> AsyncT (PidMess () :> PidMess Void : ports)
                       NextRecv i a
    tryRerun f = xcatch f $ handleOne $ M.do
      send pingAddr $ PidMess "" ()
      tryRerun f

signatureProto :: SingleSidReal SignSid
                                (HListPort SignatureScheme' Started)
                                (HListPort SignReq SignResp)
                                '[]
signatureProto = undefined
