module LUCk.Games.UCSignatureScheme where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity
import Data.List (find)

import LUCk.Types
import LUCk.Syntax

import LUCk.UC
import LUCk.UC.Core

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

pattern JustMess :: m -> HListPair '[] '[m]
pattern JustMess m = (HNil, HListMatch1 (Identity m))
{-# COMPLETE JustMess #-}

pattern PidMess :: Pid -> m -> HListPair '[] '[Pid, m]
pattern PidMess pid m = (HNil, HListMatch2 (Identity pid) (Identity m))
{-# COMPLETE PidMess #-}

pattern SidMess :: sid -> HListPair '[sid] '[]
pattern SidMess sid = (HCons (Identity sid) HNil, HNil)
{-# COMPLETE SidMess #-}

type SignatureScheme' = SignatureScheme String String String String

data UnexpectedSenderEx = UnexpectedSenderEx

signatureIF :: SingleSidIdeal SignSid
                              (HListPort SignatureScheme' Started)
                              (HListPort SignReq SignResp)
                              '[]
signatureIF (SidMess (SignSid {signSidSigner} )) = M.do
    m <- tryRerun $ myRecvOne InList2
    (scheme, sk, pk) <- initHelper
    state <- xcatch (processReq scheme sk pk m Map.empty) $ oneExceptionH $ M.do
      send Here (PidMess "" ())
      xreturn Map.empty
    loopHelper scheme sk pk state

  where

    initHelper = M.do
      send InList1 $ JustMess Started
      tmp' <- tryRerun $ myRecvOne InList1
      let (JustMess scheme) = tmp'
      (sk, pk) <- xlift $ sigKey scheme
      xreturn (scheme, sk, pk)

    loopHelper scheme sk pk state = M.do
      state' <- tryRerun $ M.do
        m <- myRecvOne InList2
        processReq scheme sk pk m state
      loopHelper scheme sk pk state'

    processReq scheme sk pk (PidMess pid req) state = case req of
      KGen -> M.do
        send InList2 (PidMess pid $ RespKGen pk)
        xreturn state
      Sign m -> M.do
        sig <- xlift $ sigSign scheme sk m
        let resp = case (m, sig, pk) `Map.lookup` state == Just False
                        || pid /= signSidSigner
                   of
              True -> RespErr
              False -> RespSign sig
        send InList2 $ PidMess pid resp
        xreturn $ Map.insert (m, sig, pk) True state
      Ver pk' m sig -> M.do
        let resp = case (pk' == pk, (m, sig, pk') `Map.lookup` state) of
                (True, Just True) -> True
                (True, Nothing) -> False
                -- ^This condition needs to be modified if we include corruptions
                (_, Just b) -> b
                (_, Nothing) -> sigVer scheme pk' m sig
        send InList2 $ PidMess pid $ RespVer resp
        xreturn $ Map.insert (m, sig, pk') resp state

    myRecvOne :: PortInList x y ports
              -> AsyncExT '[UnexpectedSenderEx :@ NextSend] ports NextRecv NextSend y
    myRecvOne = recvOneEx Here UnexpectedSenderEx

    oneExceptionH :: AsyncT ports i j a
                 -> InList '[UnexpectedSenderEx :@ i] (e :@ b) -> e -> AsyncT ports b j a
    oneExceptionH f Here = \UnexpectedSenderEx -> f
    oneExceptionH _ (There contra) = case contra of {}

    tryRerun :: AsyncExT '[UnexpectedSenderEx :@ NextSend] (Concat2 '[] '[Pid] PingSendPort : ports) NextRecv i a
             -> AsyncT (Concat2 '[] '[Pid] PingSendPort : ports) NextRecv i a
    tryRerun f = (f `xcatch`) $ \case
      Here -> \UnexpectedSenderEx -> M.do
        send Here (PidMess "" ())
        tryRerun f
      There contra -> case contra of {}
