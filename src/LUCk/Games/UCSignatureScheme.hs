module LUCk.Games.UCSignatureScheme where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity

import LUCk.Types
import LUCk.Syntax

import LUCk.UC
import LUCk.UC.Core

import Data.Type.Equality

import LUCk.Games.SignatureScheme (SpSignatureScheme, SignatureScheme(..))

import qualified Data.Map as Map

data SignReq pk mess sig
  = KGen
  | Sign mess
  | Ver pk mess sig

data SignResp pk mess sig
  = RespKGen pk
  | RespSign sig
  | RespVer Bool
  | RespErr

data Started = Started

data SignSid = SignSid
  { signSidSigner :: Pid
  , signSid' :: String
  }

pattern PidMess :: Pid -> m -> HListPair '[] '[Pid, m]
pattern PidMess pid m = (HNil, HListMatch2 (Identity pid) (Identity m))
{-# COMPLETE PidMess #-}

pattern SidMess :: sid -> HListPair '[sid] '[]
pattern SidMess sid = (HCons (Identity sid) HNil, HNil)
{-# COMPLETE SidMess #-}

recv :: PortInList x y ports
     -> (forall i. AsyncT ports NextSend i Void)
     -> AsyncT ports NextRecv NextSend y
recv i h = recvAny >>=: \case
  SomeRxMess j m -> case testEquality i j of
    Just Refl -> xreturn m
    Nothing -> h >>=: (\contra -> case contra of {})

signatureIF :: SingleSidIdeal SignSid
                              (HListPort (SignatureScheme String String String String) Started)
                              (HListPort (SignReq String String String) (SignResp String String String))
                              '[]
signatureIF (SidMess sid) = M.do
    (scheme, sk, pk) <- init
    helper scheme [] sk pk
  where
    init = M.do
      let handle = M.do
            send Here (PidMess "" ())
            init
          myRecv i = recv i $ undefined
      tmp <- myRecv (There2 Here)
      let (PidMess pid req) = tmp
      case req of
        KGen -> M.do
          send (There Here) (PidMess pid Started)
          tmp <- myRecv (There Here)
          let (PidMess _ scheme) = tmp
          (sk, pk) <- xlift $ sigKey scheme
          send (There2 Here) (PidMess pid $ RespKGen pk)
          xreturn (scheme, sk, pk)
        _ -> handle

    helper :: SignatureScheme String String String String
           -> [(String, String, String, Bool)]
           -> String
           -> String
           -> AsyncT
                (MapConcat2 '[] '[Pid]
                 [ HListPort () Void
                 , HListPort Started (SignatureScheme String String String String)
                 , HListPort (SignResp String String String) (SignReq String String String)
                 ]
                )
                NextRecv
                NextRecv
                Void
    helper scheme trace sk pk = M.do
      recvAny >>=: \case
        SomeRxMess Here (PidMess _ contra) -> case contra of {}
        SomeRxMess (There Here) (PidMess pid _) -> M.do
          send Here (PidMess pid ())
          helper scheme trace sk pk
        SomeRxMess (There2 Here) (PidMess pid req) -> case req of
          KGen -> M.do
            send Here (PidMess pid ())
            helper scheme trace sk pk
          Sign m -> M.do
            sig <- xlift $ sigSign scheme sk m
            let resp = if (m, sig, pk, False) `elem` trace then RespErr else RespSign sig
            send (There2 Here) (PidMess pid resp)
            helper scheme ((m, sig, pk, True):trace) sk pk
          Ver pk' m sig -> M.do
            let verd = sigVer scheme pk m sig
            let resp = RespVer verd
            -- TODO: check more conditions here
            send (There2 Here) (PidMess pid resp)
            let trace' = case resp of
                  RespVer b -> (m, sig, pk, b) : trace
                  _ -> trace
            helper scheme trace' sk pk
        SomeRxMess (There3 contra) _ -> case contra of {}
