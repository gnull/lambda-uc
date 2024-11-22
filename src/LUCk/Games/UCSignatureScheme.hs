module LUCk.Games.UCSignatureScheme where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity

import LUCk.Types
import LUCk.Syntax

import LUCk.UC
import LUCk.UC.Core

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

signatureIF :: SingleSidIdeal SignSid
                              (HListPort (SignatureScheme String String String String) Started)
                              (HListPort (SignReq String String String) (SignResp String String String))
                              '[]
signatureIF (SidMess sid) = M.do
    recvAny >>=: \case
      SomeRxMess Here (PidMess _ contra) -> case contra of {}
      SomeRxMess (There Here) (PidMess pid _) -> M.do
        -- adversary has sent us a message before we asked, ignore
        send Here (PidMess pid ())
        signatureIF (SidMess sid)
      SomeRxMess (There2 Here) (PidMess pid req) -> case req of
        KGen -> M.do
          -- we got our first request, let's ask adversary for algorithms
          send (There Here) (PidMess pid Started)
          recvAny >>=: \case
            SomeRxMess Here (HNil, HListMatch2 _ contra) -> case runIdentity contra of {}
            SomeRxMess (There Here) (HNil, HListMatch2 _ (Identity scheme)) -> M.do
              (sk, pk) <- xlift $ sigKey scheme
              send (There2 Here) (PidMess pid $ RespKGen pk)
              helper scheme [] sk pk
            SomeRxMess (There2 _) _ -> M.do
              send Here (PidMess pid ())
              signatureIF (SidMess sid)
        _ -> M.do
          send Here (PidMess pid ())
          signatureIF (SidMess sid)
      SomeRxMess (There3 contra) _ -> case contra of {}
  where
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
            let resp = RespVer verd -- TODO: check more conditions here
            send (There2 Here) (PidMess pid resp)
            let trace' = case resp of
                  RespVer b -> (m, sig, pk, b) : trace
                  _ -> trace
            helper scheme trace' sk pk
        SomeRxMess (There3 contra) _ -> case contra of {}
