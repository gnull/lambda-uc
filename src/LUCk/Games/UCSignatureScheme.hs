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

signatureIF :: SingleSidIdeal SignSid
                              (HListPort (SignatureScheme String String String String) Started)
                              (HListPort (SignReq String String String) (SignResp String String String))
                              '[]
signatureIF (SidMess sid) = M.do
    (scheme, sk, pk) <- initHelper
    loopHelper scheme [] sk pk
  where
    initHelper = tryRerun $ M.do
      tmp <- myRecvOne (There2 Here)
      let (PidMess pid req) = tmp
      case req of
        KGen -> M.do
          send (There Here) (PidMess pid Started)
          tmp <- myRecvOne (There Here)
          let (PidMess _ scheme) = tmp
          (sk, pk) <- xlift $ sigKey scheme
          send (There2 Here) (PidMess pid $ RespKGen pk)
          xreturn (scheme, sk, pk)
        _ -> xthrow Here ()

    loopHelper scheme trace sk pk = M.do
      trace' <- tryRerun $ M.do
        tmp <- myRecvOne $ There2 Here
        let (PidMess pid req) = tmp
        case req of
          KGen -> xthrow Here ()
          Sign m -> M.do
            sig <- xlift $ sigSign scheme sk m
            let resp = if (m, sig, pk, False) `elem` trace then RespErr else RespSign sig
            send (There2 Here) (PidMess pid resp)
            xreturn ((m, sig, pk, True):trace)
          Ver pk' m sig -> M.do
            let verd = sigVer scheme pk m sig
            let resp = RespVer verd
            -- TODO: check more conditions here
            send (There2 Here) (PidMess pid resp)
            let trace' = case resp of
                  RespVer b -> (m, sig, pk, b) : trace
                  _ -> trace
            xreturn trace'
      loopHelper scheme trace sk pk

    myRecvOne :: PortInList x y ports
              -> AsyncExT '[() :@ NextSend] ports NextRecv NextSend y
    myRecvOne = recvOneEx Here ()

    tryRerun :: AsyncExT '[() :@ NextSend] (Concat2 '[] '[Pid] PingSendPort : ports) NextRecv NextRecv a
             -> AsyncT (Concat2 '[] '[Pid] PingSendPort : ports) NextRecv NextRecv a
    tryRerun f = (f `xcatch`) $ \case
      Here -> \() -> M.do
        send Here (PidMess "" ())
        tryRerun f
      There contra -> case contra of {}
