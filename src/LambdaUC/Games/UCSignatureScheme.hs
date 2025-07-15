module LambdaUC.Games.UCSignatureScheme where

import qualified Control.XMonad.Do as M
import Control.XMonad

import Data.Functor.Identity
import Data.List (find)

import LambdaUC.Types
import LambdaUC.Syntax
import LambdaUC.Syntax.Async.Eval

import LambdaUC.UC
import LambdaUC.UC.Core
import LambdaUC.UC.Flatten
import LambdaUC.UC.Shell

import Data.Type.Equality

import LambdaUC.Games.SignatureScheme (SpSignatureScheme, SignatureScheme(..))

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
signatureIF = SingleSidIdeal' $ \(Sid (SignSid {signSidSigner} )) -> M.do
    m <- tryRerun $ recvOne' InList2
    (scheme, sk, pk) <- initHelper
    state <- xcatchOne (processReq signSidSigner scheme sk pk m Map.empty) $ M.do
      send pingAddr $ PidMess "" ()
      xreturn Map.empty
    loopHelper signSidSigner scheme sk pk state

  where

    pingAddr = InList0
    advAddr = InList1
    callerAddr = InList2

    initHelper = M.do
      send advAddr $ Started
      scheme <- tryRerun $ recvOne' advAddr
      (sk, pk) <- xlift $ sigKey scheme
      xreturn (scheme, sk, pk)

    loopHelper signSidSigner scheme sk pk state = M.do
      state' <- tryRerun $ M.do
        m <- recvOne' InList2
        processReq signSidSigner scheme sk pk m state
      loopHelper signSidSigner scheme sk pk state'

    processReq signSidSigner scheme sk pk (PidMess pid req) state = case req of
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

    recvOne' :: PortInList x y ports
              -> AsyncExT '[UnexpectedSenderEx :@ NextSend] ports NextRecv NextSend y
    recvOne' = recvOneEx Here UnexpectedSenderEx

    xcatchOne :: AsyncExT '[e' :@ i] ports bef aft a
              -> AsyncT ports i aft a
              -> AsyncT ports bef aft a
    xcatchOne f h = xcatch f $ \case
        Here -> const h
        There contra -> case contra of {}

    tryRerun :: AsyncExT '[UnexpectedSenderEx :@ NextSend]
                         (PidMess () :> PidMess Void : ports)
                         NextRecv i a
             -> AsyncT (PidMess () :> PidMess Void : ports)
                       NextRecv i a
    tryRerun f = xcatchOne f $ M.do
      send pingAddr $ PidMess "" ()
      tryRerun f

newtype SignProtoState = SignProtoState Sk

isSigner :: SidPid SignSid -> Bool
isSigner (SidPid sid pid) = signSidSigner sid == pid

matchUp :: SomeRxMess '[() :> Void, SignResp :> SignReq]
        -> SignReq
matchUp = \case
  SomeRxMess Here contra -> case contra of {}
  SomeRxMess (There Here) m -> m
  SomeRxMess (There2 contra) _ -> case contra of {}

signatureProto :: SignatureScheme'
               -> SingleSidReal' SignSid
                                (HListPort (ActiveCorrReq (Maybe SignProtoState) (HListPort SignReq SignResp) '[]) ActiveCorrResp)
                                (HListPort SignReq SignResp)
                                '[]
signatureProto sch = activeCorruption Nothing $ ActiveCorrWithErasures $ \sidpid st m ->
    case (matchUp m, st) of
      (KGen, Nothing) -> do
        if isSigner sidpid then do
          (sk, pk) <- sigKey sch
          return (Just $ SignProtoState sk, SomeTxMess upAddr $ RespKGen pk)
        else do
          return (st, SomeTxMess pingAddr ())
      (KGen, Just (SignProtoState pk)) -> do
        if isSigner sidpid then do
          return (st, SomeTxMess upAddr $ RespKGen pk)
        else do
          return (st, SomeTxMess pingAddr ())
      (Sign mess, Just (SignProtoState sk)) -> do
        if isSigner sidpid then do
          s <- sigSign sch sk mess
          return (st, SomeTxMess upAddr $ RespSign s)
        else do
          return (st, SomeTxMess pingAddr ())
      (Ver pk mess sign, _) -> do
        let resp = sigVer sch pk mess sign
        return (st, SomeTxMess upAddr $ RespVer resp)
      _ -> return (st, SomeTxMess pingAddr ())
  where
    pingAddr = InList0
    upAddr = InList1
