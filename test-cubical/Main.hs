module Main (main) where

import Control.Monad (forM_, unless)
import Dragonfly.Cubical
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label ok = unless ok (putStrLn ("FAIL: " ++ label) >> exitFailure)

accept :: String -> Either TypeError a -> IO ()
accept label result = case result of
  Left err -> putStrLn ("FAIL: " ++ label ++ "\n" ++ show err) >> exitFailure
  Right _ -> pure ()

reject :: String -> Either TypeError a -> IO ()
reject label result = case result of
  Left _ -> pure ()
  Right _ -> putStrLn ("FAIL (accepted): " ++ label) >> exitFailure

computes :: String -> Ter -> Ter -> Ter -> IO ()
computes label t expected ty = case normalizesTo t expected ty of
  Left err -> putStrLn ("FAIL: " ++ label ++ "\n" ++ show err) >> exitFailure
  Right ok -> assert label ok

line :: Ter -> Ter
line = PLam (Name "constant")

main :: IO ()
main = do
  -- Primary target: checked equivalence + checked universe path + transport
  -- changing a closed value. No opaque univalence axiom can pass this test.
  accept "swap equivalence" (checkClosed swapEquivalence (equiv pairBool pairBool))
  accept "ua swap in Type 0" (checkClosed swapPath (path (U 0) pairBool pairBool))
  computes "ua transport computes swap" (transport swapPath (Pair false true)) (Pair true false) pairBool
  computes "swap other input" (transport swapPath (Pair true false)) (Pair false true) pairBool
  computes "transport twice" (transport swapPath (transport swapPath (Pair false true))) (Pair false true) pairBool
  computes "ua zero endpoint" (AppFormula swapPath (Dir Zero)) pairBool (U 0)
  computes "ua one endpoint" (AppFormula swapPath (Dir One)) pairBool (U 0)
  assert "swap does not compute identity" $
    normalizesTo (transport swapPath (Pair false true)) (Pair false true) pairBool == Right False
  forM_ [0,1,2,7] $ \l -> do
    accept ("generic ua at level " ++ show l) (checkClosed (ua l) (uaType l))
    accept "universe successor" (checkClosed (U l) (U (l+1)))
    reject "no Type l : Type l" (checkClosed (U l) (U l))
    reject "universes remain noncumulative" (checkClosed (U l) (U (l+2)))
  reject "ua cannot be lowered" (checkClosed (ua 1) (uaType 0))
  reject "mixed-level equivalence" (inferClosed (App (App (ua 0) bool) (U 0)))
  let idU = Ann (identityEquivalence (U 0)) (equiv (U 0) (U 0))
      uaU = App (App (App (ua 1) (U 0)) (U 0)) idU
  accept "ua on a universe" (checkClosed uaU (path (U 1) (U 0) (U 0)))
  case normalizeClosed (transport uaU bool) of
    Left err -> print err >> exitFailure
    Right result -> assert "universe-level transport normalizes" (not (null result))
  -- This computation exercises compUniv and the VCompU element rules.
  accept "transport a type via ua_1" (checkClosed (transport uaU bool) (U 0))
  accept "Pi maximum level" (checkClosed (Pi (Lam "A" (U 0) (U 2))) (U 3))
  reject "Pi does not lower levels" (checkClosed (Pi (Lam "A" (U 0) (U 2))) (U 2))
  reject "Sigma does not lower levels" (checkClosed (Sigma (Lam "A" (U 0) (U 2))) (U 2))

  let reflFalse = Ann (line false) (path bool false false)
      i = Name "i"
      j = Name "j"
      tyFalse = path bool false false
  computes "path beta" (AppFormula reflFalse (Dir One)) false bool
  reject "wrong endpoint" (checkClosed (line false) (path bool false true))
  reject "unbound dimension" (inferClosed (AppFormula reflFalse (Atom i)))
  reject "unbound term variable" (inferClosed (Var "missing"))
  computes "empty composition" (Comp (line bool) false (system [])) false bool
  let fillFalse = Fill (line bool) false (system [])
  accept "filling is a dependent path" (checkClosed fillFalse tyFalse)
  computes "fill start" (AppFormula fillFalse (Dir Zero)) false bool
  computes "fill end" (AppFormula fillFalse (Dir One)) false bool
  let dimShadow = PLam i (Ann (PLam i false) tyFalse)
  accept "dimension shadowing" (checkClosed dimShadow (path tyFalse reflFalse reflFalse))
  let eta = Lam "p" tyFalse (PLam i (AppFormula (Var "p") (Atom i)))
  accept "path eta" (checkClosed eta (Pi (Lam "p" tyFalse tyFalse)))

  let impossiblePath = path bool false true
      boolLike op = Lam "p" impossiblePath
        (PLam i (AppFormula (Var "p") (op (Atom i) (NegAtom i))))
      constantFunction endpoint = Lam "p" impossiblePath (line endpoint)
      loopType endpoint = Pi (Lam "p" impossiblePath (path bool endpoint endpoint))
  assert "actual cubical interval has no excluded middle" $
    normalizesTo (boolLike (:\/:)) (constantFunction true) (loopType true) == Right False
  assert "actual cubical interval has no Boolean contradiction law" $
    normalizesTo (boolLike (:/\:)) (constantFunction false) (loopType false) == Right False
  let compatibleTube = Comp (line bool) false (system [(faceOf i Zero,line false)])
  accept "face system" (checkClosed (PLam i compatibleTube) tyFalse)
  let wrongStart = Comp (line bool) false (system [(faceOf i Zero,line true)])
  reject "tube base mismatch" (checkClosed (PLam i wrongStart) tyFalse)
  let badOverlaps = Glue 0 pairBool (system
        [(faceOf i Zero, Pair pairBool swapEquivalence),
         (faceOf j Zero, Pair pairBool (identityEquivalence pairBool))])
      overlapResult = checkClosed (PLam i (PLam j badOverlaps))
        (path (path (U 0) pairBool pairBool) (line pairBool) (line pairBool))
  assert "reject genuinely incompatible valid equivalence sides" $
    overlapResult == Left (TypeError "Incompatible overlapping system sides")
  let absorbedConflict = Glue 0 pairBool (system
        [(mempty,Pair pairBool (identityEquivalence pairBool)),
         (faceOf i Zero,Pair pairBool swapEquivalence)])
  assert "absorption cannot hide an incompatible side" $
    checkClosed (PLam i absorbedConflict) (path (U 0) pairBool pairBool)
      == Left (TypeError "Incompatible overlapping system sides")
  let unboundFace = Comp (line bool) false (system [(faceOf i Zero,line false)])
  reject "unbound face" (inferClosed unboundFace)
  reject "Glue base cannot exceed its level" (inferClosed (Glue 0 (U 0) (system [])))
  let highSide = PLam i (Glue 0 bool (system [(faceOf i Zero,Pair (U 0) (identityEquivalence (U 0)))]))
  reject "Glue domain cannot exceed its level" (checkClosed highSide (path (U 0) bool bool))

  let emptyGlue = Glue 0 bool (system [])
      emptyElement = GlueElem emptyGlue false (system [])
  computes "unglue/glue beta" (UnGlueElem emptyElement emptyGlue) false bool
  let fullGlue = Glue 0 pairBool (system [(mempty,Pair pairBool swapEquivalence)])
      fullElement = GlueElem fullGlue (Pair true false) (system [(mempty,Pair false true)])
  computes "full face Glue type" fullGlue pairBool (U 0)
  computes "full face glue element" fullElement (Pair false true) pairBool
  computes "full face unglue computes equivalence" (UnGlueElem fullElement fullGlue) (Pair true false) pairBool
  reject "incoherent glue element" $
    inferClosed (GlueElem fullGlue (Pair false true) (system [(mempty,Pair false true)]))
  reject "missing glue side" $ inferClosed (GlueElem fullGlue (Pair true false) (system []))

  let universeComp = Comp (line (U 0)) bool (system [])
      compElement = GlueElem universeComp false (system [])
  accept "universe composition level" (checkClosed universeComp (U 0))
  reject "universe composition cannot lower levels" (checkClosed (Comp (line (U 1)) (U 0) (system [])) (U 0))
  accept "universe composition element" (checkClosed compElement universeComp)
  computes "universe composition unglue beta" (UnGlueElem compElement universeComp) false bool
  computes "composition in a composed universe type"
    (transport (line universeComp) compElement) compElement universeComp
  computes "total universe tube" (Comp (line (U 0)) bool (system [(mempty,line bool)])) bool (U 0)
  putStrLn "All computational-univalence, universe, path, system, composition, and Glue tests passed."
