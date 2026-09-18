module Main (main) where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM)
import Dragonfly.Cubical
import System.Exit (exitFailure)
import System.Timeout (timeout)

data Test = Test String (Either String ())

accept :: Show a => String -> Either TypeError a -> Test
accept label result = Test label $ case result of
  Left err -> Left (show err)
  Right x -> length (show x) `seq` Right ()

reject :: Show a => String -> Either TypeError a -> Test
reject label result = Test label $ case result of
  Left err -> length (show err) `seq` Right ()
  Right x -> Left ("Unexpectedly accepted: " ++ show x)

computes :: String -> Ter -> Ter -> Ter -> Test
computes label a b ty = Test label $ case normalizesTo a b ty of
  Left err -> Left (show err)
  Right True -> Right ()
  Right False -> Left "Not convertible"

line :: Ter -> Ter
line = PLam (Name "auditConstant")

auditTests :: [Test]
auditTests =
  [ accept "annotated unglue survives face substitution" (inferClosed annotatedUngluePath)
  , computes "annotated unglue endpoint computes"
      (App (AppFormula annotatedUngluePath (Dir Zero)) false) false bool
  , accept "universe unglue survives face substitution" (inferClosed universeUngluePath)
  , computes "universe unglue endpoint computes"
      (App (AppFormula universeUngluePath (Dir Zero)) false) false bool
  , Test "path helper avoids names hidden in element annotations" $
      case path hiddenAnnotation bool bool of
        PathP (PLam (Name binder) _) _ _
          | binder /= "$constant" -> Right ()
        _ -> Left "Captured a dimension occurring in a GlueElem annotation"
  ] ++ universeTests ++ boundaryTests ++ nestedTests ++ computationTests ++ totalityTests
  where
    i = Name "i"
    g = Glue 0 bool (system [(faceOf i Zero,Pair bool (identityEquivalence bool))])
    emptyG = Glue 0 bool (system [])
    fn = Lam "x" g (UnGlueElem (Var "x") (Ann g (U 0)))
    fty = Pi (Lam "x" g bool)
    annotatedUngluePath = Ann (PLam i (Ann fn fty)) (PathP (PLam i fty)
      (Lam "x" bool (Var "x"))
      (Lam "x" emptyG (UnGlueElem (Var "x") emptyG)))
    uc = Comp (line (U 0)) bool (system [(faceOf i Zero,line bool)])
    emptyUC = Comp (line (U 0)) bool (system [])
    ufn = Lam "x" uc (UnGlueElem (Var "x") uc)
    ufty = Pi (Lam "x" uc bool)
    universeUngluePath = Ann (PLam i (Ann ufn ufty)) (PathP (PLam i ufty)
      (Lam "x" bool (transport (line bool) (Var "x")))
      (Lam "x" emptyUC (UnGlueElem (Var "x") emptyUC)))
    hiddenAnnotation = GlueElem (Glue 0 (AppFormula (Var "p") (Atom (Name "$constant"))) (system [])) (Var "x") (system [])

-- Cross every known formation level with proposed lower, equal, and higher
-- levels. No implicit cumulativity or resizing is allowed.
universeTests :: [Test]
universeTests = concat
  [ [ (if actual == proposed then accept else reject)
        (label ++ " formed at " ++ show actual ++ ", checked at " ++ show proposed)
        (checkClosed term (U proposed))
      | proposed <- [0..5] ]
  | l <- [0..3]
  , let a = if l == 0 then bool else U (l-1)
        g = Glue l a (system [])
        c = Comp (line (U l)) a (system [])
  , (label,term,actual) <-
      [ ("base",a,l)
      , ("Pi",Pi (Lam "x" a a),l)
      , ("Sigma",Sigma (Lam "x" a a),l)
      , ("Path in universe",path (U l) a a,l+1)
      , ("Glue",g,l)
      , ("universe comp",c,l)
      , ("nested Glue",Glue l g (system []),l)
      , ("nested comp",Comp (line (U l)) c (system []),l)
      , ("Glue of comp",Glue l c (system []),l)
      , ("comp of Glue",Comp (line (U l)) g (system []),l)
      , ("Equiv",equiv a a,l)
      , ("ua type",uaType l,l+1)
      ] ]

boundaryTests :: [Test]
boundaryTests =
  [ reject "universe hidden behind annotation" (checkClosed (Ann (U 0) (U 1)) (U 0))
  , reject "universe hidden behind beta" (checkClosed
      (App (Ann (Lam "x" (U 1) (Var "x")) (Pi (Lam "x" (U 1) (U 1)))) (U 0)) (U 0))
  , reject "wrong PathP family universe" (checkClosed (path (U 1) (U 0) (U 0)) (U 1))
  , reject "mixed endpoints in universe" (inferClosed (path (U 0) bool (U 0)))
  , reject "composition start in wrong universe" (inferClosed (Comp (line (U 0)) (U 0) (system [])))
  , reject "filling start in wrong universe" (inferClosed (Fill (line (U 0)) (U 0) (system [])))
  , reject "full face does not excuse wrong composition start" (inferClosed
      (Comp (line (U 0)) (U 0) (system [(mempty,line bool)])))
  , reject "full tube cannot resize result" (inferClosed
      (Comp (line (U 0)) bool (system [(mempty,line (U 0))])))
  , reject "Glue partial type from higher universe" (inferClosed
      (Glue 0 bool (system [(mempty,Pair (U 0) (identityEquivalence (U 0)))])))
  , reject "Glue partial type from lower universe" (inferClosed
      (Glue 1 (U 0) (system [(mempty,Pair bool (identityEquivalence bool))])))
  , reject "full Glue cannot conceal invalid base level" (inferClosed
      (Glue 0 (U 0) (system [(mempty,Pair bool (identityEquivalence bool))])))
  , reject "purported mixed-level equivalence witness" (checkClosed
      (identityEquivalence bool) (equiv bool (U 0)))
  , accept "heterogeneous Equiv type forms only at maximum level" (checkClosed (equiv bool (U 0)) (U 1))
  , reject "heterogeneous Equiv type does not resize" (checkClosed (equiv bool (U 0)) (U 0))
  , reject "missing equivalence proof" (inferClosed (Glue 0 bool (system [(mempty,Pair bool false)])))
  , reject "forged equivalence fiber contraction" (checkClosed
      (Pair (Lam "x" bool (Var "x")) (Lam "y" bool false)) (equiv bool bool))
  , reject "opaque ua name" (inferClosed (Ann (Var "ua") (uaType 0)))
  , reject "unknown term in absorbed system side" (checkClosed
      (PLam i (Glue 0 bool (system [(mempty,Pair bool (identityEquivalence bool)),(faceOf i Zero,Var "missing")])))
      (path (U 0) bool bool))
  , reject "unknown dimension in absorbed side" (inferClosed
      (Glue 0 bool (system [(mempty,Pair bool (identityEquivalence bool)),(faceOf i Zero,Pair bool (identityEquivalence bool))])))
  , reject "family dimension escapes into tube shape" (inferClosed
      (Comp (PLam i bool) false (system [(faceOf i Zero,line false)])))
  , reject "family dimension escapes into endpoint" (inferClosed
      (PathP (PLam i bool) (AppFormula refl (Atom i)) false))
  , reject "tube dimension escapes into composition result" (inferClosed
      (Ann (AppFormula (Fill (line bool) false (system [])) (Atom i)) bool))
  , reject "wrong fill target endpoint" (checkClosed (Fill (line bool) false (system [])) (path bool false true))
  , reject "wrong path element type" (checkClosed (line (U 0)) (path bool false false))
  , reject "wrong unglue element type" (inferClosed (UnGlueElem true emptyG))
  , reject "unglue non-Glue annotation" (inferClosed (UnGlueElem false bool))
  , reject "extra glue element face" (inferClosed (GlueElem emptyG false (system [(mempty,false)])))
  , reject "dynamic unglue presentation is rejected, not evaluated unsafely" (inferClosed
      (Ann (Lam "x" emptyG (UnGlueElem (Var "x") aliasG)) (Pi (Lam "x" emptyG bool))))
  , computes "annotated full Glue retains forward map"
      (UnGlueElem (Pair false true) (Ann fullSwap (U 0))) (Pair true false) pairBool
  , computes "annotated full Glue introduction computes"
      (GlueElem (Ann fullSwap (U 0)) (Pair true false) (system [(mempty,Pair false true)])) (Pair false true) pairBool
  , computes "full universe presentation introduction computes"
      (GlueElem fullUC false (system [(mempty,false)])) false bool
  , reject "non-uniform composition cannot masquerade as universe Glue"
      (checkClosed nonUniformElimination nonUniformType)
  ] ++
  [ accept ("dimension shadowing with source name " ++ show name) (checkClosed
      (Lam "p" edge (PLam (Name name) (PLam (Name name) (AppFormula (Var "p") (Atom (Name name))))))
      (Pi (Lam "p" edge (path edge (Var "p") (Var "p")))))
  | name <- ["i", "!0", "!not-a-number", "$constant", ""] ] ++
  [ reject ("term shadow cannot change level " ++ name) (checkClosed
      (Lam name (U 0) (Lam name (U 1) (Var name)))
      (Pi (Lam "A" (U 0) (Pi (Lam "B" (U 1) (U 0))))))
  | name <- ["A", "$base", "$T", "X"] ]
  where
    i = Name "i"
    edge = path bool false true
    refl = Ann (line false) (path bool false false)
    emptyG = Glue 0 bool (system [])
    aliasG = App (Ann (Lam "A" (U 0) (Var "A")) (Pi (Lam "A" (U 0) (U 0)))) emptyG
    fullSwap = Glue 0 pairBool (system [(mempty,Pair pairBool swapEquivalence)])
    fullUC = Comp (line (U 0)) bool (system [(mempty,line bool)])
    startType = Pi (Lam "b" bool (U 0))
    familyType = path (U 1) startType (U 0)
    target = Comp (Var "p") (Ann (Lam "b" bool bool) startType) (system [])
    nonUniformElimination = Lam "p" familyType (Lam "x" target (UnGlueElem (Var "x") target))
    nonUniformType = Pi (Lam "p" familyType (Pi (Lam "x" target startType)))

nestedTests :: [Test]
nestedTests =
  [ computes "nested Glue computation" (UnGlueElem (UnGlueElem xgg gg) g) false bool
  , computes "nested universe composition computation" (UnGlueElem (UnGlueElem xcc cc) c) false bool
  , computes "Glue over universe composition" (UnGlueElem (UnGlueElem xgc gc) c) false bool
  , computes "universe composition over Glue" (UnGlueElem (UnGlueElem xcg cg) g) false bool
  , computes "composition in nested Glue" (transport (line gg) xgg) xgg gg
  , computes "composition in nested universe composition" (transport (line cc) xcc) xcc cc
  , computes "filling nested Glue starts correctly" (AppFormula (Fill (line gg) xgg (system [])) (Dir Zero)) xgg gg
  , computes "filling nested universe composition ends correctly" (AppFormula (Fill (line cc) xcc (system [])) (Dir One)) xcc cc
  , reject "nested Glue element cannot skip inner introduction" (inferClosed (GlueElem gg false (system [])))
  , reject "nested comp element cannot skip inner introduction" (inferClosed (GlueElem cc false (system [])))
  , reject "nested Glue cannot hide a universe mismatch" (checkClosed (Glue 1 (U 0) (system [])) (U 0))
  , reject "nested composition cannot hide a universe mismatch" (checkClosed
      (Comp (line (U 1)) (Glue 1 (U 0) (system [])) (system [])) (U 0))
  , computes "unglue neutral path retains its result type"
      (App (Ann neutralPathElimination neutralPathType) (GlueElem gp refl (system []))) false bool
  ]
  where
    g = Glue 0 bool (system [])
    c = Comp (line (U 0)) bool (system [])
    xg = GlueElem g false (system [])
    xc = GlueElem c false (system [])
    gg = Glue 0 g (system [])
    cc = Comp (line (U 0)) c (system [])
    gc = Glue 0 c (system [])
    cg = Comp (line (U 0)) g (system [])
    xgg = GlueElem gg xg (system [])
    xcc = GlueElem cc xc (system [])
    xgc = GlueElem gc xc (system [])
    xcg = GlueElem cg xg (system [])
    p = path bool false false
    refl = Ann (line false) p
    gp = Glue 0 p (system [])
    neutralPathElimination = Lam "p" gp (AppFormula (UnGlueElem (Var "p") gp) (Dir Zero))
    neutralPathType = Pi (Lam "p" gp bool)

computationTests :: [Test]
computationTests =
  [ accept "independent associativity equivalence" (checkClosed associativity (equiv a b))
  , accept "independent ua with distinct endpoint types" (checkClosed universePath (path (U 0) a b))
  , computes "independent ua source endpoint" (AppFormula universePath (Dir Zero)) a (U 0)
  , computes "independent ua target endpoint" (AppFormula universePath (Dir One)) b (U 0)
  , Test "endpoint types are not definitionally equal" $ case normalizesTo a b (U 0) of
      Right False -> Right ()
      result -> Left (show result)
  , computes "full tube controls the composition result"
      (Lam "p" edge (Comp (line bool) false (system [(mempty,Var "p")])))
      (Lam "p" edge true) (Pi (Lam "p" edge bool))
  , computes "fill agrees with a total tube"
      (Lam "p" edge (Fill (line bool) false (system [(mempty,Var "p")])))
      (Lam "p" edge (Var "p")) (Pi (Lam "p" edge edge))
  , computes "Pi composition applied to closed argument"
      (App (Comp (line boolFunction) ident (system [])) false) false bool
  , computes "Path composition uses endpoint faces"
      (Lam "p" edge (Comp (line edge) (Var "p") (system [])))
      (Lam "p" edge (PLam i (Comp (line bool) (AppFormula (Var "p") (Atom i))
        (system [(faceOf i Zero,line false),(faceOf i One,line true)]))))
      (Pi (Lam "p" edge edge))
  ] ++
  [ computes ("independent ua associativity input " ++ show index)
      (transport universePath (Pair x (Pair y z))) (Pair (Pair x y) z) b
  | (index,(x,y,z)) <- zip [0 :: Int ..] [(x,y,z) | x <- bits,y <- bits,z <- bits] ]
  where
    bits = [false,true]
    a = Sigma (Lam "x" bool pairBool)
    b = Sigma (Lam "xy" pairBool bool)
    f = Ann (Lam "s" a (Pair (Pair (Fst (Var "s")) (Fst (Snd (Var "s")))) (Snd (Snd (Var "s")))))
          (Pi (Lam "s" a b))
    g = Ann (Lam "s" b (Pair (Fst (Fst (Var "s"))) (Pair (Snd (Fst (Var "s"))) (Snd (Var "s")))))
          (Pi (Lam "s" b a))
    fib = Sigma (Lam "x" a (path b (Var "y") (App f (Var "x"))))
    i = Name "assocI"
    j = Name "assocJ"
    q = Snd (Var "z")
    contraction = PLam i (Pair (App g (AppFormula q (Atom i)))
      (PLam j (AppFormula q (Atom i :/\: Atom j))))
    associativity = Ann (Pair f (Lam "y" b
      (Pair (Pair (App g (Var "y")) (line (Var "y"))) (Lam "z" fib contraction)))) (equiv a b)
    universePath = Ann (PLam i (Glue 0 b (system
      [(faceOf i Zero,Pair a associativity),(faceOf i One,Pair b (identityEquivalence b))])))
      (path (U 0) a b)
    edge = path bool false true
    boolFunction = Pi (Lam "x" bool bool)
    ident = Ann (Lam "x" bool (Var "x")) boolFunction

-- These are bounded crash/totality probes, not a typing oracle. Fully force
-- both successful normal forms and errors so lazy exceptions cannot hide.
totalityTests :: [Test]
totalityTests =
  [ Test ("bounded public-AST totality " ++ show index) $ case normalizeClosed term of
      Left err -> length (show err) `seq` Right ()
      Right result -> length result `seq` Right ()
  | (index,term) <- zip [0 :: Int ..] corpus ]
  where
    g = Glue 0 bool (system [])
    c = Comp (line (U 0)) bool (system [])
    atoms = [U 0,U 1,bool,false,true,Var "unknown",g,c,GlueElem g false (system []),
             Ann (line false) (path bool false false)]
    corpus = [constructor left right | left <- atoms,right <- atoms,constructor <-
      [Ann,App,\ty x -> GlueElem ty x (system []),UnGlueElem,
       \ty x -> Comp (line ty) x (system []),\ty x -> Fill (line ty) x (system []),
       \ty x -> PathP (line ty) x x,\ty x -> Glue 0 ty (system [(mempty,Pair ty x)])]]
      ++ [constructor x | x <- atoms,constructor <- [Fst,Snd,\t -> Glue 0 t (system [])]]

main :: IO ()
main = do
  passed <- forM auditTests $ \(Test label result) -> do
    outcome <- timeout 10000000 $ try $ evaluate (length (show result) `seq` result)
    case outcome :: Maybe (Either SomeException (Either String ())) of
      Just (Right (Right ())) -> pure True
      Just (Right (Left err)) -> putStrLn ("FAIL: " ++ label ++ "\n" ++ err) >> pure False
      Just (Left err) -> putStrLn ("EXCEPTION: " ++ label ++ "\n" ++ show err) >> pure False
      Nothing -> putStrLn ("TIMEOUT: " ++ label) >> pure False
  let successes = length (filter id passed)
  putStrLn (show successes ++ "/" ++ show (length passed) ++ " audit checks passed.")
  if and passed then pure () else exitFailure
