module Main (main) where

import Control.Monad (unless)
import Dragonfly.Syntax
import Dragonfly.Eval
import Dragonfly.Check
import Dragonfly.Examples
import Dragonfly.Pretty
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label ok = unless ok $ putStrLn ("FAIL: " ++ label) >> exitFailure

main :: IO ()
main = do
  assert "shift respects binders" $
    shift 2 0 (Lam "x" (App (Var 0) (Var 1)))
      == Lam "x" (App (Var 0) (Var 3))
  assert "substitution avoids capture" $
    instantiate (Var 0) (Lam "y" (Var 1)) == Lam "y" (Var 1)
  assert "substitution removes context entry" $
    instantiate (Universe 0) (App (Var 0) (Var 1))
      == App (Universe 0) (Var 0)
  assert "nested substitution" $
    instantiate (Var 0) (Lam "y" (Lam "z" (App (Var 2) (Var 0))))
      == Lam "y" (Lam "z" (App (Var 2) (Var 0)))
  assert "Pi domain is outside its binder" $
    instantiate (Universe 0) (Pi "x" (Var 0) (Var 1))
      == Pi "x" (Universe 0) (Universe 0)
  assert "beta reduction" $
    normalize [] 0 (App (Lam "x" (Var 0)) (Universe 0)) == Right (Universe 0)
  assert "normalize under a binder" $
    normalize [] 0 (Lam "x" (App (Lam "y" (Var 0)) (Var 0)))
      == Right (Lam "x" (Var 0))
  assert "closure captures outer environment" $
    normalize [] 0 (App (Lam "x" (Lam "y" (Var 1))) (Universe 0))
      == Right (Lam "y" (Universe 0))
  assert "function eta" $
    (do expanded <- eval [fresh 0] (Lam "x" (App (Var 1) (Var 0)))
        convertible 1 (fresh 0) expanded) == Right True
  assert "alpha equality" $
    (do a <- eval [] (Lam "x" (Var 0))
        b <- eval [] (Lam "y" (Var 0))
        convertible 0 a b) == Right True
  assert "distinct neutral variables" $
    convertible 2 (fresh 0) (fresh 1) == Right False
  assert "universe successor" $ inferClosed (Universe 0) == Right (Universe 1)
  assert "Pi universe maximum" $
    inferClosed (Pi "A" (Universe 0) (Universe 2)) == Right (Universe 3)
  assert "identity checks" $ checkClosed (Lam "A" (Lam "x" (Var 0))) (identityType 0) == Right ()
  assert "identity infers" $ inferClosed (identity 0) == Right (identityType 0)
  assert "dependent application substitutes argument" $
    inferClosed (App (identity 1) (Universe 0)) == Right (Pi "x" (Universe 0) (Universe 0))
  assert "identity application normalizes" $
    normalizeClosed (App (App (identity 2) (Universe 1)) (Universe 0))
      == Right (Universe 1, Universe 0)
  assert "all examples check" $ all (either (const False) (const True) . normalizeClosed . snd) examples
  assert "reject Type : Type" $
    inferClosed (Ann (Universe 0) (Universe 0)) == Left (TypeMismatch (Universe 0) (Universe 1))
  assert "universes are noncumulative" $
    checkClosed (Universe 0) (Universe 2) == Left (TypeMismatch (Universe 2) (Universe 1))
  assert "unbound variable" $ inferClosed (Var 3) == Left (UnboundVariable 3)
  assert "cannot infer bare lambda" $ inferClosed (Lam "x" (Var 0)) == Left CannotInferLambda
  assert "nonfunction application" $
    inferClosed (App (Universe 0) (Universe 0)) == Left (ExpectedFunction (Universe 1))
  assert "incorrect argument universe" $
    inferClosed (App (identity 0) (Universe 0)) == Left (TypeMismatch (Universe 0) (Universe 1))
  assert "lambda needs Pi" $
    checkClosed (Lam "x" (Var 0)) (Universe 0) == Left (ExpectedFunction (Universe 0))
  assert "annotation must be a type" $
    inferClosed (Ann (Universe 0) (identity 0)) == Left (ExpectedUniverse (identityType 0))
  assert "reject malformed Pi codomain" $
    inferClosed (Pi "A" (Universe 0) (identity 0)) == Left (ExpectedUniverse (identityType 0))
  assert "pretty printing avoids shadowing" $
    prettyTerm (Lam "x" (Lam "x" (Var 1))) == "(\\x. (\\x'. x))"
  -- P f and P (\x. f x) must convert inside a dependent result type.
  let etaType = Pi "A" (Universe 0)
        (Pi "f" (Pi "x" (Var 0) (Var 1))
          (Pi "P" (Pi "g" (Pi "x" (Var 1) (Var 2)) (Universe 0))
            (Pi "y" (App (Var 0) (Var 1))
              (App (Var 1) (Lam "x" (App (Var 3) (Var 0)))))))
      etaTerm = Lam "A" (Lam "f" (Lam "P" (Lam "y" (Var 0))))
  assert "eta conversion inside dependent types" $ checkClosed etaTerm etaType == Right ()
  assert "different functions are not convertible" $
    (do a <- eval [] (Lam "x" (Lam "y" (Var 0)))
        b <- eval [] (Lam "x" (Lam "y" (Var 1)))
        convertible 0 a b) == Right False
  assert "evaluation errors are structured" $
    normalize [] 0 (App (Universe 0) (Universe 0)) == Left ApplyNonFunction
  assert "reification rejects escaping levels" $
    quote 0 (fresh 0) == Left (EscapingLevel 0 0)
  putStrLn "All kernel tests passed."
