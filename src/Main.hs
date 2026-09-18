module Main (main) where

import qualified Dragonfly.Cubical as Cubical
import Dragonfly.Check
import Dragonfly.Examples
import Dragonfly.Pretty
import Dragonfly.Syntax
import System.Exit (exitFailure)

main :: IO ()
main = do
  putStrLn "Computational univalence: transport along the pair-swap equivalence"
  case Cubical.normalizeClosed (Cubical.transport Cubical.swapPath (Cubical.Pair Cubical.false Cubical.true)) of
    Left err -> print err >> exitFailure
    Right result -> putStrLn ("  (false, true) -> " ++ result)
  mapM_ showExample examples
  putStrLn "Rejected example: Type 0 : Type 0"
  case inferClosed (Ann (Universe 0) (Universe 0)) of
    Left err -> putStrLn ("  " ++ prettyError err)
    Right _ -> putStrLn "Unexpectedly accepted invalid universe annotation." >> exitFailure
  where
    showExample (label, term) = do
      putStrLn label
      case normalizeClosed term of
        Left err -> putStrLn (prettyError err) >> exitFailure
        Right (ty, normal) -> do
          putStrLn ("  type:   " ++ prettyTerm ty)
          putStrLn ("  normal: " ++ prettyTerm normal)
