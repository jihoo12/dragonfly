module Dragonfly.Pretty (prettyTerm, prettyError) where

import Dragonfly.Check (TypeError (..))
import Dragonfly.Syntax
import Numeric.Natural (Natural)

prettyTerm :: Term -> String
prettyTerm = go []
  where
    go names term = case term of
      Var i -> lookupName i names
      Universe l -> "Type " ++ show l
      Pi hint a b ->
        let name = freshName hint names
        in "(Pi (" ++ name ++ " : " ++ go names a ++ "). " ++ go (name : names) b ++ ")"
      Lam hint body ->
        let name = freshName hint names
        in "(\\" ++ name ++ ". " ++ go (name : names) body ++ ")"
      App f a -> "(" ++ go names f ++ " " ++ go names a ++ ")"
      Ann t a -> "(" ++ go names t ++ " : " ++ go names a ++ ")"

lookupName :: Natural -> [String] -> String
lookupName index = go index
  where
    go _ [] = "#" ++ show index
    go 0 (name : _) = name
    go i (_ : rest) = go (i - 1) rest

freshName :: String -> [String] -> String
freshName hint names = choose (if null hint then "x" else hint)
  where
    choose name | name `elem` names = choose (name ++ "'")
                | otherwise = name

prettyError :: TypeError -> String
prettyError err = case err of
  UnboundVariable i -> "Unbound variable #" ++ show i
  CannotInferLambda -> "Cannot infer a lambda's type; add a type annotation."
  ExpectedUniverse ty -> "Expected a type, but inferred " ++ prettyTerm ty
  ExpectedFunction ty -> "Expected a function type, but found " ++ prettyTerm ty
  TypeMismatch expected actual ->
    "Type mismatch: expected " ++ prettyTerm expected ++ ", inferred " ++ prettyTerm actual
  EvaluationError e -> "Evaluation error: " ++ show e
