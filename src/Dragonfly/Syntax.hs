module Dragonfly.Syntax
  ( Term (..), shift, substitute, instantiate ) where

import Numeric.Natural (Natural)

-- | Index 0 is the nearest enclosing binder. Names are printing hints only.
data Term
  = Var Natural
  | Universe Natural
  | Pi String Term Term
  | Lam String Term
  | App Term Term
  | Ann Term Term
  deriving (Eq, Show)

-- | Raise free indices at or above the cutoff by the given amount.
shift :: Natural -> Natural -> Term -> Term
shift amount = go
  where
    go cutoff term = case term of
      Var i -> Var (if i >= cutoff then i + amount else i)
      Universe l -> Universe l
      Pi name a b -> Pi name (go cutoff a) (go (cutoff + 1) b)
      Lam name body -> Lam name (go (cutoff + 1) body)
      App f a -> App (go cutoff f) (go cutoff a)
      Ann t a -> Ann (go cutoff t) (go cutoff a)

-- | Replace a variable and REMOVE its context entry. The replacement lives
-- in the context with that entry removed. Variables above it move down by one.
substitute :: Natural -> Term -> Term -> Term
substitute index replacement term = case term of
  Var i
    | i == index -> replacement
    | i > index -> Var (i - 1)
    | otherwise -> Var i
  Universe l -> Universe l
  Pi name a b -> Pi name (sub a) (under b)
  Lam name body -> Lam name (under body)
  App f a -> App (sub f) (sub a)
  Ann t a -> Ann (sub t) (sub a)
  where
    sub = substitute index replacement
    under = substitute (index + 1) (shift 1 0 replacement)

instantiate :: Term -> Term -> Term
instantiate = substitute 0
