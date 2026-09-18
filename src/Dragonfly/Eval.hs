module Dragonfly.Eval
  ( Value (..), Neutral (..), Closure (..), Env, EvalError (..)
  , eval, apply, instantiateClosure, fresh, quote, normalize, convertible
  ) where

import Dragonfly.Syntax
import Numeric.Natural (Natural)

type Env = [Value]

data Value
  = VUniverse Natural
  | VPi String Value Closure
  | VLam String Closure
  | VNeutral Neutral

data Closure = Closure Env Term

-- Levels count from the outside, so extending a context preserves old levels.
data Neutral = NVar Natural | NApp Neutral Value

data EvalError
  = MissingVariable Natural
  | ApplyNonFunction
  | EscapingLevel Natural Natural
  deriving (Eq, Show)

fresh :: Natural -> Value
fresh = VNeutral . NVar

lookupEnv :: Natural -> Env -> Either EvalError Value
lookupEnv i [] = Left (MissingVariable i)
lookupEnv 0 (v : _) = Right v
lookupEnv i (_ : rest) = lookupEnv (i - 1) rest

eval :: Env -> Term -> Either EvalError Value
eval env term = case term of
  Var i -> lookupEnv i env
  Universe l -> Right (VUniverse l)
  Pi name a b -> VPi name <$> eval env a <*> pure (Closure env b)
  Lam name body -> Right (VLam name (Closure env body))
  App f a -> do
    vf <- eval env f
    va <- eval env a
    apply vf va
  Ann t _ -> eval env t

instantiateClosure :: Closure -> Value -> Either EvalError Value
instantiateClosure (Closure env body) arg = eval (arg : env) body

apply :: Value -> Value -> Either EvalError Value
apply (VLam _ closure) arg = instantiateClosure closure arg
apply (VNeutral n) arg = Right (VNeutral (NApp n arg))
apply _ _ = Left ApplyNonFunction

-- | Reify at the current context size. This produces beta-normal forms;
-- eta expansion is performed on demand by conversion below.
quote :: Natural -> Value -> Either EvalError Term
quote depth value = case value of
  VUniverse l -> Right (Universe l)
  VPi name a b -> do
    domain <- quote depth a
    body <- instantiateClosure b (fresh depth) >>= quote (depth + 1)
    Right (Pi name domain body)
  VLam name closure -> do
    body <- instantiateClosure closure (fresh depth) >>= quote (depth + 1)
    Right (Lam name body)
  VNeutral n -> quoteNeutral depth n

quoteNeutral :: Natural -> Neutral -> Either EvalError Term
quoteNeutral depth neutral = case neutral of
  NVar level
    | level < depth -> Right (Var (depth - level - 1))
    | otherwise -> Left (EscapingLevel level depth)
  NApp f a -> App <$> quoteNeutral depth f <*> quote depth a

-- | Low-level normalization assumes a well-typed term. Use normalizeClosed
-- from Check to check before evaluating arbitrary input.
normalize :: Env -> Natural -> Term -> Either EvalError Term
normalize env depth term = eval env term >>= quote depth

-- | Beta-eta conversion of well-typed values at a common type. Binder names
-- have no semantic significance. Fresh neutrals let us compare open bodies.
convertible :: Natural -> Value -> Value -> Either EvalError Bool
convertible depth left right = case (left, right) of
  (VUniverse l, VUniverse r) -> Right (l == r)
  (VPi _ a b, VPi _ a' b') -> do
    domains <- convertible depth a a'
    if not domains then Right False else do
      body <- instantiateClosure b (fresh depth)
      body' <- instantiateClosure b' (fresh depth)
      convertible (depth + 1) body body'
  (VLam _ _, VLam _ _) -> functions
  (VLam _ _, VNeutral _) -> functions
  (VNeutral _, VLam _ _) -> functions
  (VNeutral n, VNeutral n') -> neutrals n n'
  _ -> Right False
  where
    functions = do
      body <- apply left (fresh depth)
      body' <- apply right (fresh depth)
      convertible (depth + 1) body body'
    neutrals (NVar l) (NVar r) = Right (l == r)
    neutrals (NApp f a) (NApp g b) = do
      heads <- neutrals f g
      if heads then convertible depth a b else Right False
    neutrals _ _ = Right False
