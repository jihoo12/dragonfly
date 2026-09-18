module Dragonfly.Check
  ( TypeError (..), inferClosed, checkClosed, normalizeClosed ) where

import Dragonfly.Eval
import Dragonfly.Syntax
import Numeric.Natural (Natural)

data TypeError
  = UnboundVariable Natural
  | CannotInferLambda
  | ExpectedUniverse Term
  | ExpectedFunction Term
  | TypeMismatch { expectedType :: Term, actualType :: Term }
  | EvaluationError EvalError
  deriving (Eq, Show)

-- Types are values in the current semantic environment, not syntax needing
-- shifting every time the context is extended.
data Context = Context { size :: Natural, environment :: Env, types :: [Value] }

empty :: Context
empty = Context 0 [] []

extend :: Context -> Value -> Context
extend ctx ty = Context (size ctx + 1) (fresh (size ctx) : environment ctx) (ty : types ctx)

liftEval :: Either EvalError a -> Either TypeError a
liftEval = either (Left . EvaluationError) Right

evaluate :: Context -> Term -> Either TypeError Value
evaluate ctx = liftEval . eval (environment ctx)

reify :: Context -> Value -> Either TypeError Term
reify ctx = liftEval . quote (size ctx)

lookupType :: Natural -> [Value] -> Either TypeError Value
lookupType index = go index
  where
    go _ [] = Left (UnboundVariable index)
    go 0 (ty : _) = Right ty
    go i (_ : rest) = go (i - 1) rest

infer :: Context -> Term -> Either TypeError Value
infer ctx term = case term of
  Var i -> lookupType i (types ctx)
  Universe l -> Right (VUniverse (l + 1))
  Pi _ a b -> do
    l <- inferUniverse ctx a
    domain <- evaluate ctx a
    r <- inferUniverse (extend ctx domain) b
    Right (VUniverse (max l r))
  Lam _ _ -> Left CannotInferLambda
  App f a -> do
    functionType <- infer ctx f
    case functionType of
      VPi _ domain codomain -> do
        check ctx a domain
        arg <- evaluate ctx a
        liftEval (instantiateClosure codomain arg)
      other -> reify ctx other >>= Left . ExpectedFunction
  Ann t a -> do
    _ <- inferUniverse ctx a
    ty <- evaluate ctx a
    check ctx t ty
    Right ty

inferUniverse :: Context -> Term -> Either TypeError Natural
inferUniverse ctx term = do
  ty <- infer ctx term
  case ty of
    VUniverse l -> Right l
    other -> reify ctx other >>= Left . ExpectedUniverse

check :: Context -> Term -> Value -> Either TypeError ()
check ctx term expected = case (term, expected) of
  (Lam _ body, VPi _ domain codomain) -> do
    bodyType <- liftEval (instantiateClosure codomain (fresh (size ctx)))
    check (extend ctx domain) body bodyType
  (Lam _ _, _) -> reify ctx expected >>= Left . ExpectedFunction
  _ -> do
    actual <- infer ctx term
    same <- liftEval (convertible (size ctx) actual expected)
    if same then Right () else do
      expectedTerm <- reify ctx expected
      actualTerm <- reify ctx actual
      Left (TypeMismatch expectedTerm actualTerm)

inferClosed :: Term -> Either TypeError Term
inferClosed term = infer empty term >>= reify empty

-- | The proposed type is itself checked before checking the term.
checkClosed :: Term -> Term -> Either TypeError ()
checkClosed term ty = do
  _ <- inferUniverse empty ty
  expected <- evaluate empty ty
  check empty term expected

-- | Return the inferred type and beta-normal form, after checking the input.
normalizeClosed :: Term -> Either TypeError (Term, Term)
normalizeClosed term = do
  ty <- inferClosed term
  normal <- evaluate empty term >>= reify empty
  Right (ty, normal)
