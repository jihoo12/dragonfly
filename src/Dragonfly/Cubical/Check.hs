-- Level-indexed boundary for cubicaltt's computational core.
module Dragonfly.Cubical.Check
  ( TypeError (..), inferClosed, checkClosed, normalizesTo, normalizeClosed ) where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.Reader
import Control.Monad.Except (throwError)
import qualified Data.Map as Map
import Data.List (nub)
import Numeric.Natural (Natural)
import Dragonfly.Cubical.Connections
import Dragonfly.Cubical.Syntax
import Dragonfly.Cubical.Eval hiding (inferType)

data TypeError = TypeError String deriving (Eq, Show)
data Context = Context { environment :: Env, usedNames :: [String] }
type Typing = ReaderT Context (Either TypeError)

emptyContext :: Context
emptyContext = Context emptyEnv []

failure :: String -> Typing a
failure = throwError . TypeError

value :: Ter -> Typing Val
value t = asks (\ctx -> eval (environment ctx) t)

same :: Val -> Val -> Typing ()
same a b = do
  ns <- asks usedNames
  unless (conv ns a b) (failure ("Not convertible: " ++ show a ++ " versus " ++ show b))

withVar :: Ident -> Val -> (Val -> Typing a) -> Typing a
withVar x ty body = do
  ctx <- ask
  let choose n | n `elem` usedNames ctx = choose (n ++ "'")
               | otherwise = n
      name = choose x
      v = VVar name ty
  local (const (Context (upd (x,v) (environment ctx)) (name : usedNames ctx))) (body v)

-- Fresh semantic dimension names allow source binders to shadow safely.
withDim :: Name -> (Name -> Typing a) -> Typing a
withDim source body = do
  rho <- asks environment
  let j = fresh rho
  local (\ctx -> ctx {environment = sub (source,Atom j) rho}) (body j)

lookupVariable :: Ident -> Typing Val
lookupVariable x = do
  rho <- asks environment
  let go (Env (Upd y rest,v:vs,fs,os))
        | x == y = case v of VVar _ ty -> Just ty; _ -> Nothing
        | otherwise = go (Env (rest,vs,fs,os))
      go (Env (Sub _ rest,vs,_:fs,os)) = go (Env (rest,vs,fs,os))
      go _ = Nothing
  maybe (failure ("Unbound variable: " ++ x)) pure (go rho)

checkFormula :: Formula -> Typing ()
checkFormula r = do
  dom <- asks (domainEnv . environment)
  unless (all (`elem` dom) (support r)) (failure ("Unbound dimension in " ++ show r))

inferType :: Ter -> Typing Natural
inferType t = do
  ty <- infer t
  case ty of
    VU l -> pure l
    _ -> failure ("Expected a type, inferred " ++ show ty)

-- Infer a uniform universe for a dimension-indexed family, without U : U.
inferFamily :: Ter -> Typing (Natural, Val)
inferFamily t@(PLam i body) = do
  l <- withDim i (const (inferType body))
  v <- value t
  pure (l,v)
inferFamily t = do
  ty <- infer t
  case ty of
    VPathP family _ _ -> do
      rho <- asks environment
      let j = fresh (rho,family)
      case family @@ j of
        VU l -> do
          same family (constPath (VU l))
          v <- value t
          pure (l,v)
        _ -> failure "Expected a path of types in one universe"
    _ -> failure "Expected a dimension abstraction or a path of types"

checkLine :: Val -> Ter -> Typing (Val,Val)
checkLine family (PLam i body) = withDim i $ \j -> do
  check (family @@ j) body
  v <- value body
  pure (v `act` (j,Dir Zero), v `act` (j,Dir One))
checkLine family t = do
  ty <- infer t
  case ty of
    VPathP actual a b -> same actual family >> pure (a,b)
    _ -> failure "Expected a path"

-- A source face may split into multiple semantic faces under substitution.
-- Validate EVERY supplied side and its overlaps before mkSystem absorbs faces.
checkedSystem :: System Ter -> (Face -> Ter -> Typing ()) -> Typing (System Val)
checkedSystem sides checkSide = do
  rho <- asks environment
  ns <- asks usedNames
  entries <- fmap concat $ forM (Map.toList sides) $ \(alpha,t) -> do
    mapM_ (checkFormula . Atom) (Map.keys alpha)
    let betas = meetss [invFormula (evalFormula rho (Atom i)) d | (i,d) <- Map.toList alpha]
    forM betas $ \beta -> local (\ctx -> ctx {environment = rho `face` beta}) $ do
      checkSide beta t
      v <- value t
      pure (beta,v)
  forM_ [(x,y) | (n,x) <- zip [0 :: Int ..] entries, y <- drop (n+1) entries] $
    \((alpha,u),(beta,v)) -> when (compatible alpha beta) $
      unless (conv ns (u `face` beta) (v `face` alpha)) (failure "Incompatible overlapping system sides")
  pure (mkSystem entries)

-- Bundled partial equivalence: (T : Type l) * Equiv T A.
-- Internal names are fresh because the supplied base is stored semantically.
equivType :: Natural -> Val -> Val
equivType l base = eval (upd ("$base",base) emptyEnv) $
  Sigma (Lam "$T" (U l) (Sigma (Lam "$f" (Pi (Lam "$x" t a))
    (Pi (Lam "$b" a (Sigma (Lam "$center" fib
      (Pi (Lam "$z" fib (PathP (PLam (Name "$constant") fib) (Var "$center") (Var "$z")))))))))))
  where
    t = Var "$T"
    a = Var "$base"
    fib = Sigma (Lam "$x" t (PathP (PLam (Name "$constant") a) (Var "$b") (App (Var "$f") (Var "$x"))))

checkGlueSystem :: Natural -> Val -> System Ter -> Typing (System Val)
checkGlueSystem l base ts = checkedSystem ts $ \beta -> check (equivType l (base `face` beta))

checkTube :: Val -> Ter -> System Ter -> Typing (System Val)
checkTube family start ts = checkedSystem ts $ \beta t -> do
  (a,_) <- checkLine (family `face` beta) t
  v <- value start
  same a v

infer :: Ter -> Typing Val
infer term = case term of
  U l -> pure (VU (l+1))
  Var x -> lookupVariable x
  Ann t a -> do
    _ <- inferType a
    ty <- value a
    check ty t
    pure ty
  Pi f -> VU <$> inferPiSigma f
  Sigma f -> VU <$> inferPiSigma f
  App f x -> do
    ty <- infer f
    case ty of
      VPi a b -> check a x >> app b <$> value x
      _ -> failure "Application requires a Pi type"
  Fst t -> do
    ty <- infer t
    case ty of
      VSigma a _ -> pure a
      _ -> failure "Projection requires a Sigma type"
  Snd t -> do
    ty <- infer t
    case ty of
      VSigma _ b -> app b . fstVal <$> value t
      _ -> failure "Projection requires a Sigma type"
  PathP family a b -> do
    (l,vf) <- inferFamily family
    check (vf @@ Zero) a
    check (vf @@ One) b
    pure (VU l)
  AppFormula p r -> do
    checkFormula r
    ty <- infer p
    rho <- asks environment
    case ty of
      VPathP family _ _ -> pure (family @@ evalFormula rho r)
      _ -> failure "Dimension application requires a path"
  Comp family start ts -> do
    (_,vf) <- inferFamily family
    check (vf @@ Zero) start
    _ <- checkTube vf start ts
    pure (vf @@ One)
  Fill family start ts -> do
    (_,vf) <- inferFamily family
    check (vf @@ Zero) start
    vs <- checkTube vf start ts
    v <- value start
    pure (VPathP vf v (compLine vf v vs))
  Glue l base ts -> do
    check (VU l) base
    vb <- value base
    _ <- checkGlueSystem l vb ts
    pure (VU l)
  GlueElem ty base us -> do
    l <- inferType ty
    target <- value ty
    case gluePresentation ty of
      Just (EquivalenceGlue _ b ts) -> do
        vb <- value b
        vs <- asks (\ctx -> evalSystem (environment ctx) ts)
        checkGlueIntro vb vs base us equivDom (\e x -> app (equivFun e) x)
      Just (UniverseGlue family b ts) -> do
        checkUniverseFamily l family
        vb <- value b
        vs <- asks (\ctx -> evalSystem (environment ctx) ts)
        checkGlueIntro vb vs base us (@@ One) eqFun
      Nothing -> case target of
        VGlue _ b vs -> checkGlueIntro b vs base us equivDom (\e x -> app (equivFun e) x)
        VCompU _ b vs -> checkGlueIntro b vs base us (@@ One) eqFun
        _ -> failure "Glue introduction requires a Glue or universe composition type"
    pure target
  UnGlueElem t ty -> do
    l <- inferType ty
    -- Do not recover this data from the reduced type: that is not stable
    -- under dimension substitution. Explicit presentations may be annotated.
    base <- case gluePresentation ty of
      Just (EquivalenceGlue _ b _) -> pure b
      Just (UniverseGlue family b _) -> checkUniverseFamily l family >> pure b
      Nothing -> failure "Unglue requires an explicit Glue or universe Comp presentation (possibly annotated)"
    target <- value ty
    check target t
    value base
  -- A finite, nullary sum suffices for the closed computational witness.
  -- No recursive definitions, positivity assumptions, or datatype eliminator.
  Sum _ _ labels -> do
    unless (all nullary labels && distinct (map labelName labels)) $
      failure "Only finite nullary sums are supported"
    pure (VU 0)
  _ -> failure ("Cannot infer this term; annotate introductions. Unsupported forms are rejected: " ++ show term)
  where
    nullary (OLabel _ []) = True
    nullary _ = False
    distinct xs = length xs == length (nub xs)

-- A Comp ending in a universe need not be a composition IN that universe.
-- For its Glue presentation the entire family must be that fixed universe.
checkUniverseFamily :: Natural -> Ter -> Typing ()
checkUniverseFamily l family = do
  vf <- value family
  same vf (constPath (VU l))

inferPiSigma :: Ter -> Typing Natural
inferPiSigma (Lam x a b) = do
  l <- inferType a
  va <- value a
  r <- withVar x va (const (inferType b))
  pure (max l r)
inferPiSigma _ = failure "Pi/Sigma requires a binder"

checkGlueIntro :: Val -> System Val -> Ter -> System Ter
               -> (Val -> Val) -> (Val -> Val -> Val) -> Typing ()
checkGlueIntro base equivs baseTerm sides domainOf forward = do
  check base baseTerm
  v <- value baseTerm
  values <- checkedSystem sides $ \beta t -> case Map.lookup eps (equivs `face` beta) of
    Nothing -> failure "Glue side is outside the equivalence system"
    Just e -> check (domainOf e) t
  unless (Map.keys values == Map.keys equivs) (failure "Glue element and equivalence faces differ")
  forM_ (Map.toList values) $ \(beta,x) -> same (forward (equivs Map.! beta) x) (v `face` beta)

check :: Val -> Ter -> Typing ()
check expected term = case (expected,term) of
  (VPi a b,Lam x annotation body) -> do
    _ <- inferType annotation
    va <- value annotation
    same a va
    withVar x a $ \v -> check (app b v) body
  (VSigma a b,Pair x y) -> do
    check a x
    vx <- value x
    check (app b vx) y
  (VPathP family a b,PLam i body) -> do
    (va,vb) <- checkLine family (PLam i body)
    same a va
    same b vb
  (Ter (Sum _ _ labels) _,Con name []) ->
    unless (OLabel name [] `elem` labels) (failure ("Unknown constructor " ++ name))
  _ -> infer term >>= same expected

inferClosed :: Ter -> Either TypeError Val
inferClosed t = runReaderT (infer t) emptyContext

checkClosed :: Ter -> Ter -> Either TypeError ()
checkClosed t ty = runReaderT (inferType ty >> value ty >>= \v -> check v t) emptyContext

normalizesTo :: Ter -> Ter -> Ter -> Either TypeError Bool
normalizesTo t expected ty = do
  checkClosed t ty
  checkClosed expected ty
  pure (conv [] (eval emptyEnv t) (eval emptyEnv expected))

normalizeClosed :: Ter -> Either TypeError String
normalizeClosed t = do
  _ <- inferClosed t
  pure (show (normal [] (eval emptyEnv t)))
