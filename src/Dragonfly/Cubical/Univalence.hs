-- Ordinary terms, not new evaluator primitives or axioms.
module Dragonfly.Cubical.Univalence
  ( path, equiv, ua, uaType, transport, identityEquivalence
  , bool, false, true, pairBool, swapEquivalence, swapPath ) where

import Numeric.Natural (Natural)
import Dragonfly.Cubical.Syntax
import Dragonfly.Cubical.Connections

-- Pick binder names absent from the supplied syntax to avoid capturing free
-- variables when these Haskell AST builders are used in an open context.
freshIdentifier :: [Ter] -> String -> String
freshIdentifier terms = choose
  where
    used = concatMap identifiers terms
    choose name | name `elem` used = choose (name ++ "'")
                | otherwise = name

constant :: Ter -> Ter
constant t = PLam (Name (freshIdentifier [t] "$constant")) t

path :: Ter -> Ter -> Ter -> Ter
path a = PathP (constant a)

fiber :: Ter -> Ter -> Ter -> Ter -> Ter
fiber a b f y = Sigma (Lam x a (path b y (App f (Var x))))
  where x = freshIdentifier [a,b,f,y] "$fiberX"

isContr :: Ter -> Ter
isContr a = Sigma (Lam x a (Pi (Lam y a (path a (Var x) (Var y)))))
  where x = freshIdentifier [a] "$center"
        y = freshIdentifier [a] "$other"

equiv :: Ter -> Ter -> Ter
equiv a b = Sigma (Lam f (Pi (Lam x a b)) (Pi (Lam y b (isContr (fiber a b (Var f) (Var y))))))
  where f = freshIdentifier [a,b] "$equivF"
        x = freshIdentifier [a,b] "$equivX"
        y = freshIdentifier [a,b] "$equivY"

identityEquivalence :: Ter -> Ter
identityEquivalence a = involutionEquivalence a (Lam x a (Var x))
  where x = freshIdentifier [a] "$identityX"

-- For a definitionally involutive function f, the fiber over y contracts
-- along (f (q @ i), <j> q @ (i /\ j)). This is checked as ordinary syntax.
involutionEquivalence :: Ter -> Ter -> Ter
involutionEquivalence a function = Pair f (Lam y a (Pair center (Lam z fib contraction)))
  where
    f = Ann function (Pi (Lam (freshIdentifier [a] "$involutionArgument") a a))
    y = freshIdentifier [a,function] "$contractY"
    z = freshIdentifier [a,function] "$contractZ"
    iname = freshIdentifier [a,function] "$contractI"
    jname = freshIdentifier [a,function] "$contractJ"
    i = Name iname
    j = Name jname
    fib = fiber a a f (Var y)
    center = Pair (App f (Var y)) (constant (Var y))
    q = Snd (Var z)
    contraction = PLam i (Pair (App f (AppFormula q (Atom i)))
                     (PLam j (AppFormula q (Atom i :/\: Atom j))))

-- ua_l : (A B : Type l) -> Equiv A B -> Path (Type l) A B
-- Glue's two endpoint faces supply e and the identity equivalence.
ua :: Natural -> Ter
ua l = Ann body (uaType l)
  where
    a = Var "$uaA"
    b = Var "$uaB"
    e = Var "$uaE"
    i = Name "$uaI"
    body = Lam "$uaA" (U l) (Lam "$uaB" (U l) (Lam "$uaE" (equiv a b)
      (PLam i (Glue l b (mkSystem
        [(i ~> Zero,Pair a e),(i ~> One,Pair b (identityEquivalence b))])))))

uaType :: Natural -> Ter
uaType l = Pi (Lam "$uaA" (U l) (Pi (Lam "$uaB" (U l)
  (Pi (Lam "$uaE" (equiv a b) (path (U l) a b))))))
  where a = Var "$uaA"; b = Var "$uaB"

transport :: Ter -> Ter -> Ter
transport family start = Comp family start (mkSystem [])

bool :: Ter
bool = Sum (Loc "dragonfly:Bool" (0,0)) "Bool" [OLabel "false" [],OLabel "true" []]

false, true, pairBool, swapEquivalence, swapPath :: Ter
false = Con "false" []
true = Con "true" []
pairBool = Sigma (Lam "$pair" bool bool)
swapEquivalence = Ann (involutionEquivalence pairBool swapFunction) (equiv pairBool pairBool)
  where swapFunction = Lam "$swap" pairBool (Pair (Snd (Var "$swap")) (Fst (Var "$swap")))
swapPath = App (App (App (ua 0) pairBool) pairBool) swapEquivalence
