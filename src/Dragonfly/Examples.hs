module Dragonfly.Examples (identityType, identity, examples) where

import Dragonfly.Syntax
import Numeric.Natural (Natural)

-- (A : Type l) -> (x : A) -> A
identityType :: Natural -> Term
identityType l = Pi "A" (Universe l) (Pi "x" (Var 0) (Var 1))

identity :: Natural -> Term
identity l = Ann (Lam "A" (Lam "x" (Var 0))) (identityType l)

examples :: [(String, Term)]
examples =
  [ ("Polymorphic identity", identity 0)
  , ("Identity specialized to Type 0", App (identity 1) (Universe 0))
  , ("Identity applied to Type 0", App (App (identity 2) (Universe 1)) (Universe 0))
  , ("Identity applied to polymorphic identity", App (App (identity 1) (identityType 0)) (identity 0))
  ]
