-- | Checked, AST-only cubical kernel. Values and evaluator internals are not
-- exported. Type checking precedes normalization through this interface.
module Dragonfly.Cubical
  ( Ter (U, Var, Ann, Pi, Lam, App, Sigma, Pair, Fst, Snd, PathP, PLam
        , AppFormula, Comp, Fill, Glue, GlueElem, UnGlueElem)
  , Name (..), Dir (..), Formula (..), Face, System, system, faceOf
  , TypeError (..), checkClosed, inferClosed, normalizeClosed, normalizesTo
  , path, equiv, ua, uaType, transport, identityEquivalence
  , bool, false, true, pairBool, swapEquivalence, swapPath
  ) where

import qualified Data.Map as Map
import Dragonfly.Cubical.Connections
import Dragonfly.Cubical.Syntax
import Dragonfly.Cubical.Check hiding (inferClosed)
import qualified Dragonfly.Cubical.Check as Check
import Dragonfly.Cubical.Univalence

-- Keep overlapping faces intact until the checker verifies compatibility.
system :: [(Face, Ter)] -> System Ter
system = Map.fromList

faceOf :: Name -> Dir -> Face
faceOf = (~>)

inferClosed :: Ter -> Either TypeError String
inferClosed = fmap show . Check.inferClosed
