-- | The free De Morgan algebra. Unlike Boolean algebra, i /\ ~i is not 0.
module Dragonfly.Interval
  ( Interval (..), normalInterval, equivalentInterval, mapDimensions
  , shiftInterval, substituteInterval ) where

import Data.List (nub, sort)
import Numeric.Natural (Natural)

data Interval = I0 | I1 | IVar Natural | INot Interval
              | IMeet Interval Interval | IJoin Interval Interval
  deriving (Eq, Ord, Show)

mapDimensions :: (Natural -> Interval) -> Interval -> Interval
mapDimensions f r = case r of
  I0 -> I0
  I1 -> I1
  IVar i -> f i
  INot a -> INot (go a)
  IMeet a b -> IMeet (go a) (go b)
  IJoin a b -> IJoin (go a) (go b)
  where go = mapDimensions f

shiftInterval :: Natural -> Natural -> Interval -> Interval
shiftInterval amount cutoff = mapDimensions $ \i -> IVar (if i >= cutoff then i + amount else i)

-- Removes the selected dimension entry, as term substitution does.
substituteInterval :: Natural -> Interval -> Interval -> Interval
substituteInterval index replacement = mapDimensions $ \i ->
  if i == index then replacement else IVar (if i > index then i - 1 else i)

-- Disjunctive normal form over signed generators, with absorption. Positive
-- and negative occurrences of a generator are independent lattice atoms.
type Literal = (Natural, Bool)
type DNF = [[Literal]]

canonical :: DNF -> DNF
canonical clauses = filter minimal unique
  where
    unique = nub (sort (map (nub . sort) clauses))
    minimal c = not (any (\d -> d /= c && all (`elem` c) d) unique)

dnf :: Bool -> Interval -> DNF
dnf neg r = case r of
  I0 -> if neg then [[]] else []
  I1 -> if neg then [] else [[]]
  IVar i -> [[(i, neg)]]
  INot a -> dnf (not neg) a
  IMeet a b -> if neg then join a b else meet a b
  IJoin a b -> if neg then meet a b else join a b
  where
    join a b = canonical (dnf neg a ++ dnf neg b)
    meet a b = canonical [x ++ y | x <- dnf neg a, y <- dnf neg b]

normalInterval :: Interval -> Interval
normalInterval = foldr join I0 . map (foldr meet I1 . map literal) . dnf False
  where
    literal (i, neg) = if neg then INot (IVar i) else IVar i
    meet a I1 = a
    meet a b = IMeet a b
    join a I0 = a
    join a b = IJoin a b

equivalentInterval :: Interval -> Interval -> Bool
equivalentInterval a b = dnf False a == dnf False b
