module Haskell.RangedSets.Ranges where

import Haskell.RangedSets.Boundaries

data Range a = Rg (Boundary a) (Boundary a)

rangeLower :: Ord a => DiscreteOrdered a => Range a -> Boundary a
rangeLower (Rg x y) = x

rangeUpper :: Ord a => DiscreteOrdered a => Range a -> Boundary a
rangeUpper (Rg x y) = y

rangeIsEmpty :: Ord a => DiscreteOrdered a => Range a -> Bool
rangeIsEmpty (Rg lower upper) = upper <= lower

instance (Ord a, DiscreteOrdered a) => Eq (Range a) where
    r1 == r2
      = rangeIsEmpty r1 && rangeIsEmpty r2 ||
          rangeLower r1 == rangeLower r2 && rangeUpper r1 == rangeUpper r2

instance (Ord a, DiscreteOrdered a) => Ord (Range a) where
    compare r1 r2
      = if r1 == r2 then EQ else
          if rangeIsEmpty r1 then LT else
            if rangeIsEmpty r2 then GT else
              compare (rangeLower r1) (rangeUpper r1) <>
                compare (rangeLower r2) (rangeUpper r2)
    x < y = compare x y == LT
    x > y = compare x y == GT
    x <= y = compare x y == LT || compare x y == EQ
    x >= y = compare x y == GT || compare x y == EQ
    max x y = if compare x y == GT then x else y
    min x y = if compare x y == LT then x else y

emptyRange :: Ord a => DiscreteOrdered a => Range a
emptyRange = Rg BoundaryAboveAll BoundaryBelowAll

rangeHas :: Ord a => DiscreteOrdered a => Range a -> a -> Bool
rangeHas (Rg b1 b2) v = (v />/ b1) && not (v />/ b2)

rangeListHas ::
               Ord a => DiscreteOrdered a => [Range a] -> a -> Bool
rangeListHas [Rg _ _] v = rangeHas (Rg x x₁) v
rangeListHas [Rg _ _, Rg _ _] v
  = rangeHas (Rg x x₁) v || rangeHas (Rg x₂ x₃) v
rangeListHas ls v = foldMap id $ map (\ r -> rangeHas r v) ls

fullRange :: Ord a => DiscreteOrdered a => Range a
fullRange = Rg BoundaryBelowAll BoundaryAboveAll

singletonRange :: Ord a => DiscreteOrdered a => a -> Range a
singletonRange v = Rg (BoundaryBelow v) (BoundaryAbove v)

rangeIsFull :: Ord a => DiscreteOrdered a => Range a -> Bool
rangeIsFull range = range == Rg BoundaryBelowAll BoundaryAboveAll

rangeOverlap ::
               Ord a => DiscreteOrdered a => Range a -> Range a -> Bool
rangeOverlap r1 r2
  = not (rangeIsEmpty r1) &&
      not (rangeIsEmpty r2) &&
        not
          (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)

rangeEncloses ::
                Ord a => DiscreteOrdered a => Range a -> Range a -> Bool
rangeEncloses r1 r2
  = rangeLower r1 <= rangeLower r2 && rangeUpper r2 <= rangeUpper r1
      || rangeIsEmpty r2

rangeIntersection ::
                    Ord a => DiscreteOrdered a => Range a -> Range a -> Range a
rangeIntersection (Rg l1 u1) (Rg l2 u2)
  = if rangeIsEmpty (Rg l1 u1) || rangeIsEmpty (Rg l2 u2) then
      Rg BoundaryAboveAll BoundaryBelowAll else
      Rg (max l1 l2) (min u1 u2)

rangeU2 ::
          Ord a => DiscreteOrdered a => Range a -> Range a -> [Range a]
rangeU2 (Rg l1 u1) (Rg l2 u2)
  = if touching then [Rg lower upper] else [Rg l1 u1, Rg l2 u2]
  where
    touching :: Bool
    touching = max l1 l2 <= min u1 u2
    lower :: Boundary a
    lower = min l1 l2
    upper :: Boundary a
    upper = max u1 u2

rangeU1 ::
          Ord a => DiscreteOrdered a => Range a -> Range a -> [Range a]
rangeU1 (Rg l1 u1) (Rg l2 u2)
  = if rangeIsEmpty (Rg l2 u2) then [Rg l1 u1] else
      rangeU2 (Rg l1 u1) (Rg l2 u2)

rangeUnion ::
             Ord a => DiscreteOrdered a => Range a -> Range a -> [Range a]
rangeUnion (Rg l1 u1) (Rg l2 u2)
  = if rangeIsEmpty (Rg l1 u1) then [Rg l2 u2] else
      rangeU1 (Rg l1 u1) (Rg l2 u2)

rangeDifference ::
                  Ord a => DiscreteOrdered a => Range a -> Range a -> [Range a]
rangeDifference (Rg lower1 upper1) (Rg lower2 upper2)
  = if intersects then filtered else [r1]
  where
    intersects :: Bool
    intersects = max lower1 lower2 < min upper1 upper2
    r1 :: Range a
    r1 = Rg lower1 upper1
    list :: [Range a]
    list = [Rg lower1 lower2, Rg upper2 upper1]
    filtered :: [Range a]
    filtered = filter (\ x -> rangeIsEmpty x == False) list

rangeSingletonValue ::
                      Ord a => DiscreteOrdered a => Range a -> Maybe a
rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryBelow v2))
  = if adjacent v1 v2 then Just v1 else Nothing
rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryAbove v2))
  = if v1 == v2 then Just v1 else Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryBelow v2))
  = adjacentBelow v2 >>=
      \ x ->
        adjacentBelow x >>= \ y -> if v1 == y then pure x else Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryAbove v2))
  = if adjacent v1 v2 then Just v2 else Nothing
rangeSingletonValue (Rg _ _) = Nothing

h :: Ord a => DiscreteOrdered a => Show a => Boundary a -> String
h BoundaryBelowAll = ""
h (BoundaryBelow x) = showsPrec 0 x "" ++ " <= "
h (BoundaryAbove x) = showsPrec 0 x "" ++ " < "
h BoundaryAboveAll = "show Range: lower bound is BoundaryAboveAll"

h2 :: Ord a => DiscreteOrdered a => Show a => Boundary a -> String
h2 BoundaryBelowAll = "show Range: upper bound is BoundaryBelowAll"
h2 (BoundaryBelow x) = " < " ++ showsPrec 0 x ""
h2 (BoundaryAbove x) = " <= " ++ showsPrec 0 x ""
h2 BoundaryAboveAll = ""

showHelper ::
             Show a =>
               Ord a => DiscreteOrdered a => Range a -> Maybe a -> String
showHelper r (Just v) = "x == " ++ showsPrec 0 v ""
showHelper r Nothing = lowerBound ++ "x" ++ upperBound
  where
    lowerBound :: String
    lowerBound = h (rangeLower r)
    upperBound :: String
    upperBound = h2 (rangeUpper r)

showHelper2 ::
              Show a => Ord a => DiscreteOrdered a => Range a -> String
showHelper2 r
  = if rangeIsEmpty r then "Empty" else
      if rangeIsFull r then "All x" else
        showHelper r (rangeSingletonValue r)

instance (Show a, Ord a, DiscreteOrdered a) => Show (Range a) where
    showsPrec _ = showString . showHelper2
    showList = defaultShowList (showString . showHelper2)

