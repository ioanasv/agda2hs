module Haskell.Prim.Ranges where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Num
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.Foldable
open import Haskell.Prim.Monoid
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative
open import Haskell.Prim.Int
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Integral
open import Haskell.Prim.Tuple
open import Haskell.Prim.Double
open import Haskell.Prim.Bounded
open import Haskell.Prim.Boundaries

data Range (a : Set) : Set where
    Rg : Boundary a -> Boundary a -> Range a

rangeLower : Range a -> Boundary a 
rangeLower (Rg x y) = x

rangeUpper : Range a -> Boundary a
rangeUpper (Rg x y) = y

rangeIsEmpty : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Bool
rangeIsEmpty (Rg lower upper) = upper <= lower

instance
    isRangeEq : ⦃ Ord a ⦄ -> ⦃ DiscreteOrdered a ⦄ → Eq (Range a)
    isRangeEq . _==_ r1 r2 = (rangeIsEmpty r1 && rangeIsEmpty r2) || (rangeLower r1 == rangeLower r2 && rangeUpper r1 == rangeUpper r2)

    isRangeOrd : ⦃ Ord a ⦄ -> ⦃ DiscreteOrdered a ⦄ → Ord (Range a)
    isRangeOrd . compare r1 r2 = if_then_else_ (r1 == r2) EQ 
                        (if_then_else_ (rangeIsEmpty r1) LT (if_then_else_ (rangeIsEmpty r2) GT 
                        (compare (rangeLower r1) (rangeUpper r1) <> compare (rangeLower r2) (rangeUpper r2))))
    isRangeOrd ._<_ x y = compare x y == LT
    isRangeOrd ._>_ x y = compare x y == GT
    isRangeOrd ._<=_ x y = (compare x y == LT) || (compare x y == EQ)
    isRangeOrd ._>=_ x y = (compare x y == GT) || (compare x y == EQ)
    isRangeOrd .max x y = if (compare x y == GT) then x else y
    isRangeOrd .min x y = if (compare x y == LT) then x else y


-- | True if the value is within the range.
rangeHas : {{ Ord a }} -> Range a -> a -> Bool
rangeHas (Rg b1 b2) v = (v />/ b1) && not (v />/ b2)

-- | True if the value is within one of the ranges.
rangeListHas : {{ Ord a }} -> List (Range a) -> a -> Bool
rangeListHas ls v = or $ map (\r -> rangeHas r v) ls

-- | The empty range
emptyRange : {{ DiscreteOrdered a }} -> Range a
emptyRange = Rg BoundaryAboveAll BoundaryBelowAll

-- | The full range.  All values are within it.
fullRange : {{ DiscreteOrdered a }} -> Range a
fullRange = Rg BoundaryBelowAll BoundaryAboveAll

-- | A range containing a single value
singletonRange : {{ DiscreteOrdered a }} -> a -> Range a
singletonRange v = Rg (BoundaryBelow v) (BoundaryAbove v)

-- | A range is full if it contains every possible value.
rangeIsFull : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Bool
rangeIsFull range = (range == fullRange)

-- | Two ranges overlap if their intersection is non-empty.
rangeOverlap : {{Ord a}} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> Bool
rangeOverlap r1 r2 =
   not (rangeIsEmpty r1)
   && not (rangeIsEmpty r2)
   && not (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)

-- | The first range encloses the second if every value in the second range is
-- also within the first range.  If the second range is empty then this is
-- always true.
rangeEncloses : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> Bool
rangeEncloses r1 r2 =
   (rangeLower r1 <= rangeLower r2 && rangeUpper r2 <= rangeUpper r1)
   || rangeIsEmpty r2

rangeIntersection : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> Range a
rangeIntersection (Rg l1 u1) (Rg l2 u2) = if_then_else_ (rangeIsEmpty (Rg l1 u1) || rangeIsEmpty (Rg l2 u2)) emptyRange (Rg (max l1 l2) (min u1 u2))


rangeUnion : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> List (Range a)
rangeUnion (Rg l1 u1) (Rg l2 u2) = if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (if_then_else_ (rangeIsEmpty r2) (r1 ∷ []) (if_then_else_ touching ((Rg lower upper) ∷ []) (r1 ∷ r2 ∷ [])))
   where
     touching = (max l1 l2) <= (min u1 u2)
     lower = min l1 l2
     upper = max u1 u2
     r1 = Rg l1 u1
     r2 = Rg l2 u2

rangeDifference : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> List (Range a)
rangeDifference (Rg lower1 upper1) (Rg lower2 upper2) = if_then_else_ intersects filtered (r1 ∷ [])
   where
      intersects = ((max lower1 lower2) < (min upper1 upper2))
      r1 = Rg lower1 upper1
      list = ((Rg lower1 lower2) ∷ (Rg upper2 upper1) ∷ [])
      filtered = filter (λ x -> (rangeIsEmpty x) == false) list

rangeSingletonValue : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Maybe a
rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryBelow v2)) = if_then_else_ (adjacent v1 v2) (Just v1) Nothing
rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryAbove v2)) = if_then_else_ (v1 == v2) (Just v1) Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryBelow v2)) = adjacentBelow v2 >>= λ x → adjacentBelow x >>= λ y -> if_then_else_ (v1 == y) (return x) Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryAbove v2)) = if_then_else_ (adjacent v1 v2) (Just v2) Nothing
rangeSingletonValue (Rg _ _) = Nothing