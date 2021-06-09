module Haskell.RangedSets.Ranges where

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
open import Haskell.Prim.Real
open import Haskell.Prim.Show
open import Haskell.Prim.String
open import Haskell.Prim.Tuple

open import Haskell.RangedSets.Boundaries

{-# FOREIGN AGDA2HS
import Haskell.RangedSets.Boundaries
#-}

data Range (a : Set) ⦃ o : Ord a ⦄ ⦃ dio : DiscreteOrdered a ⦄ : Set where
    Rg : Boundary a → Boundary a → Range a
{-# COMPILE AGDA2HS Range #-}

rangeLower : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → Boundary a 

rangeUpper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → Boundary a

rangeIsEmpty : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Bool

emptyRange : ⦃  o : Ord a ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a

rangeHas : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → a → Bool

rangeListHas : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → List (Range a) → a → Bool

fullRange : ⦃ o : Ord a ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a

singletonRange : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → a → Range a

rangeIsFull : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Bool

rangeOverlap : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → Bool

rangeEncloses : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → Bool

rangeUnion : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → List (Range a)

rangeIntersection : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → Range a

rangeDifference : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → List (Range a)

rangeSingletonValue : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Maybe a

instance
    isRangeEq : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Eq (Range a)
    isRangeEq . _==_ r1 r2 = (rangeIsEmpty r1 && rangeIsEmpty r2) || (rangeLower r1 == rangeLower r2 && rangeUpper r1 == rangeUpper r2)
{-# COMPILE AGDA2HS isRangeEq #-}

instance
    isRangeOrd : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Ord (Range a)
    isRangeOrd . compare r1 r2 = if_then_else_ (r1 == r2) EQ 
                        (if_then_else_ (rangeIsEmpty r1) LT (if_then_else_ (rangeIsEmpty r2) GT 
                        (compare (rangeLower r1) (rangeUpper r1) <> compare (rangeLower r2) (rangeUpper r2))))
    isRangeOrd ._<_ x y = compare x y == LT
    isRangeOrd ._>_ x y = compare x y == GT
    isRangeOrd ._<=_ x y = (compare x y == LT) || (compare x y == EQ)
    isRangeOrd ._>=_ x y = (compare x y == GT) || (compare x y == EQ)
    isRangeOrd .max x y = if (compare x y == GT) then x else y
    isRangeOrd .min x y = if (compare x y == LT) then x else y
{-# COMPILE AGDA2HS isRangeOrd #-}

h : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → ⦃ Show a ⦄ → Boundary a → String
h BoundaryBelowAll = ""
h (BoundaryBelow x) = show x ++ " <= "
h (BoundaryAbove x) = show x ++ " < "
h BoundaryAboveAll = "show Range: lower bound is BoundaryAboveAll"
{-# COMPILE AGDA2HS h #-}

h2 : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → ⦃ Show a ⦄ → Boundary a → String
h2 BoundaryBelowAll = "show Range: upper bound is BoundaryBelowAll"
h2 (BoundaryBelow x) = " < " ++ show x
h2 (BoundaryAbove x) = " <= " ++ show x
h2 BoundaryAboveAll = ""
{-# COMPILE AGDA2HS h2 #-}

showHelper : ⦃ Show a ⦄ → ⦃  o : Ord a  ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → Maybe a → String
showHelper r (Just v) = "x == " ++ show v
showHelper r Nothing = lowerBound ++ "x" ++ upperBound
         where 
            lowerBound = h (rangeLower r)
            upperBound = h2 (rangeUpper r)
showHelper2 : ⦃ Show a ⦄ → ⦃  o : Ord a  ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → String 
showHelper2 r = if_then_else_ (rangeIsEmpty r) "Empty" (if_then_else_ (rangeIsFull r) "All x" (showHelper r (rangeSingletonValue r)))
{-# COMPILE AGDA2HS showHelper #-}
{-# COMPILE AGDA2HS showHelper2 #-}

instance
   isRangeShow : ⦃ Show a ⦄ → ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Show (Range a)
   isRangeShow .showsPrec _ = showString ∘ showHelper2
   isRangeShow .showList = defaultShowList (showString ∘ showHelper2)
{-# COMPILE AGDA2HS isRangeShow #-}

rangeLower ⦃ o ⦄ ⦃ dio ⦄ (Rg x y) = x
{-# COMPILE AGDA2HS rangeLower #-}

rangeUpper ⦃ o ⦄ ⦃ dio ⦄ (Rg x y) = y
{-# COMPILE AGDA2HS rangeUpper #-}

rangeIsEmpty r@(Rg lower upper) = upper <= lower
{-# COMPILE AGDA2HS rangeIsEmpty #-}

emptyRange = Rg BoundaryAboveAll BoundaryBelowAll
{-# COMPILE AGDA2HS emptyRange #-}

rangeHas r@(Rg b1 b2) v = (v />/ b1) && not (v />/ b2)
{-# COMPILE AGDA2HS rangeHas #-}

rangeHas1 : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → a → Range a → Bool
rangeHas1 v r@(Rg b1 b2) = (v />/ b1) && not (v />/ b2)

rangeListHas (r@(Rg _ _) ∷ []) v = rangeHas r v
rangeListHas (r1@(Rg _ _) ∷ r2@(Rg _ _) ∷ []) v = (rangeHas r1 v) || (rangeHas r2 v)
rangeListHas ls v = or $ map (\r → rangeHas r v) ls
{-# COMPILE AGDA2HS rangeListHas #-}

rangeListHas1 : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → a → List (Range a) → Bool
rangeListHas1 v (r@(Rg _ _) ∷ []) = rangeHas r v
rangeListHas1 v (r1@(Rg _ _) ∷ r2@(Rg _ _) ∷ []) = (rangeHas r1 v) || (rangeHas r2 v)
rangeListHas1 v ls = or $ map (\r → rangeHas r v) ls

fullRange ⦃ o ⦄ ⦃ dio ⦄ = Rg BoundaryBelowAll BoundaryAboveAll
{-# COMPILE AGDA2HS fullRange #-}

singletonRange v = Rg (BoundaryBelow v) (BoundaryAbove v)
{-# COMPILE AGDA2HS singletonRange #-}

rangeIsFull range = (range == fullRange)
{-# COMPILE AGDA2HS rangeIsFull #-}

rangeOverlap r1 r2 =
   not (rangeIsEmpty r1) && not (rangeIsEmpty r2) && not (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)
{-# COMPILE AGDA2HS rangeOverlap #-}

rangeEncloses r1 r2 =
   (rangeLower r1 <= rangeLower r2 && rangeUpper r2 <= rangeUpper r1)
   || rangeIsEmpty r2
{-# COMPILE AGDA2HS rangeEncloses #-}

rangeIntersection r1@(Rg l1 u1) r2@(Rg l2 u2) = if_then_else_ (rangeIsEmpty r1 || rangeIsEmpty r2) emptyRange (Rg (max l1 l2) (min u1 u2))
{-# COMPILE AGDA2HS rangeIntersection #-}

rangeU2 : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → List (Range a)
rangeU2 r1@(Rg l1 u1) r2@(Rg l2 u2) = (if_then_else_ touching ((Rg lower upper) ∷ []) (r1 ∷ r2 ∷ []))
   where
     touching = (max l1 l2) <= (min u1 u2)
     lower = min l1 l2
     upper = max u1 u2
{-# COMPILE AGDA2HS rangeU2 #-}

rangeU1 : ⦃  o : Ord a  ⦄ → ⦃  dio : DiscreteOrdered a  ⦄ → Range a → Range a → List (Range a)
rangeU1 r1@(Rg l1 u1) r2@(Rg l2 u2) = if_then_else_ (rangeIsEmpty r2) (r1 ∷ []) (rangeU2 r1 r2)
{-# COMPILE AGDA2HS rangeU1 #-}

rangeUnion r1@(Rg l1 u1) r2@(Rg l2 u2) = if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (rangeU1 r1 r2)
{-# COMPILE AGDA2HS rangeUnion #-}

rangeDifference (Rg lower1 upper1) (Rg lower2 upper2) = if_then_else_ intersects filtered (r1 ∷ [])
   where
      intersects = ((max lower1 lower2) < (min upper1 upper2))
      r1 = Rg lower1 upper1
      list = ((Rg lower1 lower2) ∷ (Rg upper2 upper1) ∷ [])
      filtered = filter (λ x → (rangeIsEmpty x) == false) list
{-# COMPILE AGDA2HS rangeDifference #-}

rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryBelow v2)) = if_then_else_ (adjacent v1 v2) (Just v1) Nothing
rangeSingletonValue (Rg (BoundaryBelow v1) (BoundaryAbove v2)) = if_then_else_ (v1 == v2) (Just v1) Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryBelow v2)) = adjacentBelow v2 >>= λ x → adjacentBelow x >>= λ y → if_then_else_ (v1 == y) (return x) Nothing
rangeSingletonValue (Rg (BoundaryAbove v1) (BoundaryAbove v2)) = if_then_else_ (adjacent v1 v2) (Just v2) Nothing
rangeSingletonValue (Rg _ _) = Nothing
{-# COMPILE AGDA2HS rangeSingletonValue #-}
