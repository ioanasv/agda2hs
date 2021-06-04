module Haskell.RangedSets.RangedSet where
open import Agda.Builtin.Equality

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Num
open import Haskell.Prim.Eq
open import Haskell.Prim.Foldable
open import Haskell.Prim.Monoid
open import Haskell.Prim.Int
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Real

open import Haskell.RangedSets.Boundaries
open import Haskell.RangedSets.Ranges
open import Haskell.RangedSetsProp.library

{-# FOREIGN AGDA2HS
import Haskell.RangedSets.Boundaries
#-}
{-# FOREIGN AGDA2HS
import Haskell.RangedSets.Ranges
#-}
{-# FOREIGN AGDA2HS
import Data.List
#-}

infixl 7 _-/\-_
infixl 6 _-\/-_ _-!-_
infixl 5 _-<=-_ _-<-_ _-?-_


okAdjacent : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → Range a → Bool
okAdjacent r@(Rg lower1 upper1) r2@(Rg lower2 upper2) = rangeLower r <= rangeUpper r && rangeUpper r <= rangeLower r2 && rangeLower r2 <= rangeUpper r2
{-# COMPILE AGDA2HS okAdjacent #-}

validRangeList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → Bool
validRangeList [] = true
validRangeList (x ∷ []) = (rangeLower x) <= (rangeUpper x)
validRangeList (x ∷ rs@(r1 ∷ rss)) = (okAdjacent x r1) && (validRangeList rs)
{-# COMPILE AGDA2HS validRangeList #-}

validBoundaryList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Boundary a) → Bool
validBoundaryList [] = true
validBoundaryList (x ∷ []) = true
validBoundaryList (x ∷ rs@(r1 ∷ rss)) = (x <= r1) && (validBoundaryList rs)

data RSet (a : Set) ⦃ o : Ord a ⦄ 
      ⦃ dio : DiscreteOrdered a ⦄ : Set where
    RS :  (rg : List (Range a)) 
      → {IsTrue (validRangeList rg)} → RSet a

{-# COMPILE AGDA2HS RSet #-}

rSetRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → RSet a → List (Range a)
rSetRanges (RS ranges) = ranges
{-# COMPILE AGDA2HS rSetRanges #-}

overlap1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Range a → Range a → Bool
overlap1 (Rg _ upper1) (Rg lower2 _) = (upper1 >= lower2)
{-# COMPILE AGDA2HS overlap1 #-}

sortedRangeList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → Bool
sortedRangeList [] = true 
sortedRangeList (r ∷ []) = true 
sortedRangeList (r1 ∷ r2 ∷ rs) = (r1 <= r2) && (sortedRangeList (r2 ∷ rs))

validRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → Bool
validRanges [] = true 
validRanges (r ∷ rs) = (rangeLower r <= rangeUpper r) && (validRanges rs)

headandtailSorted : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      → ⦃ ne : NonEmpty rs ⦄ → (IsTrue (sortedRangeList rs)) 
      → (IsTrue (sortedRangeList (tail rs ⦃ ne ⦄))) 
headandtailValidRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      → ⦃ ne : NonEmpty rs ⦄ → (IsTrue (validRanges rs)) 
      → (IsTrue (validRanges (tail rs ⦃ ne ⦄)))

normalise : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
   → (rg : List (Range a)) 
   → ⦃ IsTrue (sortedRangeList rg) ⦄ 
   → ⦃ IsTrue (validRanges rg) ⦄
   → List (Range a)

postulate 
   sortedList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      -> IsTrue (sortedRangeList (sort (filter (λ r → (rangeIsEmpty r) == false) rs)))

   validRangesList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      -> IsTrue (validRanges (sort (filter (λ r → (rangeIsEmpty r) == false) rs)))   


unsafeRangedSet : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                → (rg : List (Range a)) 
                → ⦃ IsTrue (validRangeList ⦃ o ⦄ ⦃ dio ⦄ rg) ⦄ → RSet a
unsafeRangedSet rs ⦃ prf ⦄  = RS rs {prf}

{-# COMPILE AGDA2HS unsafeRangedSet #-}

-- validFunction3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → {x : Boundary a} → (f : Boundary a → Boundary a) → Bool
-- validFunction3 {x = b@(BoundaryBelow y)} f = (f b) > b
-- validFunction3 {x = b@(BoundaryAbove y)} f = (f b) > b
-- validFunction3 {x = b@(BoundaryBelowAll)} f = (f b) > b
-- validFunction3 {x = b@(BoundaryAboveAll)} f = (f b) > b

validFunction2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) → (f : Boundary a → Boundary a) → Bool
validFunction2 b f = (f b) > b

validFunction : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) → (g : Boundary a → Maybe (Boundary a)) → Bool
validFunction b g with (g b)
...                       | Nothing = true 
...                       | Just b2 = (b2 > b)

ranges3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → 
      Maybe (Boundary a) → (f : Boundary a → Boundary a) → (g : Boundary a → Maybe (Boundary a))
      → List (Range a)
{-# TERMINATING #-}
ranges2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
      → (f : Boundary a → Boundary a) → (g : Boundary a → Maybe (Boundary a))
      → List (Range a)
ranges2 b upperFunc succFunc = (Rg b (upperFunc b)) ∷ (ranges3 (succFunc b) upperFunc succFunc)

ranges3 (Just b1) upperFunc succFunc = if ((validFunction2 b1 upperFunc) && (validFunction b1 succFunc)) then
                              (ranges2 b1 upperFunc succFunc) else []
ranges3 Nothing _ _ = []
{-# COMPILE AGDA2HS ranges2 #-}
{-# COMPILE AGDA2HS ranges3 #-}

setBounds1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
            → (xs : List (Boundary a)) → List (Boundary a)
setBounds1 (BoundaryBelowAll ∷ xs) = xs 
setBounds1 xs = (BoundaryBelowAll ∷ xs)
{-# COMPILE AGDA2HS setBounds1 #-}

bounds1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
         → List (Range a) → List (Boundary a)
bounds1 (r ∷ rs) = (rangeLower r) ∷ (rangeUpper r) ∷ (bounds1 rs)
bounds1 [] = []
{-# COMPILE AGDA2HS bounds1 #-}

ranges1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
         → List (Boundary a) → List (Range a)
ranges1 (b1 ∷ b2 ∷ bs) = (Rg b1 b2) ∷ (ranges1 bs)
ranges1 (BoundaryAboveAll ∷ [])  = []
ranges1 (b ∷ []) = (Rg b BoundaryAboveAll) ∷ []
ranges1 _ = []
{-# COMPILE AGDA2HS ranges1 #-}

merge1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → List (Range a) → List (Range a)
merge1 [] [] = []
merge1 ms1@(h1 ∷ t1) [] = ms1
merge1 [] ms2@(h2 ∷ t2) = ms2
merge1 ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
{-# COMPILE AGDA2HS merge1 #-}

merge2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → List (Range a) → List (Range a)
merge2 [] [] = []
merge2 ms1@(h1 ∷ t1) [] = []
merge2 [] ms2@(h2 ∷ t2) = []
merge2 ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
   (rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h1 < rangeUpper h2) (merge2 t1 ms2) (merge2 ms1 t2))
{-# COMPILE AGDA2HS merge2 #-}

postulate

   sortedListComposed : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
            → (r1 r2 : Range a) → (ranges : List (Range a))
            → IsTrue (sortedRangeList (r1 ∷ r2 ∷ ranges))
            → IsTrue (sortedRangeList ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ ranges))

   validRangesComposed : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
            → (r1 r2 : Range a) → (ranges : List (Range a))
            → IsTrue (sortedRangeList (r1 ∷ r2 ∷ ranges))
            → IsTrue (validRanges (r1 ∷ r2 ∷ ranges))
            → IsTrue (validRanges ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ ranges))

   rangesLTEQ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b : Boundary a)
                          → (f : Boundary a → Boundary a) → IsTrue (f b > b) → IsTrue (b <= f b)

   stupid1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b b1 : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a)) 
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → (cond : Bool) -- this condition is (validFunction2 b1 f) && (validFunction b1 g)
                          → IsTrue cond
                          → IsTrue (validFunction2 b1 f)
   stupid2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b b1 : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a))
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → (cond : Bool) -- this condition is (validFunction2 b1 f) && (validFunction b1 g)
                          → IsTrue cond
                          → IsTrue (validFunction b1 g)

   -- used only when h <= h3
   okSorted : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (h h3 : Range a)
         → sortedRangeList (h ∷ h3 ∷ []) ≡ true

   -- holds only when upper h <= lower(head ms)
   validList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (h : Range a) → (ms : List (Range a))
         → IsTrue (validRangeList ms)
         → validRangeList (h ∷ ms) ≡ true

   validIsSorted :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ms : List (Range a))
                     → IsTrue (validRangeList ms) → IsTrue (sortedRangeList ms)

   -- holds only when h < (head ms)
   validSortedList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (h : Range a) → (ms : List (Range a))
         → IsTrue (sortedRangeList ms)
         → sortedRangeList (h ∷ ms) ≡ true



normalise (r1 ∷ r2 ∷ rs) ⦃ prf ⦄ ⦃ prf2 ⦄ = 
   if_then_else_ (overlap1 r1 r2) 
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) 
      ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄ ) 
         (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄ ))
normalise rs = rs
{-# COMPILE AGDA2HS normalise #-}

subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

-- some useful proofs
headandtail : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
      → ⦃ ne : NonEmpty (rSetRanges rs) ⦄ → (IsTrue (validRangeList (rSetRanges rs))) 
      → (IsTrue (validRangeList (tail (rSetRanges rs) ⦃ ne ⦄)))   
okAdjValid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) → (r : Range a)
      → ⦃ ne : NonEmpty rs ⦄ → (IsTrue (validRangeList (r ∷ rs))) → IsTrue (okAdjacent r (head rs ⦃ ne ⦄))            
headandtail2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      → ⦃ ne : NonEmpty rs ⦄ → (IsTrue (validRangeList rs)) 
      → (IsTrue (validRangeList (tail rs ⦃ ne ⦄)))      
tailandhead : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
      → ⦃ ne : NonEmpty (rSetRanges rs) ⦄ → (IsTrue (validRangeList (rSetRanges rs))) 
      → (IsTrue (validRangeList ((head (rSetRanges rs) ⦃ ne ⦄) ∷ [])))
tailandhead2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : List (Range a)) 
      → ⦃ ne : NonEmpty rs ⦄ → (IsTrue (validRangeList rs)) 
      → (IsTrue (validRangeList ((head rs ⦃ ne ⦄) ∷ [])))      
BoundaryBelowAllSmaller :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a)
      → (BoundaryBelowAll <= b) ≡ true

okAdjIsTrue :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) → (r2 : Range a)
               → okAdjacent r r2 ≡ ((rangeLower r <= rangeUpper r) && (rangeUpper r <= rangeLower r2) && (rangeLower r2 <= rangeUpper r2))


normalisedSortedList0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
         → (ms : List (Range a))
         → (prf : IsTrue (sortedRangeList ms)) 
         → (prf2 : IsTrue (validRanges ms))
         → validRangeList (normalise ms ⦃ prf ⦄ ⦃ prf2 ⦄) ≡ true 

normalisedSortedList00 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
         → (rs : List (Range a))
         → (r1 r2 : Range a) → (prf : IsTrue (sortedRangeList (r1 ∷ r2 ∷ rs))) → (prf2 : IsTrue (validRanges (r1 ∷ r2 ∷ rs)))
         → (b : Bool)
         → validRangeList (if_then_else_ b
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄) 
         (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄))) ≡ true 

normalisedSortedList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
  → (ms : List (Range a))
  → (prf : IsTrue (sortedRangeList ms)) 
  → (prf2 : IsTrue (validRanges ms))
  → IsTrue (validRangeList (normalise ms ⦃ prf ⦄ ⦃ prf2 ⦄))

merge1HasValidRanges0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (rs1 rs2 : RSet a)
                          → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
                          → (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2))) ≡ true 

merge1HasValidRanges00 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (rs1 rs2 : RSet a) → (h1 h2 : Range a)
                          → IsTrue (validRangeList (h1 ∷ (rSetRanges rs1))) → IsTrue (validRangeList (h2 ∷ (rSetRanges rs2)))
                          → (b : Bool)
                          → validRanges (if_then_else_ b 
                          (h1 ∷ (merge1 (rSetRanges rs1) (h2 ∷ (rSetRanges rs2)))) 
                          (h2 ∷ (merge1 (h1 ∷ (rSetRanges rs1)) (rSetRanges rs2)))) ≡ true 

validListMeansValidRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (rs1 : RSet a)
                          → IsTrue (validRangeList (rSetRanges rs1))
                          → (validRanges (rSetRanges rs1)) ≡ true 

merge1HasValidRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
   → (rs1 rs2 : RSet a)
   → IsTrue (validRangeList (rSetRanges rs1)) 
   → IsTrue (validRangeList (rSetRanges rs2))
   → IsTrue (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2))) 

ranges2HasValidRanges0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a))
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → (validRanges (ranges2 b f g)) ≡ true  
ranges2HasValidRanges00 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a))
                          → (mb : Maybe (Boundary a)) 
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → (validRanges ((Rg b (f b)) ∷ (ranges3 mb f g))) ≡ true  
ranges2HasValidRanges000 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b b1 : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a))
                          → (cond : Bool) 
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → (validRanges ((Rg b (f b)) ∷ (if cond then (ranges2 b1 f g) else []))) ≡ true 

ranges2HasValidRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
                          → (b : Boundary a)
                          → (f : Boundary a → Boundary a)
                          → (g : Boundary a → Maybe (Boundary a))
                          → IsTrue (validFunction2 b f) → IsTrue (validFunction b g)
                          → IsTrue (validRanges (ranges2 b f g)) 
                       

isTrue&&₁ : {x y : Bool} → IsTrue (x && y) → IsTrue x
isTrue&&₂ : {x y : Bool} → IsTrue (x && y) → IsTrue y

unfoldSorted : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
            → (f : Boundary a → Boundary a) 
            → (g : Boundary a → Maybe (Boundary a))
            → IsTrue (sortedRangeList (ranges2 b f g))

unfoldIsSorted00 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
            → (f : Boundary a → Boundary a) 
            → (g : Boundary a → Maybe (Boundary a))
            → (b1 : Boundary a) → (cond : Bool)
            → sortedRangeList ((Rg b (f b)) ∷ (if_then_else_ cond (ranges2 b1 f g) [])) ≡ true

unfoldIsSorted0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
            → (f : Boundary a → Boundary a) 
            → (g : Boundary a → Maybe (Boundary a))
            → (mb : Maybe (Boundary a)) → sortedRangeList ((Rg b (f b)) ∷ (ranges3 mb f g)) ≡ true

unfoldIsSorted : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
            → (f : Boundary a → Boundary a) 
            → (g : Boundary a → Maybe (Boundary a))
            → sortedRangeList (ranges2 b f g) ≡ true



-- the following proofs are used for proving that intersection is valid
intersection2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                  → ⦃ ne1 : NonEmpty (rSetRanges rs1) ⦄ → ⦃ ne2 : NonEmpty (rSetRanges rs2) ⦄
                  → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
                  → (b : Bool)
                  →     validRangeList (
       if_then_else_ b
      
      ((rangeIntersection (head (rSetRanges rs1) ⦃ ne1 ⦄) (head (rSetRanges rs2) ⦃ ne2 ⦄)) 
      ∷ (filter (λ x → (rangeIsEmpty x == false))
       (if_then_else_ (rangeUpper (head (rSetRanges rs1) ⦃ ne1 ⦄) < rangeUpper (head (rSetRanges rs2) ⦃ ne2 ⦄)) 
        (merge2 (tail (rSetRanges rs1) ⦃ ne1 ⦄) (rSetRanges rs2))
        (merge2 (rSetRanges rs1) (tail (rSetRanges rs2) ⦃ ne2 ⦄))))) 
       
       (filter (λ x → (rangeIsEmpty x == false)) 
         (if_then_else_ (rangeUpper (head (rSetRanges rs1) ⦃ ne1 ⦄) < rangeUpper (head (rSetRanges rs2) ⦃ ne2 ⦄))
          (merge2 (tail (rSetRanges rs1) ⦃ ne1 ⦄) (rSetRanges rs2)) 
          (merge2 (rSetRanges rs1) (tail (rSetRanges rs2) ⦃ ne2 ⦄)))) ) ≡ true
intersection3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                  → ⦃ ne1 : NonEmpty (rSetRanges rs1) ⦄ → ⦃ ne2 : NonEmpty (rSetRanges rs2) ⦄
                  → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
                  → (b : Bool)
                  → validRangeList ((filter (λ x → (rangeIsEmpty x == false)) 
                        (if_then_else_ b
                           (merge2 (tail (rSetRanges rs1) ⦃ ne1 ⦄) (rSetRanges rs2)) 
                           (merge2 (rSetRanges rs1) (tail (rSetRanges rs2) ⦃ ne2 ⦄))))) ≡ true

intersectionHolds : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                  → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
                  → validRangeList (filter (λ x → (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2))) ≡ true


-- intersection of two valid ranged sets is also valid range set
intersection0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
      → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
      → IsTrue (validRangeList (filter (λ x → (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2))))
intersection0 ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 = subst IsTrue (sym (intersectionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2)) IsTrue.itsTrue

-- used for proving that union is valid (merge1 returns a valid range list)
merge1IsSorted0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (h1 h2 : Range a) → (t1 t2 : RSet a) → (b : Bool)
         → IsTrue (validRangeList (h1 ∷ (rSetRanges t1))) → IsTrue (validRangeList (h2 ∷ (rSetRanges t2)))
         → sortedRangeList (if_then_else_ b (h1 ∷ (merge1 (rSetRanges t1) (h2 ∷ (rSetRanges t2)))) 
            (h2 ∷ (merge1 (h1 ∷ (rSetRanges t1)) (rSetRanges t2)))) ≡ true 
merge1IsSorted1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → IsTrue (validRangeList (rSetRanges rs1)) → IsTrue (validRangeList (rSetRanges rs2))
         → sortedRangeList (merge1 (rSetRanges rs1) (rSetRanges rs2)) ≡ true 

merge1Sorted : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
   → (rs1 : RSet a) → (rs2 : RSet a)
   → IsTrue (validRangeList (rSetRanges rs1))
   → IsTrue (validRangeList (rSetRanges rs2))
   → IsTrue (sortedRangeList (merge1 (rSetRanges rs1) (rSetRanges rs2)))

merge1Sorted ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 = subst IsTrue (sym (merge1IsSorted1 rs1 rs2 prf1 prf2)) IsTrue.itsTrue

-- union of two valid ranged sets is also valid range set
unionHolds : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
         → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) 
         → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → IsTrue (validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2))
          ⦃ merge1Sorted rs1 rs2 prf1 prf2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 prf1 prf2 ⦄)) 
unionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 = normalisedSortedList 
   (merge1 (rSetRanges rs1) (rSetRanges rs2)) (merge1Sorted rs1 rs2 prf1 prf2) 
      (merge1HasValidRanges rs1 rs2 prf1 prf2)      

-- used for proving negation is valid
{-# TERMINATING #-}
valid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
   → {IsTrue (validRangeList (rSetRanges rs))}
   → (validRangeList (rSetRanges rs)) ≡ (validBoundaryList (bounds1 (rSetRanges rs)))

validSetBounds : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
   → (bs : List (Boundary a)) → validBoundaryList (setBounds1 bs) ≡ validBoundaryList bs

validRanges1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a))
   → validRangeList (ranges1 bs) ≡ validBoundaryList bs

-- negation of valid ranged set is also valid
prop3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
   → IsTrue (validRangeList (rSetRanges rs)) 
   → validRangeList (rSetRanges rs) ≡ validBoundaryList (setBounds1 (bounds1 (rSetRanges rs)))
prop3 ⦃ o ⦄ ⦃ dio ⦄ rs prf = trans (valid rs {prf}) (sym (validSetBounds (bounds1 (rSetRanges rs))))         

prop4 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
   → IsTrue (validRangeList (rSetRanges rs)) 
   → validRangeList (rSetRanges rs) ≡ validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))

prop4 ⦃ o ⦄ ⦃ dio ⦄ rs prf = trans (prop3 rs prf) (sym (validRanges1 (setBounds1 (bounds1 (rSetRanges rs)))))         

negation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
   → (IsTrue (validRangeList (rSetRanges rs))) 
   → (IsTrue (validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))))
negation ⦃ o ⦄ ⦃ dio ⦄ rs prf = subst IsTrue (prop4 rs prf) prf      

-- empty range is valid
emptyRangeValid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (validRangeList ⦃ o ⦄ ⦃ dio ⦄ []) ≡ true
emptyRangeValid = refl 
empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → IsTrue (validRangeList ⦃ o ⦄ ⦃ dio ⦄ [])
empty ⦃ o ⦄ ⦃ dio ⦄ = subst IsTrue (sym (emptyRangeValid ⦃ o ⦄ ⦃ dio ⦄)) IsTrue.itsTrue

-- full range is valid 
fullRangeValid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → 
      (validRangeList ⦃ o ⦄ ⦃ dio ⦄ (fullRange ⦃ o ⦄ ⦃ dio ⦄ ∷ [])) ≡ true
full0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → 
      IsTrue (validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []))
full0 ⦃ o ⦄ ⦃ dio ⦄ = subst IsTrue (sym (fullRangeValid ⦃ o ⦄ ⦃ dio ⦄)) IsTrue.itsTrue

-- any singleton range is valid
singletonRangeValid0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (x : a) → (validRangeList ((singletonRange x) ∷ [])) ≡ true
singletonRangeValid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (x : a) → IsTrue (validRangeList ((singletonRange x) ∷ [])) 
singletonRangeValid x = subst IsTrue (sym (singletonRangeValid0 x)) IsTrue.itsTrue

rSingleton : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → a → RSet a
rSingleton ⦃ o ⦄ ⦃ dio ⦄ a = RS ((singletonRange a) ∷ []) {singletonRangeValid a}
{-# COMPILE AGDA2HS rSingleton #-}

normaliseRangeList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → List (Range a)
normaliseRangeList [] = []
normaliseRangeList rs@(r1 ∷ rss) = normalise (sort (filter (λ r → (rangeIsEmpty r) == false) rs)) ⦃ sortedList rs ⦄ ⦃ validRangesList rs ⦄
{-# COMPILE AGDA2HS normaliseRangeList #-}

makeRangedSet : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → RSet a
makeRangedSet ⦃ o ⦄ ⦃ dio ⦄ [] = RS [] {empty ⦃ o ⦄ ⦃ dio ⦄}
makeRangedSet ⦃ o ⦄ ⦃ dio ⦄ rs@(r1 ∷ rss) = RS (normaliseRangeList rs) 
   { normalisedSortedList (sort (filter (λ r → (rangeIsEmpty r) == false) rs)) (sortedList rs) (validRangesList rs) }
{-# COMPILE AGDA2HS makeRangedSet #-}

rangesAreEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → Bool
rangesAreEmpty [] = true 
rangesAreEmpty (r ∷ rs) = (rangeIsEmpty r) && (rangesAreEmpty rs)
{-# COMPILE AGDA2HS rangesAreEmpty #-}

rSetIsEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → Bool
rSetIsEmpty ⦃ o ⦄ ⦃ dio ⦄ rset@(RS ranges) = rangesAreEmpty ⦃ o ⦄ ⦃ dio ⦄ ranges
{-# COMPILE AGDA2HS rSetIsEmpty #-}

rSetNegation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rg : RSet a) → {(IsTrue (validRangeList (rSetRanges rg)))} → RSet a
rSetNegation ⦃ o ⦄ ⦃ dio ⦄ set@(RS ranges) {prf} = 
   RS (ranges1 (setBounds1 (bounds1 ranges))) {negation set prf}

{-# COMPILE AGDA2HS rSetNegation #-}

rSetIsFull : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
      → {IsTrue (validRangeList (rSetRanges rs))} → Bool
rSetIsFull set {prf} = rSetIsEmpty (rSetNegation set {prf}) 
{-# COMPILE AGDA2HS rSetIsFull #-}

rSetEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → RSet a
rSetEmpty ⦃ o ⦄ ⦃ dio ⦄ = RS [] {empty ⦃ o ⦄ ⦃ dio ⦄} 
{-# COMPILE AGDA2HS rSetEmpty #-}

rSetFull : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → RSet a
rSetFull ⦃ o ⦄ ⦃ dio ⦄ = RS ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []) {full0 ⦃ o ⦄ ⦃ dio ⦄}
{-# COMPILE AGDA2HS rSetFull #-}

rSetHas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → {IsTrue (validRangeList (rSetRanges rs))} → a → Bool
rSetHas (RS []) _ = false
rSetHas ⦃ o ⦄ ⦃ dio ⦄ (RS ls@(r ∷ [])) value = rangeHas ⦃ o ⦄ r value 
rSetHas ⦃ o ⦄ ⦃ dio ⦄ rst@(RS ls@(r ∷ rs)) {prf} value = (rangeHas ⦃ o ⦄ r value) || (rSetHas (RS rs {headandtail rst prf}) {headandtail rst prf} value)
{-# COMPILE AGDA2HS rSetHas #-}

_-?-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → {IsTrue (validRangeList (rSetRanges rs))} → a → Bool
_-?-_ rs {prf} = rSetHas rs {prf}
{-# COMPILE AGDA2HS _-?-_ #-}

negationHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
         → {tr0 : IsTrue (validRangeList (rSetRanges rs))}
         → validRangeList (rSetRanges (rSetNegation rs {tr0})) ≡ validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))

negation2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
         → {tr0 : IsTrue (validRangeList (rSetRanges rs))}
         → (tr : IsTrue (validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs)))))) 
         → IsTrue (validRangeList (rSetRanges (rSetNegation rs {tr0})))
negation2 rs {prf0} prf = subst IsTrue (sym (negationHelper rs {prf0})) prf


rSetUnion : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
rSetUnion ⦃ o ⦄ ⦃ dio ⦄ r1@(RS ls1) {prf1} r2@(RS ls2) {prf2} = 
   RS (normalise (merge1 ls1 ls2) ⦃ merge1Sorted r1 r2 prf1 prf2 ⦄ 
    ⦃ merge1HasValidRanges r1 r2 prf1 prf2 ⦄)
    {unionHolds r1 r2 prf1 prf2}

{-# COMPILE AGDA2HS rSetUnion #-}

_-\/-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
_-\/-_ rs1 {prf1} rs2 {prf2} = rSetUnion rs1 {prf1} rs2 {prf2}
{-# COMPILE AGDA2HS _-\/-_ #-}

unionHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → validRangeList (rSetRanges (rSetUnion rs1 {prf1} rs2 {prf2})) 
         ≡ validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 prf1 prf2 ⦄ ⦃ merge1HasValidRanges rs1 rs2 prf1 prf2 ⦄)
unionHelper ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1) rs2@(RS ls2) prf1 prf2 =   
  begin 
     validRangeList (rSetRanges (rSetUnion rs1 {prf1} rs2 {prf2})) 
  =⟨⟩ 
     validRangeList (rSetRanges (RS (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 prf1 prf2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 prf1 prf2 ⦄) {unionHolds rs1 rs2 prf1 prf2}))
  =⟨⟩
     validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 prf1 prf2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 prf1 prf2 ⦄)
  end

union2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → IsTrue (validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2)) ⦃ merge1Sorted rs1 rs2 prf1 prf2 ⦄  ⦃ merge1HasValidRanges rs1 rs2 prf1 prf2 ⦄))
         → IsTrue (validRangeList (rSetRanges (rSetUnion rs1 {prf1} rs2 {prf2})))
union2 rs1 rs2 prf1 prf2 prf = subst IsTrue (sym (unionHelper rs1 rs2 prf1 prf2)) prf

rSetIntersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
rSetIntersection ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1) {prf1} rs2@(RS ls2) {prf2} =
    RS ⦃ o ⦄ ⦃ dio ⦄ 
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ls1 ls2)) 
         {intersection0 rs1 rs2 prf1 prf2}
{-# COMPILE AGDA2HS rSetIntersection #-}

_-/\-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
_-/\-_ rs1 {prf1} rs2 {prf2} = rSetIntersection rs1 {prf1} rs2 {prf2}
{-# COMPILE AGDA2HS _-/\-_ #-}


intersectHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → validRangeList (rSetRanges (rSetIntersection rs1 {prf1} rs2 {prf2})) ≡ validRangeList (filter (λ r → (rangeIsEmpty r) == false) (merge2 (rSetRanges rs1) (rSetRanges rs2)))

intersection22 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a)
         → (prf1 : IsTrue (validRangeList (rSetRanges rs1))) → (prf2 : IsTrue (validRangeList (rSetRanges rs2)))
         → IsTrue (validRangeList (filter (λ r → (rangeIsEmpty r) == false) (merge2 (rSetRanges rs1) (rSetRanges rs2))))
         → IsTrue (validRangeList (rSetRanges (rSetIntersection rs1 {prf1} rs2 {prf2})))
intersection22 ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 prf = subst IsTrue (sym (intersectHelper rs1 rs2 prf1 prf2)) prf

rSetDifference : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
rSetDifference ⦃ o ⦄ ⦃ dio ⦄ rs1 {prf1} rs2 {prf2} = 
   rSetIntersection rs1 {prf1} (rSetNegation rs2 {prf2}) {negation2 rs2 (negation rs2 prf2)}
{-# COMPILE AGDA2HS rSetDifference #-}

_-!-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → RSet a
_-!-_ rs1 {prf1} rs2 {prf2} = rSetDifference rs1 {prf1} rs2 {prf2}
{-# COMPILE AGDA2HS _-!-_ #-}

rSetIsSubset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → Bool
rSetIsSubset rs1 {prf1} rs2 {prf2} = rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})
{-# COMPILE AGDA2HS rSetIsSubset #-}

_-<=-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → Bool
_-<=-_ rs1 {prf1} rs2 {prf2}  = rSetIsSubset rs1 {prf1} rs2 {prf2} 
{-# COMPILE AGDA2HS _-<=-_ #-}

rSetIsSubsetStrict : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → Bool
rSetIsSubsetStrict rs1 {prf1} rs2 {prf2} = rSetIsEmpty 
   (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))
{-# COMPILE AGDA2HS rSetIsSubsetStrict #-}

_-<-_ : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
      → (rs1 : RSet a) → {IsTrue (validRangeList (rSetRanges rs1))} 
      → (rs2 : RSet a) → {IsTrue (validRangeList (rSetRanges rs2))} → Bool
_-<-_ rs1 {prf1} rs2 {prf2} = rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}
{-# COMPILE AGDA2HS _-<-_ #-}

instance 
    isRangedSetSemigroup : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Semigroup (RSet a) 
    isRangedSetSemigroup ._<>_ r1@(RS l1 {prf1}) r2@(RS l2 {prf2}) = rSetUnion r1 {prf1} r2 {prf2}

    isRangedSetMonoid : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → Monoid (RSet a)
    isRangedSetMonoid .mempty = rSetEmpty

rSetUnfold : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a) 
            → (f : Boundary a → Boundary a) 
            → (g : Boundary a → Maybe (Boundary a))
            → ⦃ IsTrue (validFunction2 b f) ⦄ 
            → ⦃ IsTrue (validFunction b g) ⦄ → RSet a

rSetUnfold ⦃ o ⦄ ⦃ dio ⦄ bound upperFunc succFunc ⦃ fValid ⦄ ⦃ gValid ⦄ = 
   RS (normalise (ranges2 bound upperFunc succFunc) 
               ⦃ unfoldSorted bound upperFunc succFunc ⦄ ⦃ ranges2HasValidRanges bound upperFunc succFunc fValid gValid ⦄)
      { normalisedSortedList (ranges2 bound upperFunc succFunc) 
               (unfoldSorted bound upperFunc succFunc) (ranges2HasValidRanges bound upperFunc succFunc fValid gValid) }

{-# COMPILE AGDA2HS rSetUnfold #-}

okAdjIsTrue ⦃ o ⦄ ⦃ dio ⦄ r@(Rg l1 u1) r2@(Rg l2 u2) = refl 
-- normaliseValidList ⦃ o ⦄ ⦃ dio ⦄ ranges prf ⦃ prf2 ⦄ = subst IsTrue (sym (normaliseValidList0 ranges prf)) IsTrue.itsTrue

isTrue&&₁ {true} _ = IsTrue.itsTrue
isTrue&&₁ {false} ()

isTrue&&₂ {true} p = p
isTrue&&₂ {false} ()

headandtailSorted rs@(r ∷ []) prf = IsTrue.itsTrue
headandtailSorted rs@(r ∷ rss@(r2 ∷ rsss)) prf = isTrue&&₂ {r <= r2} prf

headandtail rs@(RS (r ∷ [])) prf = IsTrue.itsTrue
headandtail rs@(RS (r ∷ rss@(r2 ∷ rsss))) prf = isTrue&&₂ {okAdjacent r r2} prf

tailandhead rs@(RS (r ∷ [])) prf = prf
tailandhead rs@(RS (r ∷ rss@(r2 ∷ rsss))) prf = isTrue&&₁ {rangeLower r <= rangeUpper r} 
      (subst IsTrue (okAdjIsTrue r r2) (isTrue&&₁ {okAdjacent r r2} prf))

okAdjValid rs@(r2 ∷ rss) r prf = isTrue&&₁ {okAdjacent r r2} prf

tailandhead2 rs@(r ∷ []) prf = prf
tailandhead2 rs@(r ∷ rss@(r2 ∷ rsss)) prf = isTrue&&₁ {rangeLower r <= rangeUpper r} 
      (subst IsTrue (okAdjIsTrue r r2) (isTrue&&₁ {okAdjacent r r2} prf))

headandtail2 rs@(r ∷ []) prf = IsTrue.itsTrue
headandtail2 rs@(r ∷ rss@(r2 ∷ rsss)) prf = isTrue&&₂ {okAdjacent r r2} prf

headandtailValidRanges rs@(r ∷ []) prf = IsTrue.itsTrue
headandtailValidRanges rs@(r ∷ rss@(r2 ∷ rsss)) prf = isTrue&&₂ {rangeLower r <= rangeUpper r} prf

ranges2HasValidRanges ⦃ o ⦄ ⦃ dio ⦄ b f g prf1 prf2 = subst IsTrue (sym (ranges2HasValidRanges0 b f g prf1 prf2)) IsTrue.itsTrue

ranges2HasValidRanges000 ⦃ o ⦄ ⦃ dio ⦄ b b1 f g false prf1 prf2 = 
   begin 
      (validRanges ⦃ o ⦄ ⦃ dio ⦄ ((Rg b (f b)) ∷ []))
  =⟨⟩
      b <= (f b) && (validRanges ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩
      b <= (f b) && true   
  =⟨ prop_and_true (b <= (f b)) ⟩
      b <= (f b)         
  =⟨ propIsTrue (b <= (f b)) (rangesLTEQ b f prf1) ⟩
     true      
   end 
ranges2HasValidRanges000 ⦃ o ⦄ ⦃ dio ⦄ b b1 f g true prf1 prf2 = 
   begin 
      (validRanges ((Rg b (f b)) ∷ (ranges2 b1 f g)))
  =⟨⟩
      b <= (f b) && (validRanges (ranges2 b1 f g))
  =⟨ cong (b <= (f b) &&_) (ranges2HasValidRanges0 b1 f g (stupid1 b b1 f g prf1 prf2 true IsTrue.itsTrue) 
         (stupid2 b b1 f g prf1 prf2 true IsTrue.itsTrue) ) ⟩
      b <= (f b) && true   
  =⟨ prop_and_true (b <= (f b)) ⟩
      b <= (f b)         
  =⟨ propIsTrue (b <= (f b)) (rangesLTEQ b f prf1) ⟩
     true      
   end 


ranges2HasValidRanges00 ⦃ o ⦄ ⦃ dio ⦄ b f g Nothing prf1 prf2 = 
   begin 
      (validRanges ⦃ o ⦄ ⦃ dio ⦄ ((Rg b (f b)) ∷ (ranges3 Nothing f g)))
  =⟨⟩    
      validRanges ⦃ o ⦄ ⦃ dio ⦄ ((Rg b (f b)) ∷ [])
  =⟨⟩
      (b <= (f b)) && (validRanges ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩  
      (b <= (f b)) && true
  =⟨ prop_and_true (b <= (f b)) ⟩    
      b <= (f b)
  =⟨ propIsTrue (b <= (f b)) (rangesLTEQ b f prf1) ⟩
     true      
   end  
ranges2HasValidRanges00 ⦃ o ⦄ ⦃ dio ⦄ b f g (Just b1) prf1 prf2 = 
   begin 
      (validRanges ((Rg b (f b)) ∷ (ranges3 (Just b1) f g)))
  =⟨⟩    
      validRanges ((Rg b (f b)) ∷ (if ((validFunction2 b1 f) && (validFunction b1 g)) then (ranges2 b1 f g) else []))
  =⟨ ranges2HasValidRanges000 b b1 f g ((validFunction2 b1 f) && (validFunction b1 g)) prf1 prf2 ⟩
     true    
   end 

ranges2HasValidRanges0 ⦃ o ⦄ ⦃ dio ⦄ b f g prf1 prf2 = 
   begin 
      (validRanges (ranges2 b f g))
  =⟨⟩    
      validRanges ((Rg b (f b)) ∷ (ranges3 (g b) f g))
  =⟨ ranges2HasValidRanges00 b f g (g b) prf1 prf2 ⟩
      true
   end   

merge1HasValidRanges ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 = subst IsTrue (sym (merge1HasValidRanges0 rs1 rs2 prf1 prf2)) IsTrue.itsTrue

validListMeansValidRanges ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) prf = 
   begin 
      (validRanges ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩ 
  true 
 end 
validListMeansValidRanges ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS (r1 ∷ [])) prf = 
   begin 
      (validRanges (r1 ∷ []))
  =⟨⟩ 
      (rangeLower r1 <= rangeUpper r1) && (validRanges ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩ 
      (rangeLower r1 <= rangeUpper r1) && true
  =⟨ prop_and_true (rangeLower r1 <= rangeUpper r1) ⟩ 
   (rangeLower r1 <= rangeUpper r1)
  =⟨ propIsTrue (rangeLower r1 <= rangeUpper r1) prf ⟩   
  true 
 end 
validListMeansValidRanges ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges@(r1 ∷ r2 ∷ r3)) prf = 
   begin 
      (validRanges ranges)
  =⟨⟩ 
      (rangeLower r1 <= rangeUpper r1) && (validRanges ⦃ o ⦄ ⦃ dio ⦄ (r2 ∷ r3))
  =⟨ cong ((rangeLower r1 <= rangeUpper r1) &&_) (validListMeansValidRanges (RS (r2 ∷ r3) {headandtail rs1 prf}) (headandtail rs1 prf)) ⟩ 
      (rangeLower r1 <= rangeUpper r1) && true
  =⟨ prop_and_true (rangeLower r1 <= rangeUpper r1) ⟩ 
   (rangeLower r1 <= rangeUpper r1)
  =⟨ propIsTrue (rangeLower r1 <= rangeUpper r1) (tailandhead rs1 prf) ⟩   
  true 
 end 


merge1HasValidRanges00 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS t1) rs2@(RS t2) h1 h2 prf1 prf2 true = 
   begin 
      validRanges (h1 ∷ (merge1 (rSetRanges rs1) (h2 ∷ (rSetRanges rs2)))) 
  =⟨⟩ 
      (rangeLower h1 <= rangeUpper h1) && (validRanges (merge1 t1 (h2 ∷ t2)))
  =⟨ cong ((rangeLower h1 <= rangeUpper h1) &&_) 
   (merge1HasValidRanges0 rs1 (RS (h2 ∷ t2) {prf2}) (headandtail (RS (h1 ∷ t1) {prf1}) prf1) prf2) ⟩ 
   (rangeLower h1 <= rangeUpper h1) && true 
  =⟨ prop_and_true (rangeLower h1 <= rangeUpper h1) ⟩ 
   (rangeLower h1 <= rangeUpper h1) 
  =⟨ propIsTrue (rangeLower h1 <= rangeUpper h1) (tailandhead (RS (h1 ∷ t1) {prf1}) prf1) ⟩ 
   true 
 end 
merge1HasValidRanges00 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS t1) rs2@(RS t2) h1 h2 prf1 prf2 false = 
   begin 
      validRanges (h2 ∷ (merge1 (h1 ∷ t1) t2)) 
  =⟨⟩ 
      (rangeLower h2 <= rangeUpper h2) && (validRanges (merge1 (h1 ∷ t1) t2))
  =⟨ cong ((rangeLower h2 <= rangeUpper h2) &&_) 
   (merge1HasValidRanges0 (RS (h1 ∷ t1) {prf1}) rs2 prf1 (headandtail (RS (h2 ∷ t2) {prf2}) prf2)) ⟩ 
   (rangeLower h2 <= rangeUpper h2) && true 
  =⟨ prop_and_true (rangeLower h2 <= rangeUpper h2) ⟩ 
   (rangeLower h2 <= rangeUpper h2) 
  =⟨ propIsTrue (rangeLower h2 <= rangeUpper h2) (tailandhead (RS (h2 ∷ t2) {prf2}) prf2) ⟩ 
   true 
 end 

merge1HasValidRanges0 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) prf1 prf2 =
   begin 
      (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2)))
  =⟨⟩ 
      validRanges ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩ 
  true 
 end 
merge1HasValidRanges0 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS (h1 ∷ t1)) rs2@(RS []) prf1 prf2 =
   begin 
      (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2)))
  =⟨⟩ 
      validRanges (h1 ∷ t1)
  =⟨ validListMeansValidRanges rs1 prf1 ⟩ 
  true 
 end 
merge1HasValidRanges0 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS (h2 ∷ t2)) prf1 prf2 =
   begin 
      (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2)))
  =⟨⟩ 
      validRanges (h2 ∷ t2)
  =⟨ validListMeansValidRanges rs2 prf2 ⟩ 
  true 
 end 
merge1HasValidRanges0 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS (h1 ∷ t1)) rs2@(RS (h2 ∷ t2)) prf1 prf2 =
   begin 
      (validRanges (merge1 (rSetRanges rs1) (rSetRanges rs2)))
  =⟨⟩ 
      validRanges (if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 (h2 ∷ t2))) (h2 ∷ (merge1 (h1 ∷ t1) (t2))))
  =⟨ merge1HasValidRanges00 (RS t1 {headandtail rs1 prf1}) (RS t2 {headandtail rs2 prf2}) h1 h2 prf1 prf2 (h1 < h2) ⟩ 
  true 
 end 

normalisedSortedList ⦃ o ⦄ ⦃ dio ⦄ ms prf prf2 = subst IsTrue (sym (normalisedSortedList0 ms prf prf2)) IsTrue.itsTrue

normalisedSortedList00 ⦃ o ⦄ ⦃ dio ⦄ rs r1 r2 prf prf2 true = 
   begin 
      validRangeList (if_then_else_ true
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄) 
         (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄)))
  =⟨⟩ 
      validRangeList ((normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄) )
  =⟨ normalisedSortedList0 ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) (sortedListComposed r1 r2 rs prf) (validRangesComposed r1 r2 rs prf prf2) ⟩ 
  true 
 end 
normalisedSortedList00 ⦃ o ⦄ ⦃ dio ⦄ rs r1 r2 prf prf2 false = 
   begin 
      validRangeList (if_then_else_ false
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄) 
         (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄)))
  =⟨⟩ 
      validRangeList (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄))
  =⟨ validList r1 (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄) 
  (normalisedSortedList (r2 ∷ rs) (headandtailSorted (r1 ∷ r2 ∷ rs) prf) (headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2))  ⟩ 
  true 
 end 


normalisedSortedList0 ⦃ o ⦄ ⦃ dio ⦄ ms@([]) prf prf2 = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (normalise [] ⦃ prf ⦄ ⦃ prf2 ⦄)
  =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩ 
      true
   end 
normalisedSortedList0 ⦃ o ⦄ ⦃ dio ⦄ ms@(m ∷ []) prf prf2 =       
   begin 
      validRangeList (normalise ms ⦃ prf ⦄ ⦃ prf2 ⦄)
  =⟨⟩
      validRangeList (m ∷ [])   
  =⟨⟩  
      (rangeLower m <= rangeUpper m)
  =⟨ sym (prop_and_true (rangeLower m <= rangeUpper m))  ⟩  
      (rangeLower m <= rangeUpper m) && true
  =⟨⟩  
      (rangeLower m <= rangeUpper m) && (validRanges ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩  
      validRanges ms
  =⟨ propIsTrue (validRanges ms) prf2 ⟩  
      true 
  end    
normalisedSortedList0 ⦃ o ⦄ ⦃ dio ⦄ ms@(r1 ∷ r2 ∷ rs) prf prf2 =       
   begin 
      validRangeList (normalise ms ⦃ prf ⦄ ⦃ prf2 ⦄)
  =⟨⟩
      validRangeList (if_then_else_ (overlap1 r1 r2) 
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs) ⦃ sortedListComposed r1 r2 rs prf ⦄ ⦃ validRangesComposed r1 r2 rs prf prf2 ⦄) 
         (r1 ∷ (normalise (r2 ∷ rs) ⦃ headandtailSorted (r1 ∷ r2 ∷ rs) prf ⦄ ⦃ headandtailValidRanges (r1 ∷ r2 ∷ rs) prf2 ⦄)))   
  =⟨ normalisedSortedList00 rs r1 r2 prf prf2 (overlap1 r1 r2) ⟩    
      true 
  end 

unfoldIsSorted00 ⦃ o ⦄ ⦃ dio ⦄ b f g b1 false = 
     begin 
      sortedRangeList ((Rg b (f b)) ∷ (if_then_else_ false (ranges2 b1 f g) []))
  =⟨⟩ 
      sortedRangeList ((Rg b (f b)) ∷ []) 
  =⟨⟩ 
   true 
   end           
unfoldIsSorted00 ⦃ o ⦄ ⦃ dio ⦄ b f g b1 true = 
     begin 
      sortedRangeList ((Rg b (f b)) ∷ (if_then_else_ true (ranges2 b1 f g) []))
  =⟨⟩ 
      sortedRangeList ((Rg b (f b)) ∷ (ranges2 b1 f g)) 
  =⟨ validSortedList (Rg b (f b)) (ranges2 b1 f g) (unfoldSorted b1 f g) ⟩ 
   true 
   end
   
unfoldIsSorted0 ⦃ o ⦄ ⦃ dio ⦄ b f g Nothing = 
     begin 
      sortedRangeList ((Rg b (f b)) ∷ (ranges3 Nothing f g))
  =⟨⟩ 
      sortedRangeList ((Rg b (f b)) ∷ []) 
  =⟨⟩ 
   true 
   end           
unfoldIsSorted0 ⦃ o ⦄ ⦃ dio ⦄ b f g mb@(Just b1) = 
     begin 
      sortedRangeList ((Rg b (f b)) ∷ (ranges3 mb f g))
  =⟨⟩ 
      sortedRangeList ((Rg b (f b)) ∷ (if_then_else_ ((validFunction2 b1 f) && (validFunction b1 g)) (ranges2 b1 f g) [])) 
  =⟨ unfoldIsSorted00 b f g b1 ((validFunction2 b1 f) && (validFunction b1 g)) ⟩ 
   true 
   end  

unfoldIsSorted ⦃ o ⦄ ⦃ dio ⦄ b f g = 
   begin 
      sortedRangeList (ranges2 b f g)
  =⟨⟩ 
      sortedRangeList ((Rg b (f b)) ∷ (ranges3 (g b) f g)) 
  =⟨ unfoldIsSorted0 b f g (g b) ⟩  
   true 
   end

unfoldSorted ⦃ o ⦄ ⦃ dio ⦄ b f g = subst IsTrue (sym (unfoldIsSorted b f g)) IsTrue.itsTrue

merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS []) rs2@(RS []) true prf1 prf2 = 
   begin 
      sortedRangeList (h1 ∷ (merge1 [] (h2 ∷ [])))
  =⟨⟩  
      sortedRangeList (h1 ∷ h2 ∷ [])   
  =⟨ okSorted h1 h2 ⟩ 
      true
   end
merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS []) rs2@(RS t2@(h4 ∷ tt2)) true prf1 prf2 = 
   begin 
      sortedRangeList (h1 ∷ (merge1 [] (h2 ∷ t2)))
  =⟨⟩  
      sortedRangeList (h1 ∷ (h2 ∷ t2))   
  =⟨ validSortedList h1 (h2 ∷ t2) (validIsSorted (h2 ∷ t2) prf2) ⟩ 
      true
   end     
merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS t1@(h3 ∷ tt1)) rs2@(RS t2) true prf1 prf2 = 
   begin 
      sortedRangeList (h1 ∷ (merge1 t1 (h2 ∷ t2)))
  =⟨ validSortedList h1 (merge1 t1 (h2 ∷ t2)) (merge1Sorted rs1 (RS (h2 ∷ t2) {prf2}) (headandtail (RS (h1 ∷ t1) {prf1}) prf1) prf2) ⟩ 
      true
   end        
merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS []) rs2@(RS []) false prf1 prf2 = 
   begin 
      sortedRangeList (h2 ∷ (merge1 (h1 ∷ []) []))
  =⟨⟩  
      sortedRangeList (h2 ∷ h1 ∷ [])   
  =⟨ okSorted h2 h1 ⟩ 
      true
   end
merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS t1@(h3 ∷ tt1)) rs2@(RS []) false prf1 prf2 = 
   begin 
      sortedRangeList (h2 ∷ (merge1 (h1 ∷ t1) []))
  =⟨⟩  
      sortedRangeList (h2 ∷ h1 ∷ t1)   
  =⟨ validSortedList h2 (h1 ∷ t1) (validIsSorted (h1 ∷ t1) prf1) ⟩ 
      true
   end
merge1IsSorted0 ⦃ o ⦄ ⦃ dio ⦄ h1 h2 rs1@(RS t1) rs2@(RS t2@(h4 ∷ tt2)) false prf1 prf2 = 
   begin 
      sortedRangeList (h2 ∷ (merge1 (h1 ∷ t1) t2))
  =⟨ validSortedList h2 (merge1 (h1 ∷ t1) t2) (merge1Sorted (RS (h1 ∷ t1) {prf1}) rs2 prf1 (headandtail (RS (h2 ∷ t2) {prf2}) prf2)) ⟩ 
      true
   end

merge1IsSorted1 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) prf1 prf2 = refl
merge1IsSorted1 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ms1@(h1 ∷ t1)) rs2@(RS []) prf1 prf2 = propIsTrue (sortedRangeList (merge1 (rSetRanges rs1) (rSetRanges rs2))) (validIsSorted (merge1 (rSetRanges rs1) (rSetRanges rs2)) prf1)
merge1IsSorted1 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS ms1@(h1 ∷ t1)) prf1 prf2 = propIsTrue (sortedRangeList (merge1 (rSetRanges rs1) (rSetRanges rs2))) (validIsSorted (merge1 (rSetRanges rs1) (rSetRanges rs2)) prf2)
merge1IsSorted1 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ms1@(h1 ∷ t1)) rs2@(RS ms2@(h2 ∷ t2)) prf1 prf2 = 
   begin 
      sortedRangeList (merge1 (rSetRanges rs1) (rSetRanges rs2))
  =⟨⟩  
      sortedRangeList (if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2)))     
  =⟨ merge1IsSorted0 h1 h2 (RS t1 {headandtail rs1 prf1}) (RS t2 {headandtail rs2 prf2}) (h1 < h2) prf1 prf2 ⟩ 
      true
   end

singletonRangeValid0 ⦃ o ⦄ ⦃ dio ⦄ x = 
  begin 
   validRangeList ((singletonRange x) ∷ [])
  =⟨⟩ 
    ((rangeLower (singletonRange x)) <= (rangeUpper (singletonRange x))) 
  =⟨⟩
    ((rangeLower (Rg (BoundaryBelow x) (BoundaryAbove x))) <= (rangeUpper (Rg (BoundaryBelow x) (BoundaryAbove x)))) 
  =⟨⟩
    (BoundaryBelow x <= BoundaryAbove x) 
  =⟨⟩  
    ((compare (BoundaryBelow x) (BoundaryAbove x) == LT) || (compare (BoundaryBelow x) (BoundaryAbove x) == EQ))
  =⟨⟩   
    (((if_then_else_ (x > x) (if_then_else_ (adjacent x x) EQ GT) LT) == LT) || (compare (BoundaryBelow x) (BoundaryAbove x) == EQ))
  =⟨ cong (_|| (compare (BoundaryBelow x) (BoundaryAbove x) == EQ)) (cong (_== LT) (propIf3 (x > x) (lt x x refl))) ⟩       
    ((LT == LT) || (compare (BoundaryBelow x) (BoundaryAbove x) == EQ))
  =⟨⟩  
    (true || (compare (BoundaryBelow x) (BoundaryAbove x) == EQ))
  =⟨⟩  
    true
  end  

intersectHelper ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1) rs2@(RS ls2) prf1 prf2 =   
  begin 
     validRangeList (rSetRanges (rSetIntersection rs1 {prf1} rs2 {prf2})) 
  =⟨⟩ 
     validRangeList (rSetRanges (RS (filter (λ r → (rangeIsEmpty r) == false) (merge2 (rSetRanges rs1) (rSetRanges rs2))) {intersection0 rs1 rs2 prf1 prf2}))
  =⟨⟩
     validRangeList (filter (λ r → (rangeIsEmpty r) == false) (merge2 (rSetRanges rs1) (rSetRanges rs2)))
  end

negationHelper ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges) {prf} =   
  begin 
     validRangeList (rSetRanges (rSetNegation rs {prf})) 
  =⟨⟩ 
     validRangeList (rSetRanges (RS ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))) {negation rs prf}))
  =⟨⟩
    validRangeList (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)))
  =⟨⟩  
    validRangeList (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs))))
  end  

fullRangeValid ⦃ o ⦄ ⦃ dio ⦄ = 
  begin 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (fullRange ⦃ o ⦄ ⦃ dio ⦄ ∷ [])
  =⟨⟩ 
    ((rangeLower (fullRange ⦃ o ⦄ ⦃ dio ⦄)) <= (rangeUpper (fullRange ⦃ o ⦄ ⦃ dio ⦄))) 
  =⟨⟩  
    true
  end  

intersection3 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 true = 
  begin
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) 
         (if_then_else_ true 
            (merge2 rss1 ranges2) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ranges1 rss2)))
   =⟨⟩
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) (merge2 rss1 ranges2))
   =⟨ intersectionHolds
 ⦃ o ⦄ ⦃ dio ⦄ (RS rss1 {headandtail rs1 ⦃ NonEmpty.itsNonEmpty ⦄ prf1}) rs2 (headandtail ⦃ o ⦄ ⦃ dio ⦄ rs1 ⦃ ne1 ⦄ prf1) prf2 ⟩
      true 
   end
intersection3 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 false = 
  begin
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) 
         (if_then_else_ false 
            (merge2 ⦃ o ⦄ ⦃ dio ⦄ rss1 ranges2) (merge2 ranges1 rss2)))
   =⟨⟩
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) (merge2 ranges1 rss2))
   =⟨ intersectionHolds
 ⦃ o ⦄ ⦃ dio ⦄ rs1 (RS rss2 {headandtail rs2 ⦃ NonEmpty.itsNonEmpty ⦄ prf2}) prf1 (headandtail ⦃ o ⦄ ⦃ dio ⦄ rs2 ⦃ ne2 ⦄ prf2) ⟩
      true 
   end


intersection2 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 false = 
  begin
        validRangeList (
       if_then_else_ false
      
      ((rangeIntersection ⦃ o ⦄ ⦃ dio ⦄ r1 r2) ∷ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
       (if_then_else_ ((rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1) < (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2)) 
       (merge2 ⦃ o ⦄ ⦃ dio ⦄ rss1 ranges2) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ranges1 rss2)))) 
       
       (filter (λ x → (rangeIsEmpty x == false)) 
         (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
         (merge2 rss1 ranges2) (merge2 ranges1 rss2)))
      ) 
   =⟨⟩
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) 
    (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
    (merge2 rss1 ranges2) (merge2 ranges1 rss2)))
   =⟨ intersection3 ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) ⟩      
    true    
   end
intersection2 ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 true = 
  begin
        validRangeList (
       if_then_else_ true
      
      ((rangeIntersection ⦃ o ⦄ ⦃ dio ⦄ r1 r2) ∷ (filter (λ x → (rangeIsEmpty x == false))
       (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
       (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
       
       (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) 
         (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
         (merge2 ⦃ o ⦄ ⦃ dio ⦄ rss1 ranges2) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ranges1 rss2)))
      ) 
   =⟨⟩
    validRangeList ((rangeIntersection ⦃ o ⦄ ⦃ dio ⦄ r1 r2) ∷ (filter (λ x → (rangeIsEmpty x == false))
       (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
       (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
   =⟨ validList (rangeIntersection ⦃ o ⦄ ⦃ dio ⦄ r1 r2) (filter (λ x → (rangeIsEmpty x == false))
       (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) 
       (merge2 rss1 ranges2) (merge2 ranges1 rss2))) 
       (subst IsTrue (sym 
       (intersection3 ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 ⦃ ne1 ⦄ ⦃ ne2 ⦄ prf1 prf2 (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2))) 
       IsTrue.itsTrue) ⟩      
    true    
   end
 


intersectionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) _ _ =                  
   begin
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs1) (rSetRanges rs2)))
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ [] [])) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) []) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
   =⟨⟩
    true    
   end   
intersectionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges@(r ∷ rs)) rs2@(RS []) _ _ =                  
   begin
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs1) (rSetRanges rs2)))
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ranges [])) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) []) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
   =⟨⟩
    true    
   end

intersectionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS ranges@(r ∷ rs)) _ _ =                  
   begin
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs1) (rSetRanges rs2)))
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (merge2 ⦃ o ⦄ ⦃ dio ⦄ [] ranges)) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (filter (λ x → (rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) []) 
   =⟨⟩
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
   =⟨⟩
    true    
   end

intersectionHolds ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) prf1 prf2 =                  
   begin
    validRangeList (filter (λ x → (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2)))
   =⟨⟩
    validRangeList (filter (λ x → (rangeIsEmpty x == false))  
      ((rangeIntersection r1 r2) ∷ (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
   =⟨⟩
    validRangeList (
       if_then_else_ (rangeIsEmpty (rangeIntersection r1 r2) == false)
      
      ((rangeIntersection r1 r2) ∷ (filter (λ x → (rangeIsEmpty x == false))
       (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
       
       (filter (λ x → (rangeIsEmpty x == false)) 
         (if_then_else_ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r1 < rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))
      ) 
   =⟨ intersection2 ⦃ o ⦄ ⦃ dio ⦄ rs1 rs2 prf1 prf2 (rangeIsEmpty (rangeIntersection r1 r2) == false) ⟩
     true    
   end

   
BoundaryBelowAllSmaller BoundaryBelowAll = refl
BoundaryBelowAllSmaller BoundaryAboveAll = refl
BoundaryBelowAllSmaller (BoundaryBelow _) = refl
BoundaryBelowAllSmaller (BoundaryAbove _)  = refl


validRanges1 ⦃ o ⦄ ⦃ dio ⦄ [] = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 [])
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ [] 
   =⟨⟩ 
      true 
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []
   end 
validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (BoundaryAboveAll ∷ []) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (BoundaryAboveAll  ∷ []))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ [] 
   =⟨⟩ 
      true 
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (BoundaryAboveAll ∷ [])
   end  
validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (BoundaryBelowAll ∷ []) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (BoundaryBelowAll ∷ []))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (BoundaryBelowAll ∷ [])
   end     
validRanges1 ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryAbove x) ∷ []) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryAbove x) ∷ []))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg (BoundaryAbove x) BoundaryAboveAll) ∷ [])
   =⟨⟩ 
      (BoundaryAbove x) <= BoundaryAboveAll 
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryAbove x) ∷ [])
   end     
validRanges1 ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryBelow x) ∷ []) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryBelow x) ∷ []))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg (BoundaryBelow x) (BoundaryAboveAll)) ∷ [])
   =⟨⟩ 
      (BoundaryBelow x) <= BoundaryAboveAll
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ ((BoundaryBelow x) ∷ [])
   end   

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ []) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ []))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ ranges1([]))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ [])      
   =⟨⟩ 
      (b1 <= b2)  
   =⟨ sym (prop_and_true (b1 <= b2)) ⟩ 
      ((b1 <= b2) && true)        
   =⟨⟩ 
      ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []))        
   =⟨⟩    
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ [])
   end   

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs@(b3@(BoundaryBelow x) ∷ [])) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && (validRangeList ⦃ o ⦄ ⦃ dio ⦄ []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs)
   end   

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs@(b3@(BoundaryAbove x) ∷ [])) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && (validRangeList ⦃ o ⦄ ⦃ dio ⦄ []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs)
   end 

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs@(b3@(BoundaryBelowAll) ∷ [])) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && (validRangeList ⦃ o ⦄ ⦃ dio ⦄ []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= (BoundaryAboveAll))) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= (BoundaryAboveAll))) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs)
   end 

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs@(b3@(BoundaryAboveAll) ∷ [])) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄  (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄  bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄  ((Rg b1 b2) ∷ [])      
   =⟨⟩ 
      (b1 <= b2)
   =⟨ sym (prop_and_true (b1 <= b2)) ⟩ 
      ((b1 <= b2) && true)
   =⟨⟩ 
      ((b1 <= b2) && (b2 <= b3))                     
   =⟨ sym (prop_and_true ((b1 <= b2) && (b2 <= b3))) ⟩       
      (((b1 <= b2) && (b2 <= b3)) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄  (b3 ∷ [])))        
   =⟨ prop_and_assoc (b1 <= b2) (b2 <= b3) (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄  (b3 ∷ [])) ⟩    
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄  (b3 ∷ []))) 
   =⟨⟩    
      ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ b3 ∷ []))) 
   =⟨⟩    
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs)      
   end 

validRanges1 ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs@(b3 ∷ bss@(b4 ∷ bsss))) = 
   begin 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ (ranges1 ⦃ o ⦄ ⦃ dio ⦄  (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄ ((Rg b1 b2) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄  bs))
   =⟨⟩ 
      validRangeList ⦃ o ⦄ ⦃ dio ⦄  ((Rg b1 b2) ∷ (Rg b3 b4) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bsss))      
   =⟨⟩ 
      (okAdjacent (Rg b1 b2) (Rg b3 b4)) && validRangeList ((Rg b3 b4) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bsss))
   =⟨⟩ 
      (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) && (validRangeList ((Rg b3 b4) ∷ (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bsss))))
   =⟨⟩ 
      (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) && (validRangeList (ranges1 ⦃ o ⦄ ⦃ dio ⦄ bs)))                    
   =⟨ cong (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) &&_) (validRanges1 ⦃ o ⦄ ⦃ dio ⦄ bs) ⟩       
      (((b1 <= b2) && ((b2 <= b3) && (b3 <= b4))) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs))      
   =⟨ prop_and_assoc (b1 <= b2) ((b2 <= b3) && (b3 <= b4)) (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs) ⟩    
      ((b1 <= b2) && (((b2 <= b3) && (b3 <= b4)) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs)))  
   =⟨ cong ((b1 <= b2) &&_) (prop_and_assoc (b2 <= b3) (b3 <= b4) (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs)) ⟩    
      ((b1 <= b2) && ((b2 <= b3) && (b3 <= b4) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs)))  
   =⟨⟩    
      ((b1 <= b2) && ((b2 <= b3) && (b3 <= b4) && (b3 <= b4 && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bss))))  
   =⟨ cong ((b1 <= b2) &&_) (cong (b2 <= b3 &&_) (prop_and_cancel (b3 <= b4))) ⟩   
      ((b1 <= b2) && (b2 <= b3) && (b3 <= b4) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bss))  
   =⟨⟩   
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs))  
   =⟨⟩ 
      ((b1 <= b2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs)))  
   =⟨⟩ 
      validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (b1 ∷ b2 ∷ bs)      
   end 




validSetBounds ⦃ o ⦄ ⦃ dio ⦄ [] = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []
   end           

validSetBounds ⦃ o ⦄ ⦃ dio ⦄ bs@(BoundaryBelowAll ∷ []) = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ bs)
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩ 
   true   
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bs  
   end   

validSetBounds ⦃ o ⦄ ⦃ dio ⦄ bs@(b0@(BoundaryBelowAll) ∷ bss@(b1 ∷ b2)) = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ bs)
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bss
  =⟨⟩ 
    (true && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bss))
  =⟨ cong (_&& (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ bss)) (sym (BoundaryBelowAllSmaller ⦃ o ⦄ ⦃ dio ⦄ b1)) ⟩ 
    ((BoundaryBelowAll <= b1) && (validBoundaryList bss))    
  =⟨⟩ 
    validBoundaryList bs     
  end   

validSetBounds ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryBelow x) ∷ bss) = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ bs)
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end   

validSetBounds ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryAboveAll) ∷ bss) = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ bs)
  =⟨⟩ 
    validBoundaryList (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end  
validSetBounds ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryAbove x) ∷ bss) = 
  begin 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ bs)
  =⟨⟩ 
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end  



valid ⦃ o ⦄ ⦃ dio ⦄ rs@(RS []) {_} = 
  begin 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)
  =⟨⟩ 
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩
    true
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ [])
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs))
  end  
valid ⦃ o ⦄ ⦃ dio ⦄ rs@(RS (r ∷ [])) {_} = 
  begin 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)
  =⟨⟩ 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (r ∷ [])
  =⟨⟩
    ((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r) <= (rangeUpper ⦃ o ⦄ ⦃ dio ⦄  r))
  =⟨ sym (prop_and_true ((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r) <= (rangeUpper ⦃ o ⦄ ⦃ dio ⦄  r))) ⟩
    (((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r) <= (rangeUpper ⦃ o ⦄ ⦃ dio ⦄  r)) && true)    
  =⟨⟩  
    (((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r) <= (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r)) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ []))    
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ ((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r) ∷ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r) ∷ [])
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (r ∷ []))
  =⟨⟩  
    validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs))
  end  

valid ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges@(r@(Rg l1 u1) ∷ r1@(r2@(Rg l2 u2) ∷ rss))) {prf} = 
  begin 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)
  =⟨⟩ 
     validRangeList ⦃ o ⦄ ⦃ dio ⦄ (r ∷ (r2 ∷ rss))
  =⟨⟩ 
     ((okAdjacent r r2) && (validRangeList ⦃ o ⦄ ⦃ dio ⦄ r1))   
  =⟨⟩
    ((l1 <= u1 && (u1 <= l2 && l2 <= u2)) && (validRangeList ⦃ o ⦄ ⦃ dio ⦄ r1))
  =⟨ cong ((l1 <= u1 && u1 <= l2 && l2 <= u2) &&_) (valid ⦃ o ⦄ ⦃ dio ⦄ (RS r1 {headandtail rs prf}) {headandtail rs prf}) ⟩  
     ((l1 <= u1 && (u1 <= l2 && l2 <= u2)) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ r1)))
  =⟨ prop_and_assoc (l1 <= u1) (u1 <= l2 && l2 <= u2) (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ r1)) ⟩  
    (l1 <= u1 && ((u1 <= l2  && l2 <= u2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ r1))))
  =⟨ cong (l1 <= u1 &&_) (prop_and_assoc (u1 <= l2) (l2 <= u2) (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ r1))) ⟩       
    (l1 <= u1 && u1 <= l2  && (l2 <= u2  && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ r1))))
  =⟨⟩       
    (l1 <= u1 && u1 <= l2  && (l2 <= u2  
         && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ ((rangeLower ⦃ o ⦄ ⦃ dio ⦄  r2) ∷ (rangeUpper ⦃ o ⦄ ⦃ dio ⦄  r2) ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss)))))       
  =⟨⟩       
    (l1 <= u1 && u1 <= l2 && l2 <= u2 && l2 <= u2 
         && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ ((rangeUpper ⦃ o ⦄ ⦃ dio ⦄  r2) ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss))))    
  =⟨ cong (l1 <= u1 &&_) (cong (u1 <= l2 &&_) (prop_and_cancel (l2 <= u2))) ⟩       
    (l1 <= u1 && u1 <= l2 && ((l2 <= u2) && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (u2 ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss)))))   
  =⟨⟩       
    (l1 <= u1 && u1 <= l2 && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (l2 ∷ (u2 ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss))))) 
  =⟨⟩       
    (l1 <= u1 && (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (u1 ∷ l2 ∷ u2 ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss)))) 
  =⟨⟩ 
   (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (l1 ∷ u1 ∷ l2 ∷ u2 ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rss)))    
  =⟨⟩ 
   (validBoundaryList ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))                   
  end 

