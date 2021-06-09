module Haskell.RangedSetsProp.RangedSetProperties where

open import Haskell.RangedSetsProp.library
open import Haskell.RangedSetsProp.RangesProperties
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Eq
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Double
open import Haskell.Prim.Foldable

open import Haskell.RangedSets.Boundaries
open import Haskell.RangedSets.Ranges
open import Haskell.RangedSets.RangedSet


prop_empty : ⦃ o : Ord a ⦄ → ⦃ d : DiscreteOrdered a ⦄ → (v : a) 
           → (not (rSetHas rSetEmpty {empty ⦃ o ⦄ ⦃ d ⦄} v)) ≡ true 
prop_empty v = refl

prop_full : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (v : a) → (rSetHas rSetFull {full0 ⦃ o ⦄ ⦃ dio ⦄} v) ≡ true
prop_full v = refl

prop_validNormalised : ⦃ o : Ord a ⦄ → ⦃ d : DiscreteOrdered a ⦄ → (ls : List (Range a)) 
   → (validRangeList (normaliseRangeList ls)) ≡ true
prop_validNormalised ⦃ o ⦄ ⦃ dio ⦄ [] = refl  
prop_validNormalised ⦃ o ⦄ ⦃ dio ⦄ ls@(r1 ∷ rs) = 
  begin 
    (validRangeList (normaliseRangeList ls))
  =⟨⟩  
    (validRangeList (normalise (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) ⦃ sortedList ls ⦄ ⦃ validRangesList ls ⦄))
  =⟨ propIsTrue (validRangeList (normalise (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) ⦃ sortedList ls ⦄ ⦃ validRangesList ls ⦄))
    (normalisedSortedList (sort (filter (λ r → (rangeIsEmpty r) == false) ls)) (sortedList ls) (validRangesList ls)) ⟩ 
    true 
  end

postulate
  rangeSetCreation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    → {prf : IsTrue (validRangeList (rSetRanges rs))} → (RS ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs) {prf}) ≡ rs
  rangesEqiv : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → {rs1 rs2 : RSet a} → rSetRanges rs1 ≡ rSetRanges rs2 → rs1 ≡ rs2
  rangesEqiv2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → {rs1 rs2 : List (Range a)} 
    → (prf1 : IsTrue (sortedRangeList rs1)) → (prf2 : IsTrue (validRanges rs1))
    → (prf3 : IsTrue (sortedRangeList rs2)) → (prf4 : IsTrue (validRanges rs2))
    → rs1 ≡ rs2 → normalise rs1 ⦃ prf1 ⦄ ⦃ prf2 ⦄ ≡ normalise rs2 ⦃ prf3 ⦄ ⦃ prf4 ⦄ 

singletonRangeSetHas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) → (v : a) 
  → {prf : IsTrue (validRangeList (r ∷ []))}
  → (rSetHas (RS (r ∷ []) {prf}) {prf} v) ≡ rangeHas r v
singletonRangeSetHas r v {prf} = 
  begin 
    (rSetHas (RS (r ∷ []) {prf}) {prf} v)
  =⟨⟩  
    rangeHas r v 
  end

rSetHasHelper : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → a → (rs : List (Range a)) → {prf : IsTrue (validRangeList rs)} → Bool
rSetHasHelper ⦃  o  ⦄ ⦃ dio ⦄ value rs {prf} = rSetHas ⦃ o ⦄ ⦃ dio ⦄ (RS rs {prf}) {prf} value

-- rangeHasSym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) → (rs : RSet a) → (v : a) 
--                              → {prf1 : IsTrue (validRangeList (r ∷ (rSetRanges rs)))}
--                              → (rSetHas (RS (r ∷ (rSetRanges rs)) {prf1}) {prf1} v) ≡ 
--                                               ((rangeHas r v) || (rSetHas rs {headandtail (RS (r ∷ (rSetRanges rs)) {prf1}) prf1} v))
-- rangeHasSym ⦃ o ⦄ ⦃ dio ⦄ r rs@(RS []) v {prf1} = 
--   begin 
--     (rSetHas (RS (r ∷ []) {prf1}) {prf1} v)
--   =⟨⟩
--     (rangeHas r v)
--   =⟨ sym (prop_or_false2 (rangeHas r v)) ⟩
--     ((rangeHas r v) || false)
--   =⟨⟩
--     ((rangeHas r v) || (rSetHas (RS [] {empty ⦃ o ⦄ ⦃ dio ⦄}) {empty ⦃ o ⦄ ⦃ dio ⦄} v))    
--   end
-- rangeHasSym ⦃ o ⦄ ⦃ d ⦄ r rs@(RS ranges@(r1 ∷ r2) {prf}) v {prf1} = 
--   begin 
--     ((RS (r ∷ (rSetRanges rs)) {prf1}) -?- v)
--   =⟨⟩
--     ((rangeHas r v) || (rSetHas (RS (rSetRanges rs) {headandtail (RS (r ∷ (rSetRanges rs)) {prf1}) prf1}) v))
--   =⟨ cong ((rangeHas r v) ||_) (cong (rSetHasHelper v) (rangesEqiv refl)) ⟩
--     ((rangeHas r v) || (rSetHas rs v))
--   end


postulate
  -- the following postulates hold when the boundaries are ordered
  emptyIntersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              → IsFalse (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)

  emptyIntersection2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              → IsFalse (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)           
   
  orderedBoundaries2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            → IsFalse (b2 < b1) 
  -- used for easing the proofs, the true value should be IsTrue (b1 <= b2)                       
  orderedBoundaries3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            → IsTrue (b1 < b2)               
         
{-# TERMINATING #-}
lemma0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    → {prf : IsTrue (validRangeList (rSetRanges rs))}
    → (ranges1 (bounds1 (rSetRanges rs))) ≡ (rSetRanges rs)
lemma0 ⦃ o ⦄ ⦃ dio ⦄ rs@(RS []) {_} = 
    begin
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ []))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ [])
    =⟨⟩
      [] 
    =⟨⟩
      rSetRanges rs      
    end
lemma0 ⦃ o ⦄ ⦃ dio ⦄ rs@(RS (r@(Rg l u) ∷ rgs)) {prf} = 
    begin
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (rSetRanges rs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ (r ∷ rgs)))
    =⟨⟩
      (ranges1 ⦃ o ⦄ ⦃ dio ⦄ ((rangeLower ⦃ o ⦄ ⦃ dio ⦄ r) ∷ ((rangeUpper ⦃ o ⦄ ⦃ dio ⦄ r) ∷ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))))
    =⟨⟩
      ((Rg l u) ∷ ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))    
    =⟨⟩
      (r ∷ ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ rgs))
    =⟨ cong (r ∷_) (lemma0 ⦃ o ⦄ ⦃ dio ⦄ (RS rgs {headandtail rs prf}) {headandtail rs prf}) ⟩
      (r ∷ rgs)   
    =⟨⟩
      rSetRanges rs
    end


rangeEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x : Boundary a) → rangeIsEmpty (Rg x x) ≡ true
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll = refl
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ BoundaryAboveAll = refl
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ b@(BoundaryBelow m) =
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 ⦃ o ⦄ refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end
rangeEmpty ⦃ o ⦄ ⦃ dio ⦄ b@(BoundaryAbove m) = 
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 ⦃ o ⦄ refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end





merge2Empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) → ⦃ ne : NonEmpty bs ⦄
          → filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 (tail bs ⦃ ne ⦄)) (ranges1 bs)) ≡ []

merge2Empty2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) → ⦃ ne : NonEmpty bs ⦄
          → filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (tail bs ⦃ ne ⦄))) ≡ []  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end    
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end     
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end        
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ []))  (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 [])) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 (ranges1 bounds) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3' ⦃ o ⦄ {((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))}
        {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))}
      (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2  ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ false (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll))
        ∷ (merge2 ((Rg b1 b2) ∷ []) []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2  (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss) )))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds ⦃ ne ⦄)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 


merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end 
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end  
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []
    =⟨⟩
      []      
    end         
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3' ⦃ o ⦄ {((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))}
        {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))}
      (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end           
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
    
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
       (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []      
    end
merge2Empty ⦃ o ⦄ ⦃ dio ⦄ bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) ⦃ ne ⦄ = 
    begin
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (tail bounds ⦃ ne ⦄)) (ranges1 bounds))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ b2 b3))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ b1 b2 b3) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end         


lemma2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) 
               → (filter (λ x → rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs)))) ≡ []
lemma2 ⦃ o ⦄ ⦃ dio ⦄ [] =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 []) (ranges1 (setBounds1 []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (BoundaryBelowAll ∷ []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(BoundaryBelowAll ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (BoundaryBelowAll ∷ [])))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  (ranges1 [])))
    =⟨⟩
     (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  []))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(BoundaryAboveAll ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)(merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 [] (ranges1 (setBounds1 (BoundaryAboveAll ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryBelow x) ∷ []) = 
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 ((BoundaryBelow x) ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(b@(BoundaryAbove x) ∷ []) =
    begin
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (b ∷ [])))))
    =⟨⟩    
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
        (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryAboveAll) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3' ⦃ o ⦄
        {((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))}
          {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))}
        (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelow x) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryAbove x) ∷ (b ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 ⦃ o ⦄ ⦃ dio ⦄ a b))) ⟩
      
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection ⦃ o ⦄ ⦃ dio ⦄ BoundaryBelowAll a b) ⟩      
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 ⦃ o ⦄ ⦃ dio ⦄ bs ⟩
      []                         
    end   

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b ∷ bs2@(c ∷ bss)) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) (ranges1 (b ∷ bs2)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) ((Rg b c) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (if_then_else_ (b < c) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))) (merge2 (ranges1 bs) (ranges1 bss)))) 
    
    =⟨ cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false))
        (cong ((rangeIntersection (Rg a b) (Rg b c)) ∷_) (propIf2 (b < c) (orderedBoundaries3 ⦃ o ⦄ ⦃ dio ⦄ b c))) ⟩
     
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false)  
       ((rangeIntersection (Rg a b) (Rg b c)) ∷
         (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2)))))  
         (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b c) ⟩   
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ merge2Empty ⦃ o ⦄ ⦃ dio ⦄ (b ∷ bs2) ⟩ 
      []                    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAboveAll) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)(merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) [])
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []      
    =⟨⟩
      []    
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelowAll) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3' ⦃ o ⦄
      {((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))}
      {(filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []) }
      (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAbove x) ∷ []) =
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 ⦃ o ⦄ ⦃ dio ⦄ bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelow x) ∷ []) =
          (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) []))
           (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 ⦃ o ⦄ ⦃ dio ⦄ a b BoundaryAboveAll) ⟩         
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) [])  
    =⟨⟩         
      []       
    end   


merge2' : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) → List (Range a) → List (Range a)
merge2' ms1 ms2 = merge2 ms2 ms1


prop_empty_intersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → 
  rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)}) ≡ true

prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs@(RS ranges) {prf} =
    begin
      rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs {prf} (negation rs prf)})
    =⟨⟩
      rSetIsEmpty (rSetIntersection rs {prf}
       (RS (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))) {negation rs prf}) 
        {negation2 rs {prf} (negation rs prf)} )
    
    =⟨⟩    
      rSetIsEmpty (RS (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) 
        (merge2 ranges (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))))) 
              {intersection0 rs (RS (ranges1 (setBounds1 (bounds1 ranges))) {negation rs prf}) prf (negation rs prf)}) 
    =⟨⟩ 
      rangesAreEmpty (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ranges (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges))))) 
    =⟨ cong rangesAreEmpty (cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) 
              (cong (merge2' (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)))) (sym (lemma0 rs {prf})))) ⟩  
      rangesAreEmpty (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)) 
          (ranges1 ⦃ o ⦄ ⦃ dio ⦄ (setBounds1 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)))))             
    =⟨ cong rangesAreEmpty (lemma2 ⦃ o ⦄ ⦃ dio ⦄ (bounds1 ⦃ o ⦄ ⦃ dio ⦄ ranges)) ⟩ 
     rangesAreEmpty ⦃ o ⦄ ⦃ dio ⦄ []  
    =⟨⟩           
      true
   end  


prop_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubset rs {prf} rs {prf} ≡ true
prop_subset ⦃ o ⦄ ⦃ dio ⦄ rs {prf} = 
   begin
    rSetIsSubset rs {prf} rs {prf}
   =⟨⟩
    rSetIsEmpty (rSetDifference rs {prf} rs {prf})
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})
   =⟨ prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf} ⟩
     true   
   end 

prop_strictSubset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  → {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubsetStrict rs {prf} rs {prf} ≡ false
prop_strictSubset ⦃ o ⦄ ⦃ dio ⦄ rs {prf} = 
   begin
    rSetIsSubsetStrict rs {prf} rs {prf}
   =⟨⟩
    rSetIsEmpty (rSetDifference rs {prf} rs {prf}) && (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)}) 
      && (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))
   =⟨ cong (_&& (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))) (prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf}) ⟩
    true && (not (rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})))
   =⟨⟩
    (not (rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})))
   =⟨ cong not (prop_empty_intersection ⦃ o ⦄ ⦃ dio ⦄ rs {prf}) ⟩  
     not true 
   =⟨⟩    
     false   
   end 

-- prop_union : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
--                         → {prf1 : IsTrue (validRangeList (rSetRanges rs1))} → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
--                         → (v : a) → (rSetHas rs1 {prf1} v || rSetHas rs2 {prf2} v) ≡ 
--                         (rSetHas (rSetUnion rs1 {prf1} rs2 {prf2}) {union2 rs1 rs2 prf1 prf2 (unionn rs1 rs2 prf1 prf2)} v)
-- prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS []) {prf1} {prf2} v = 
--    begin
--     (rSetHas rs1 {prf1} v || rSetHas rs2 {prf2} v)
--    =⟨⟩
--     (false || false)
--    =⟨⟩
--      false
--    =⟨⟩
--      (rSetHas (RS [] {empty ⦃ o ⦄ ⦃ dio ⦄}) {empty ⦃ o ⦄ ⦃ dio ⦄} v) 
--    =⟨⟩
--      (rSetHas (rSetUnion rs1 {prf1} rs2 {prf2}) {unionn rs1 rs2 prf1 prf2} v)     
--    end 
-- prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS []) rs2@(RS rg1@(r1 ∷ rss1)) {prf1} {prf2} v = 
--    begin
--     (rSetHas rs1 {prf1} v || rSetHas rs2 {prf2} v)
--    =⟨⟩
--     (false || rSetHas rs2 {prf2} v)
--    =⟨⟩
--      rSetHas rs2 {prf2} v
--    =⟨⟩
--      (rSetHas (rSetUnion rs1 {prf1} rs2 {prf2}) {unionn rs1 rs2 prf1 prf2} v)  
--    end 
-- prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS rg@(r1 ∷ rss1)) rs2@(RS []) {prf1} {prf2} v = 
--    begin
--     (rSetHas rs1 {prf1} v || rSetHas rs2 {prf2} v)
--    =⟨⟩
--     (rSetHas rs1 {prf1} v || false)
--    =⟨ prop_or_false2 (rSetHas rs1 {prf1} v) ⟩
--      (rSetHas rs1 {prf1} v)
--    =⟨⟩
--      (rSetHas (rSetUnion rs1 {prf1} rs2 {prf2}) {unionn rs1 rs2 prf1 prf2} v)  
--    end    
-- prop_union ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS rg1@(r1 ∷ rss1)) rs2@(RS rg2@(r2 ∷ rss2)) {prf1} {prf2} v = 
--    begin
--     (rSetHas rs1 {prf1} v || rSetHas rs2 {prf2} v)
--    =⟨ cong (_|| (rSetHas rs2 {prf2} v)) (rangeHasSym r1 (RS rss1 {headandtail rs1 prf1}) v {prf1}) ⟩
--     (((rangeHas r1 v) || (rSetHas (RS rss1 {headandtail rs1 prf1}) {headandtail rs1 prf1} v)) || (rSetHas rs2 {prf2} v))
--    =⟨ prop_or_assoc (rangeHas r1 v) (rSetHas (RS rss1 {headandtail rs1 prf1}) {headandtail rs1 prf1} v)  (rSetHas rs2 {prf2} v) ⟩
--      ((rangeHas r1 v) || (rSetHas (RS rss1 {headandtail rs1 prf1}) {headandtail rs1 prf1} v) || (rSetHas rs2 {prf2} v))
--    =⟨ cong ((rangeHas r1 v) ||_) (prop_union (RS rss1) rs2  {headandtail rs1 prf1} {prf2} v) ⟩
--      ((rangeHas r1 v) ||
--       (rSetHas (rSetUnion (RS rss1) {headandtail rs1 prf1} rs2 {prf2})
--        {(union2 (RS rss1) rs2 (headandtail rs1 prf1) prf2 (unionn (RS rss1) rs2 (headandtail rs1 prf1) prf2))} v))
--    =⟨ sym (rangeHasSym r1 (rSetUnion (RS rss1) {headandtail rs1 prf1} rs2 {prf2}) v 
--     {union2 (RS rss1) rs2 (headandtail rs1 prf1) prf2 (unionn (RS rss1) rs2 (headandtail rs1 prf1) prf2)}) ⟩
--      RS (r1 ∷ (rSetRanges ((RS rss1) -\/- rs2))) -?- v
--    =⟨ cong (_-?- v) (cong RS (union0 r1 (RS rss1) rs2)) ⟩       
--      RS (rSetRanges ((RS (r1 ∷ rss1)) -\/- rs2)) -?- v
--    =⟨ cong (_-?- v) (sym (rangeSetCreation ((RS (r1 ∷ rss1)) -\/- rs2))) ⟩
--      (rSetHas (rSetUnion rs1 {prf1} rs2 {prf2}) {union2 rs1 rs2 prf1 prf2 (unionn rs1 rs2 prf1 prf2)} v)   
--    end

-- prop_union_has_sym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
--   → (rs1 : RSet a) → (rs2 : RSet a) → (v : a) 
--   → ((rs1 -\/- rs2) -?- v) ≡ ((rs2 -\/- rs1) -?- v)
-- prop_union_has_sym ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1) rs2@(RS ranges2) v = 
--   begin 
--     ((rs1 -\/- rs2) -?- v) 
--   =⟨ sym (prop_union rs1 rs2 v) ⟩ 
--     ((rs1 -?- v) || (rs2 -?- v))
--   =⟨ prop_or_sym (rs1 -?- v) (rs2 -?- v) ⟩
--     ((rs2 -?- v) || (rs1 -?- v))
--   =⟨ prop_union rs2 rs1 v ⟩
--     ((rs2 -\/- rs1) -?- v) 
--   end  

-- prop_union_same_set : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (v : a) → ((rs1 -\/- rs1) -?- v) ≡ (rs1 -?- v)
-- prop_union_same_set ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ranges1) v = 
--   begin 
--     ((rs1 -\/- rs1) -?- v) 
--   =⟨ sym (prop_union rs1 rs1 v) ⟩ 
--     ((rs1 -?- v) || (rs1 -?- v))
--   =⟨ prop_or_same_value (rs1 -?- v) ⟩
--     (rs1 -?- v) 
--   end  

prop_validNormalisedEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → validRangeList ⦃ o ⦄ ⦃ dio ⦄ (normaliseRangeList ⦃ o ⦄ ⦃ dio ⦄ []) ≡ true
prop_validNormalisedEmpty ⦃ o ⦄ ⦃ dio ⦄ = 
  begin 
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ (normaliseRangeList ⦃ o ⦄ ⦃ dio ⦄ []) 
  =⟨⟩ 
    validRangeList ⦃ o ⦄ ⦃ dio ⦄ []
  =⟨⟩
    true 
  end  



postulate 
  -- these postulates hold when r1 == r2 does not hold, used for easing the proofs for union/intersection commutes
  equalityRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r1 : Range a) → (r2 : Range a)
                  → (r1 < r2) ≡ (not (r2 < r1))                               
  equalityRanges2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r1 : Range a) → (r2 : Range a)
                  → (rangeUpper r1 < rangeUpper r2) ≡ (not (rangeUpper r2 < rangeUpper r1))

prop_sym_merge1' :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
  → ⦃ ne1 : NonEmpty rs1 ⦄ → ⦃ ne2 : NonEmpty rs2 ⦄ → (b : Bool)
  → if_then_else_ b ((head rs1 ⦃ ne1 ⦄) ∷ (merge1 (tail rs1 ⦃ ne1 ⦄) rs2)) ((head rs2 ⦃ ne2 ⦄) ∷ (merge1 rs1 (tail rs2 ⦃ ne2 ⦄))) ≡
      if_then_else_ (not b) ((head rs2 ⦃ ne2 ⦄) ∷ (merge1 (tail rs2 ⦃ ne2 ⦄) rs1)) ((head rs1 ⦃ ne1 ⦄) ∷ (merge1 rs2 (tail rs1 ⦃ ne1 ⦄)))

prop_sym_merge1 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
                  → merge1 rs1 rs2 ≡ merge1 rs2 rs1 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ [] [] = refl 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) [] = refl                 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ [] ms2@(h2 ∷ t2) = refl 
prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
  begin 
    merge1 ms1 ms2 
   =⟨⟩
    if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2)) 
   =⟨ prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1 ms2 (h1 < h2) ⟩
    if_then_else_ (not (h1 < h2)) (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1)) 
   =⟨ cong (ifThenElseHelper (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))) (sym (equalityRanges h2 h1)) ⟩    
    if_then_else_ (h2 < h1) (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1)) 
   =⟨⟩
    merge1 ms2 ms1
  end  


prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) true = 
  begin 
    if_then_else_ true (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
   =⟨⟩
    (h1 ∷ (merge1 t1 ms2)) 
   =⟨ cong (h1 ∷_) (prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ t1 ms2) ⟩
    (h1 ∷ (merge1 ms2 t1))   
   =⟨⟩  
    if_then_else_ false (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))  
  end  
prop_sym_merge1' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) false = 
  begin 
    if_then_else_ false (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
   =⟨⟩
    (h2 ∷ (merge1 ms1 t2)) 
   =⟨ cong (h2 ∷_) (prop_sym_merge1 ⦃ o ⦄ ⦃ dio ⦄ ms1 t2) ⟩
    (h2 ∷ (merge1 t2 ms1))   
   =⟨⟩  
    if_then_else_ true (h2 ∷ (merge1 t2 ms1)) (h1 ∷ (merge1 ms2 t1))  
  end 

prop_sym_sortedRangeList : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
                          → (sortedRangeList (merge1 ls1 ls2)) ≡ (sortedRangeList (merge1 ls2 ls1))
prop_sym_sortedRangeList ⦃  o  ⦄ ⦃  dio  ⦄ ls1 ls2 =  (cong sortedRangeList (prop_sym_merge1 ls1 ls2))

prop_sym_validRanges : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (ls1 ls2 : List (Range a))
                          →  (validRanges (merge1 ls1 ls2)) ≡  (validRanges (merge1 ls2 ls1))
prop_sym_validRanges ⦃  o  ⦄ ⦃  dio  ⦄ ls1 ls2 =  (cong validRanges (prop_sym_merge1 ls1 ls2))

prop_union_commutes : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                      → {prf1 : IsTrue (validRangeList (rSetRanges rs1))} → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
                      → (rSetUnion rs1 {prf1} rs2 {prf2}) ≡ (rSetUnion rs2 {prf2} rs1 {prf1})
prop_union_commutes (RS []) (RS []) = refl
prop_union_commutes (RS ranges@(r ∷ rs)) (RS []) = refl
prop_union_commutes (RS []) (RS ranges@(r ∷ rs)) = refl
prop_union_commutes ⦃ o ⦄ ⦃ dio ⦄ RS1@(RS ls1@(r1 ∷ rs1)) RS2@(RS ls2@(r2 ∷ rs2)) {prf1} {prf2} =
  begin 
    (rSetUnion RS1 {prf1} RS2 {prf2}) 
   =⟨⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ (normalise ⦃ o ⦄ ⦃ dio ⦄ (merge1 ⦃ o ⦄ ⦃ dio ⦄ ls1 ls2) ⦃ merge1Sorted RS1 RS2 prf1 prf2 ⦄ 
    ⦃ merge1HasValidRanges RS1 RS2 prf1 prf2 ⦄) {unionHolds RS1 RS2 prf1 prf2}
   =⟨ rangesEqiv (rangesEqiv2 (merge1Sorted RS1 RS2 prf1 prf2) (merge1HasValidRanges RS1 RS2 prf1 prf2)
     (merge1Sorted RS2 RS1 prf2 prf1) (merge1HasValidRanges RS2 RS1 prf2 prf1) (prop_sym_merge1 ls1 ls2))  ⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ (normalise ⦃ o ⦄ ⦃ dio ⦄ (merge1 ⦃ o ⦄ ⦃ dio ⦄ ls2 ls1) ⦃ merge1Sorted RS2 RS1 prf2 prf1 ⦄ 
    ⦃ merge1HasValidRanges RS2 RS1 prf2 prf1 ⦄) {unionHolds RS2 RS1 prf2 prf1}
  =⟨⟩
   (rSetUnion RS2 {prf2} RS1 {prf1})
     end

prop_sym_merge2 :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
                  → merge2 rs1 rs2 ≡ merge2 rs2 rs1 

prop_sym_merge2' :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : List (Range a)) → (rs2 : List (Range a))
  → ⦃ ne1 : NonEmpty rs1 ⦄ → ⦃ ne2 : NonEmpty rs2 ⦄ → (b : Bool)
  → (if_then_else_ b (merge2 (tail rs1 ⦃ ne1 ⦄) rs2) (merge2 rs1 (tail rs2 ⦃ ne2 ⦄))) ≡
      (if_then_else_ (not b) (merge2 (tail rs2 ⦃ ne2 ⦄) rs1) (merge2 rs2 (tail rs1 ⦃ ne1 ⦄)))
prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) true = 
  begin 
    (if_then_else_ true (merge2 t1 ms2) (merge2 ms1 t2)) 
  =⟨⟩  
   (merge2 t1 ms2)
  =⟨ prop_sym_merge2 t1 ms2 ⟩
   (merge2 ms2 t1)
  =⟨⟩
   if_then_else_ false (merge2 t2 ms1) (merge2 ms2 t1)
  end  
prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) false = 
  begin 
    (if_then_else_ false (merge2 t1 ms2) (merge2 ms1 t2)) 
  =⟨⟩  
   (merge2 ms1 t2)
  =⟨ prop_sym_merge2 ms1 t2 ⟩
   (merge2 t2 ms1)
  =⟨⟩
   if_then_else_ true (merge2 t2 ms1) (merge2 ms2 t1)
     end  

prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ [] [] = refl 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) [] = refl                 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ [] ms2@(h2 ∷ t2) = refl 
prop_sym_merge2 ⦃ o ⦄ ⦃ dio ⦄ ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
  begin 
    merge2 ms1 ms2 
   =⟨⟩
    (rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h1 < rangeUpper h2) (merge2 t1 ms2) (merge2 ms1 t2)) 
   =⟨ cong ((rangeIntersection h1 h2) ∷_) (prop_sym_merge2' ⦃ o ⦄ ⦃ dio ⦄ ms1 ms2 (rangeUpper h1 < rangeUpper h2)) ⟩
    (rangeIntersection h1 h2) ∷ (if_then_else_ (not (rangeUpper h1 < rangeUpper h2)) (merge2 t2 ms1) (merge2 ms2 t1))  
   =⟨ cong ((rangeIntersection h1 h2) ∷_) (cong (ifThenElseHelper (merge2 t2 ms1) (merge2 ms2 t1)) (sym (equalityRanges2 h2 h1))) ⟩    
    ((rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) 
   =⟨ cong (_∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) (prop_intersection_sym h1 h2) ⟩    
    ((rangeIntersection h2 h1) ∷ (if_then_else_ (rangeUpper h2 < rangeUpper h1) (merge2 t2 ms1) (merge2 ms2 t1))) 
   =⟨⟩
    merge2 ms2 ms1
  end 

prop_intersection_commutes : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) 
                      → {prf1 : IsTrue (validRangeList (rSetRanges rs1))} → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
                      → (rSetIntersection rs1 {prf1} rs2 {prf2}) ≡ (rSetIntersection rs2 {prf2} rs1 {prf1})
prop_intersection_commutes (RS []) (RS []) = refl
prop_intersection_commutes (RS ranges@(r ∷ rs)) (RS []) = refl
prop_intersection_commutes (RS []) (RS ranges@(r ∷ rs)) = refl
prop_intersection_commutes ⦃ o ⦄ ⦃ dio ⦄ rs1@(RS ls1@(r1 ∷ rss1)) rs2@(RS ls2@(r2 ∷ rss2)) {prf1} {prf2} =
  begin 
    (rSetIntersection rs1 {prf1} rs2 {prf2}) 
   =⟨⟩
    RS ⦃ o ⦄ ⦃ dio ⦄ 
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ls1 ls2)) 
         {intersection0 rs1 rs2 prf1 prf2}
   =⟨ rangesEqiv (cong (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false)) (prop_sym_merge2 ls1 ls2)) ⟩
     RS ⦃ o ⦄ ⦃ dio ⦄ 
      (filter (λ x → rangeIsEmpty ⦃ o ⦄ ⦃ dio ⦄ x == false) (merge2 ⦃ o ⦄ ⦃ dio ⦄ ls2 ls1)) 
         {intersection0 rs2 rs1 prf2 prf1}
  =⟨⟩
   (rSetIntersection rs2 {prf2} rs1 {prf1})
     end

-- if x is strict subset of y, y is not strict subset of x 
-- prop_subset_not1 asserts that rSetIsSubstrict x y is true 
-- this means that rSetIsEmpty (rSetDifference x y) is true 
-- and rSetEmpty (rSetDifference x y) is false
prop_subset_not1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  -> (a1 : IsTrue (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) 
  -> (a2 : IsTrue (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))
  → (rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}) ≡ (not (rSetIsSubsetStrict rs2 {prf2} rs1 {prf1})) 
prop_subset_not1 {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} a1 a2 = 
  begin 
    rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}
  =⟨⟩
   (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))
  =⟨ not-not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))) ⟩  
    not (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))
  =⟨ cong not (prop_demorgan (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})) (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))) ⟩
    not ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) || (not (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))))
  =⟨ cong not (cong ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) ||_) (sym (not-not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))) ⟩  
    not ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) || (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))
  =⟨ cong not (prop_or_sym (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))) ⟩    
    not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}) || not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
  =⟨ cong not (prop_or_and_eqiv_false (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})) 
    (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
    (isTrueAndIsFalse2 a2)
    (isTrueAndIsFalse1 a1)) ⟩
   not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}) && not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
  =⟨⟩
   not (rSetIsSubsetStrict rs2 {prf2} rs1 {prf1})
 end

-- if x is strict subset of y, y is not strict subset of x 
-- prop_subset_not2 asserts that rSetIsSubstrict x y is false 
-- this means that rSetIsEmpty (rSetDifference x y) is false 
-- and rSetEmpty (rSetDifference x y) is true
prop_subset_not2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  -> (a1 : IsFalse (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) 
  -> (a2 : IsFalse (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))
  → (rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}) ≡ (not (rSetIsSubsetStrict rs2 {prf2} rs1 {prf1})) 
prop_subset_not2 {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} a1 a2 = 
  begin 
    rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}
  =⟨⟩
   (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))
  =⟨ not-not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))) ⟩  
    not (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))
  =⟨ cong not (prop_demorgan (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})) (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))) ⟩
    not ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) || (not (not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))))
  =⟨ cong not (cong ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) ||_) (sym (not-not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))))) ⟩  
    not ((not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) || (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})))
  =⟨ cong not (prop_or_sym (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2}))) (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))) ⟩    
    not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}) || not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
  =⟨ cong not (prop_or_and_eqiv_true (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1})) 
    (not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
    (isTrueAndIsFalse3 a2)
    (isTrueAndIsFalse4 a1)) ⟩
   not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}) && not (rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})))
  =⟨⟩
   not (rSetIsSubsetStrict rs2 {prf2} rs1 {prf1})
 end 

prop_strictSubset_means_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 rs2 : RSet a)
  → {prf1 : IsTrue (validRangeList (rSetRanges rs1))}
  → {prf2 : IsTrue (validRangeList (rSetRanges rs2))} 
  → IsTrue (rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}) -> IsTrue (rSetIsSubset rs1 {prf1} rs2 {prf2})
prop_strictSubset_means_subset {{ o }} {{ dio }} rs1 rs2 {prf1} {prf2} prf = isTrue&&₁ {(rSetIsSubset rs1 {prf1} rs2 {prf2})} prf