module Haskell.RangedSetsProp.RangesProperties where

open import Haskell.RangedSetsProp.library

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (_==_ to eqq; _<_ to ltt)

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Eq

open import Haskell.Prim.Foldable
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Double

open import Haskell.RangedSets.Boundaries
open import Haskell.RangedSets.Ranges
open import Haskell.RangedSetsProp.BoundariesProperties

postulate 
  prop_range_creation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → {r1 r2 : Boundary a} →  
                        {r3 r4 : Boundary a} → (r1 ≡ r3) → (r2 ≡ r4) → (Rg r1 r2) ≡ Rg r3 r4

prop_intersection_sym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r1 : Range a) → (r2 : Range a) → 
                        rangeIntersection r1 r2 ≡ rangeIntersection r2 r1
prop_intersection_sym ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) = 
   begin
      rangeIntersection r1 r2
     =⟨⟩ 
      if_then_else_ (rangeIsEmpty r1 || rangeIsEmpty r2) emptyRange (Rg (max l1 l2) (min u1 u2))
     =⟨ cong (ifThenElseHelper emptyRange (Rg (max l1 l2) (min u1 u2))) (prop_or_sym (rangeIsEmpty r1) (rangeIsEmpty r2)) ⟩
      if_then_else_ (rangeIsEmpty r2 || rangeIsEmpty r1) emptyRange (Rg (max l1 l2) (min u1 u2))
     =⟨ cong (if_then_else_ (rangeIsEmpty r2 || rangeIsEmpty r1) emptyRange) 
     (prop_range_creation (prop_max_sym l1 l2) (prop_min_sym u1 u2))  ⟩
      if_then_else_ (rangeIsEmpty r2 || rangeIsEmpty r1) emptyRange (Rg (max l2 l1) (min u2 u1))
     =⟨⟩
      rangeIntersection r2 r1
   end


prop_singletonRangeHas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x : a) → (rangeHas ⦃ o ⦄ (singletonRange x) x) ≡ true
prop_singletonRangeHas ⦃ o ⦄ ⦃ dio ⦄ x = 
   begin
      (rangeHas (singletonRange x) x)
     =⟨⟩ 
      (rangeHas (Rg (BoundaryBelow x) (BoundaryAbove x)) x)
     =⟨⟩
      ((x />/ (BoundaryBelow x)) && (not (x />/ (BoundaryAbove x))))
     =⟨⟩
      ((x >= x) && (not (x > x)))
     =⟨ cong (_&& (not (x > x))) (gteq ⦃ o ⦄ refl) ⟩
      (true && (not (x > x)))
     =⟨ cong (true &&_) (gt ⦃ o ⦄ refl) ⟩
      (true && true)
     =⟨⟩
      true
   end

prop_singletonRangeHasOnly : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x y : a) → (rangeHas ⦃ o ⦄ (singletonRange x) y) ≡ (x == y)
prop_singletonRangeHasOnly ⦃ o ⦄ ⦃ dio ⦄ v1 v2 =
   begin
      (rangeHas (singletonRange v1) v2)
     =⟨⟩ 
      (rangeHas (Rg (BoundaryBelow v1) (BoundaryAbove v1)) v2)
     =⟨⟩
      ((v2 />/ (BoundaryBelow v1)) && (not (v2 />/ (BoundaryAbove v1))))
     =⟨⟩
      ((v2 >= v1) && (not (v2 > v1)))
     =⟨ eq1 v2 v1 ⟩
      (v1 == v2)
   end

prop_singletonRangeConverse : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x : a) → rangeSingletonValue (singletonRange x) ≡ Just x
prop_singletonRangeConverse ⦃ o ⦄ ⦃ dio ⦄ v =
   begin
      rangeSingletonValue (singletonRange v)
     =⟨⟩ 
      rangeSingletonValue (Rg (BoundaryBelow v) (BoundaryAbove v))
     =⟨⟩
      if_then_else_ (v == v) (Just v) Nothing
     =⟨ propIf2 (v == v) (eq0 ⦃ o ⦄ refl) ⟩
      Just v
   end

prop_emptyNonSingleton : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → rangeSingletonValue ⦃ o ⦄ ⦃ dio ⦄ emptyRange ≡ Nothing
prop_emptyNonSingleton = refl

prop_fullNonSingleton : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → rangeSingletonValue ⦃ o ⦄ ⦃ dio ⦄ fullRange ≡ Nothing
prop_fullNonSingleton = refl

rs : Double → Double → List (Range Double)
rs x y = (Rg (BoundaryBelow x) (BoundaryBelow y)) ∷ (Rg (BoundaryAbove x) (BoundaryBelow y)) ∷ (Rg (BoundaryBelow x) (BoundaryAbove y)) ∷ (Rg (BoundaryAbove x) (BoundaryAbove y)) ∷ []

length' : List a → Nat 
length' [] = 0
length' (x ∷ []) = 1
length' (x ∷ xs) = 1 + (length' xs)

prop_unionRangeLengthHelper3 : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
                 → (r1 r2 : (Range a)) → (b : Bool) 
                 → ((eqq ((length' (if_then_else_ b ((Rg (min (rangeLower r1) (rangeLower r2)) (max (rangeUpper r1) (rangeUpper r2))) ∷ []) (r1 ∷ r2 ∷ [])))) 1) 
                 || (eqq (length' ((if_then_else_ b ((Rg (min (rangeLower r1) (rangeLower r2)) (max (rangeUpper r1) (rangeUpper r2))) ∷ []) (r1 ∷ r2 ∷ [])))) 2)) ≡ true
prop_unionRangeLengthHelper3 ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) true = 
  begin 
    ((eqq (length' ((Rg (min l1 l2) (max u1 u2)) ∷ [])) 1) || (eqq (length' ((Rg (min l1 l2) (max u1 u2)) ∷ [])) 2))
   =⟨⟩
    ((eqq 1 1) || (eqq 1 2))
   =⟨⟩
     (true || false)
   =⟨⟩  
     true
   end 
prop_unionRangeLengthHelper3 ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) false = 
  begin 
    ((eqq (length' (r1 ∷ r2 ∷ [])) 1) || (eqq (length' (r1 ∷ r2 ∷ [])) 2))
   =⟨⟩
    ((eqq 2 1) || (eqq 2 2))  
   =⟨⟩
     (false || true) 
   =⟨⟩  
     true
   end 

prop_unionRangeLengthHelper2 : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
                 → (r1 r2 : (Range a)) → (b : Bool) 
                 → ((eqq (length' (if_then_else_ b (r1 ∷ []) (rangeU2 r1 r2))) 1) || (eqq (length' ((if_then_else_ b (r1 ∷ []) (rangeU2 r1 r2)))) 2)) ≡ true
prop_unionRangeLengthHelper2 ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) true = 
    begin
     ((eqq (length' (r1 ∷ [])) 1) || (eqq (length' (r1 ∷ [])) 2))
   =⟨⟩
    ((eqq 1 1) || (eqq 1 2))  
   =⟨⟩
     (true || false)
   =⟨⟩  
     true
   end 
prop_unionRangeLengthHelper2 ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) false = 
    begin
     ((eqq (length' (rangeU2 r1 r2)) 1) || (eqq (length' (rangeU2 r1 r2)) 2))
   =⟨⟩
     ((eqq (length' (if_then_else_ ((max l1 l2) <= (min u1 u2)) ((Rg (min l1 l2) (max u1 u2)) ∷ []) (r1 ∷ r2 ∷ []))) 1) 
     || (eqq (length' (if_then_else_ ((max l1 l2) <= (min u1 u2)) ((Rg (min l1 l2) (max u1 u2)) ∷ []) (r1 ∷ r2 ∷ []))) 2))
   =⟨ prop_unionRangeLengthHelper3 r1 r2 (((max l1 l2) <= (min u1 u2))) ⟩  
     true
   end 

prop_unionRangeLengthHelper : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
                 → (r1 r2 : (Range a)) → (b : Bool) 
                 → ((eqq (length' (if_then_else_ b (r2 ∷ []) (rangeU1 r1 r2))) 1) || (eqq (length' ((if_then_else_ b (r2 ∷ []) (rangeU1 r1 r2)))) 2)) ≡ true
prop_unionRangeLengthHelper ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) true = 
    begin
     ((eqq (length' (r2 ∷ [])) 1) || (eqq (length' (r2 ∷ [])) 2))
   =⟨⟩
    ((eqq 1 1) || (eqq 1 2))   
   =⟨⟩
     (true || false)
   =⟨⟩  
     true
   end 
prop_unionRangeLengthHelper ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) false = 
    begin
     ((eqq (length' (rangeU1 r1 r2)) 1) || (eqq (length' (rangeU1 r1 r2)) 2))
   =⟨⟩
     ((eqq (length' (if_then_else_ (rangeIsEmpty r2) (r1 ∷ []) (rangeU2 r1 r2))) 1) 
     || (eqq (length' (if_then_else_ (rangeIsEmpty r2) (r1 ∷ []) (rangeU2 r1 r2))) 2))
   =⟨ prop_unionRangeLengthHelper2 r1 r2 (rangeIsEmpty r2) ⟩  
     true
   end 

prop_unionRangeLength : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
                 → (r1 r2 : (Range a)) → ((eqq (length' (rangeUnion r1 r2)) 1) || (eqq (length' (rangeUnion r1 r2)) 2)) ≡ true
prop_unionRangeLength ⦃ o ⦄ ⦃ dio ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) = 
   begin
     ((eqq (length' (rangeUnion r1 r2)) 1) || (eqq (length' (rangeUnion r1 r2)) 2))
   =⟨⟩
     ((eqq (length' (if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (rangeU1 r1 r2))) 1) || (eqq (length' (if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (rangeU1 r1 r2))) 2))
   =⟨ prop_unionRangeLengthHelper r1 r2 (rangeIsEmpty r1) ⟩  
     true
   end


prop_UnionRange1 : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
                 → (r1 r2 : (Range a)) → ⦃ ne1 : IsFalse (rangeIsEmpty r1) ⦄ → ⦃ ne2 : IsFalse (rangeIsEmpty r2) ⦄
                 → ⦃ ne3 : IsFalse ((max (rangeLower r1) (rangeLower r2)) <= (min (rangeUpper r1) (rangeUpper r2))) ⦄ → (n : a) 
                 → (rangeListHas1 n (rangeUnion ⦃ ord ⦄ ⦃ diso ⦄ r1 r2)) ≡ ((rangeHas ⦃ ord ⦄ r1 n) || (rangeHas ⦃ ord ⦄ r2 n)) 
prop_UnionRange1 ⦃ ord ⦄ ⦃ diso ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) ⦃ ne1 ⦄ ⦃ ne2 ⦄ ⦃ ne3 ⦄ n = 
   begin
     (rangeListHas1 n (rangeUnion r1 r2))
   =⟨⟩
     (rangeListHas1 n (if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (rangeU1 r1 r2)))
   =⟨ propIf (rangeListHas1 n) (rangeIsEmpty r1) ⟩
     if_then_else_ (rangeIsEmpty r1) (rangeListHas1 n (r2 ∷ [])) (rangeListHas1 n (rangeU1 r1 r2))
   =⟨ propIf3 (rangeIsEmpty r1) ne1 ⟩
     rangeListHas1 n (rangeU1 r1 r2) 
   =⟨ cong (rangeListHas1 n) (propIf3 (rangeIsEmpty r2) ne2) ⟩
     (rangeListHas1 n (rangeU2 r1 r2))
   =⟨ cong (rangeListHas1 n) (propIf3 ((max l1 l2) <= (min u1 u2)) ne3) ⟩  
     (rangeListHas1 n (r1 ∷ r2 ∷ []))
   =⟨⟩  
     ((rangeHas r1 n) || (rangeHas r2 n))
   end

-- prop_UnionRange1' : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ 
--                  → (r1 r2 : (Range a)) → ⦃ne1 : IsFalse (rangeIsEmpty r1)⦄ → ⦃ne2 : IsFalse (rangeIsEmpty r2)⦄
--                  → ⦃ne3 : IsTrue ((max (rangeLower r1) (rangeLower r2)) <= (min (rangeUpper r1) (rangeUpper r2)))⦄ → (n : a) 
--                  → (rangeListHas1 n (rangeUnion ⦃ord⦄ ⦃diso⦄ r1 r2)) ≡ ((rangeHas ⦃ord⦄ r1 n) || (rangeHas ⦃ord⦄ r2 n)) 
-- prop_UnionRange1' ⦃ord⦄ ⦃diso⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) ⦃ne1⦄ ⦃ne2⦄ ⦃ne3⦄ n = 
--    begin
--      (rangeListHas1 n (rangeUnion r1 r2))
--    =⟨⟩
--      (rangeListHas1 n (if_then_else_ (rangeIsEmpty r1) (r2 ∷ []) (rangeU1 r1 r2)))
--    =⟨ propIf (rangeListHas1 n) (rangeIsEmpty r1) ⟩
--      if_then_else_ (rangeIsEmpty r1) (rangeListHas1 n (r2 ∷ [])) (rangeListHas1 n (rangeU1 r1 r2))
--    =⟨ propIf3 (rangeIsEmpty r1) ne1 ⟩
--      rangeListHas1 n (rangeU1 r1 r2) 
--    =⟨ cong (rangeListHas1 n) (propIf3 (rangeIsEmpty r2) ne2) ⟩
--      (rangeListHas1 n (rangeU2 r1 r2))
--    =⟨ cong (rangeListHas1 n) (propIf2 ((max l1 l2) <= (min u1 u2)) ne3) ⟩  
--      (rangeListHas1 n ((Rg (min l1 l2) (max u1 u2)) ∷ []))
--    =⟨⟩  
--     ((n />/ (min l1 l2)) && not (n />/ (max u1 u2)))
--    =⟨⟩  
--     ((n />/ (if (compare l1 l2 == LT) then l1 else l2)) && not (n />/ (if (compare u1 u2 == GT) then u1 else u2)))    
--    =⟨⟩  
--      ((rangeHas r1 n) || (rangeHas r2 n))
--    end

prop_emptyRange : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) → not (rangeIsEmpty r) ≡ (rangeLower r <= rangeUpper r)
prop_emptyRange ⦃ o ⦄ ⦃ dio ⦄ r@(Rg l u) = 
  begin 
    not (rangeIsEmpty r) 
  =⟨⟩ 
    not (u <= l)
  =⟨ eq2 u l ⟩
    l < u
  =⟨ lteq l u ⟩
    l <= u
  end 

prop_rangeHas : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ → {r : (Range a)} → {n : a} 
                        → (rangeHas1 ⦃ ord ⦄ n r) ≡ (rangeHas ⦃ ord ⦄ r n)
prop_rangeHas {r = (Rg x y)} {n} = 
   begin
     rangeHas1 n (Rg x y)
   =⟨⟩
     (n />/ x) && (not (n />/ y))
   =⟨⟩
     rangeHas (Rg x y) n  
   end

prop_IntersectionRange : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ → (r1 r2 : (Range a)) 
                        → ⦃ ff : IsFalse (rangeIsEmpty r1 || rangeIsEmpty r2) ⦄  → (n : a) 
                        → ((rangeHas r1 n) && (rangeHas r2 n)) ≡ (rangeHas (rangeIntersection r1 r2) n)

prop_IntersectionRange ⦃ ord ⦄ ⦃ diso ⦄ r1@(Rg x1 y1) r2@(Rg x2 y2) ⦃ ff ⦄ n = 
   begin
     ((rangeHas r1 n) && (rangeHas r2 n))
   =⟨⟩
     ((n />/ x1) && (not (n />/ y1))) && ((n />/ x2) && (not (n />/ y2)))
   =⟨ prop_and_assoc (n />/ x1) (not (n />/ y1)) (n />/ x2 && (not (n />/ y2))) ⟩
     ((n />/ x1) && ((not (n />/ y1)) && ((n />/ x2) && (not (n />/ y2)))))
   =⟨ cong ((n />/ x1) &&_) (sym (prop_and_assoc (not (n />/ y1)) (n />/ x2) (not (n />/ y2)))) ⟩
     ((n />/ x1) && (not (n />/ y1) && (n />/ x2)) && (not (n />/ y2)))
   =⟨ sym (prop_and_assoc (n />/ x1) (not (n />/ y1) && (n />/ x2)) (not (n />/ y2))) ⟩
     (((n />/ x1) && (not (n />/ y1) && (n />/ x2))) && (not (n />/ y2)))
   =⟨ cong (_&& (not (n />/ y2))) (cong ((n />/ x1) &&_) (prop_and_comm (not (n />/ y1)) (n />/ x2))) ⟩
     (((n />/ x1) && ((n />/ x2) && not (n />/ y1))) && (not (n />/ y2)))
   =⟨ cong (_&& (not (n />/ y2))) (sym (prop_and_assoc (n />/ x1) (n />/ x2) (not (n />/ y1)))) ⟩
     ((((n />/ x1) && (n />/ x2)) && not (n />/ y1)) && (not (n />/ y2)))
   =⟨ prop_and_assoc ((n />/ x1) && (n />/ x2)) (not (n />/ y1)) (not (n />/ y2)) ⟩
     (((n />/ x1) && (n />/ x2)) && (not (n />/ y1) && (not (n />/ y2))))
   =⟨ cong ((n />/ x1 && n />/ x2) &&_) (prop_demorgan2 (n />/ y1) (n />/ y2)) ⟩
     (n />/ x1 && n />/ x2) && (not ((n />/ y1) || (n />/ y2)))
   =⟨ cong (_&& (not ((n />/ y1) || (n />/ y2)))) (boundaries0 n x1 x2) ⟩
     (n />/ (max x1 x2)) && (not ((n />/ y1) || (n />/ y2)))
   =⟨ cong ((n />/ (max x1 x2)) &&_) (cong not (boundaries1 n y1 y2)) ⟩ 
     (n />/ (max x1 x2)) && not (n />/ (min y1 y2))
   =⟨⟩
     rangeHas (Rg (max (rangeLower r1) (rangeLower r2)) (min (rangeUpper r1) (rangeUpper r2))) n 
   =⟨ sym (cong (rangeHas1 n) (propIf3 (rangeIsEmpty r1 || rangeIsEmpty r2) ff)) ⟩
     rangeHas1 n (rangeIntersection r1 r2)
   =⟨ prop_rangeHas ⦃ ord ⦄ ⦃ diso ⦄ {(rangeIntersection r1 r2)} ⟩
     rangeHas (rangeIntersection r1 r2) n
   end


prop_notEmptyRanges : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ → (r1 r2 : (Range a)) 
                    → (not ((rangeIsEmpty r1) || (rangeIsEmpty r2))) ≡ (((rangeLower r1) < (rangeUpper r1)) && ((rangeLower r2) < (rangeUpper r2)))
prop_notEmptyRanges ⦃ ord ⦄ ⦃ diso ⦄ r1@(Rg l1 u1) r2@(Rg l2 u2) = 
   begin
      not ((rangeIsEmpty r1 )|| (rangeIsEmpty r2))
   =⟨⟩
      (not (((rangeUpper r1) <= (rangeLower r1)) || ((rangeUpper r2) <= (rangeLower r2))))
   =⟨ sym (prop_demorgan2 ((rangeUpper r1) <= (rangeLower r1)) ((rangeUpper r2) <= (rangeLower r2))) ⟩  
      ((not ((rangeUpper r1) <= (rangeLower r1)))) && (not ((rangeUpper r2) <= (rangeLower r2)))   
   =⟨ cong (not ((rangeUpper r1) <= (rangeLower r1)) &&_) (eq2 (rangeUpper r2) (rangeLower r2)) ⟩  
      ((not ((rangeUpper r1) <= (rangeLower r1))) && ((rangeLower r2) < (rangeUpper r2)))   
   =⟨ cong (_&& ((rangeLower r2) < (rangeUpper r2))) (eq2 (rangeUpper r1) (rangeLower r1)) ⟩  
      (((rangeLower r1) < (rangeUpper r1)) && ((rangeLower r2) < (rangeUpper r2)))
    end


prop_intersectionOverlap : ⦃ ord : Ord a ⦄ → ⦃ diso : DiscreteOrdered a ⦄ → (r1 r2 : (Range a)) 
                            → ⦃ ff : IsFalse (rangeIsEmpty r1 || rangeIsEmpty r2) ⦄
                            → ⦃ tr : IsTrue (((rangeLower r1) < (rangeUpper r1)) && ((rangeLower r2) < (rangeUpper r2))) ⦄
                            → (rangeIsEmpty (rangeIntersection r1 r2)) ≡ not (rangeOverlap r1 r2)
prop_intersectionOverlap ⦃ ord ⦄ ⦃ diso ⦄ r1@(Rg _ _) r2@(Rg _ _) ⦃ ff ⦄ ⦃ tr ⦄ =
   begin
     (rangeIsEmpty (rangeIntersection r1 r2))
   =⟨⟩
     rangeIsEmpty (if_then_else_ (rangeIsEmpty r1 || rangeIsEmpty r2) emptyRange (Rg (max (rangeLower r1) (rangeLower r2)) (min (rangeUpper r1) (rangeUpper r2)))) 
   =⟨ cong rangeIsEmpty (propIf3 (rangeIsEmpty r1 || rangeIsEmpty r2) ff) ⟩
     (rangeIsEmpty (Rg (max (rangeLower r1) (rangeLower r2)) (min (rangeUpper r1) (rangeUpper r2))))
   =⟨⟩
     ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2)))
   =⟨ sym (prop_or_false ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2)))) ⟩  
     (false ||  ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2))))
   =⟨ cong (_|| ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2)))) (sym (propIsFalse (rangeIsEmpty r1 || rangeIsEmpty r2) ff)) ⟩  
     (((rangeIsEmpty r1) || (rangeIsEmpty r2)) || ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2))))
   =⟨ prop_or_assoc (rangeIsEmpty r1) (rangeIsEmpty r2) ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2))) ⟩
     ((rangeIsEmpty r1) || ((rangeIsEmpty r2) || ((min (rangeUpper r1) (rangeUpper r2)) <= (max (rangeLower r1) (rangeLower r2)))))
   =⟨ cong ((rangeIsEmpty r1) ||_) (cong ((rangeIsEmpty r2) ||_) (eq3 (rangeUpper r1) (rangeUpper r2) (rangeLower r1) (rangeLower r2) ⦃ tr ⦄)) ⟩
     ((rangeIsEmpty r1) || ((rangeIsEmpty r2) || (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)))     
   =⟨ not-not ((rangeIsEmpty r1) || (rangeIsEmpty r2) || (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)) ⟩
     not (not ((rangeIsEmpty r1) || (rangeIsEmpty r2) || (rangeUpper r1 <= rangeLower r2 || rangeUpper r2 <= rangeLower r1)))
   =⟨ cong (not) (demorgan3 (rangeIsEmpty r1) (rangeIsEmpty r2) (rangeUpper r1 <= rangeLower r2) (rangeUpper r2 <= rangeLower r1)) ⟩ 
     not (not (rangeIsEmpty r1) && not (rangeIsEmpty r2) && ((not (rangeUpper r1 <= rangeLower r2)) && (not (rangeUpper r2 <= rangeLower r1))))
   =⟨ cong not (cong ((not (rangeIsEmpty r1)) &&_) (cong ((not (rangeIsEmpty r2)) &&_) (prop_demorgan2 (rangeUpper r1 <= rangeLower r2) (rangeUpper r2 <= rangeLower r1)))) ⟩
     not (not (rangeIsEmpty r1) && not (rangeIsEmpty r2) && not ((rangeUpper r1 <= rangeLower r2) || (rangeUpper r2 <= rangeLower r1)))
   =⟨⟩
     not (rangeOverlap r1 r2)
   end

