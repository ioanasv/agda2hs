module Haskell.RangedSetsProp.RangedSetProperties where

open import Haskell.RangedSetsProp.library
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


-- record List2 (A : Set) : Set where
--   constructor _∷_∷_

-- open List2

-- head1 : List2 a -> a 
-- head1 (aa ∷ b ∷ c) = aa

-- head2 : List2 a -> a 
-- head2 (aa ∷ b ∷ c) = b

prop_empty : ⦃ o : Ord a ⦄ → ⦃ d : DiscreteOrdered a ⦄ → (v : a) 
                          → (not (rSetEmpty -?- v)) ≡ true 
prop_empty v = refl

prop_full : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (v : a) → (rSetFull -?- v) ≡ true
prop_full v = refl

postulate
  rangeSetCreation : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    -> {prf : IsTrue (validRangeList (rSetRanges rs))} -> (RS {{o}} {{dio}} (rSetRanges rs) {prf}) ≡ rs
  rangesEqiv : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
    → (rs1 : RSet a) 
    → (rs2 : RSet a) -> IsTrue (rSetRanges rs1 == rSetRanges rs2) -> rs1 ≡ rs2

-- postulate 


--     union0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) -> (rs1 : RSet a) -> (rs2 : RSet a) 
--                              -> (r ∷ (rSetRanges (rs1 -\/- rs2))) ≡ (rSetRanges ((RS (r ∷ (rSetRanges rs1))) -\/- rs2))

    -- unionIntersectionDistr : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) -> (rs2 : RSet a) -> (rs3 : RSet a)
    --                          -> ((rs1 -/\- rs3) -\/- (rs2 -/\- rs3)) ≡ ((rs1 -\/- rs2) -/\- rs3)
 
    -- rangeSetAsUnion : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) -> ⦃ ne : NonEmpty (rSetRanges rs) ⦄
                              -- -> rs ≡ ((RS ((head (rSetRanges rs) ⦃ ne ⦄) ∷ [])) -\/- (RS (tail (rSetRanges rs) ⦃ ne ⦄)))
 

-- union0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) -> (rs2 : RSet a) -> {{ ne : NonEmpty (rSetRanges rs1) }}
--   -> (rSetRanges (rs1 -\/- rs2)) ≡ ((head (rSetRanges rs1) {{ne}}) ∷ (rSetRanges ((RS (tail (rSetRanges rs1) {{ne}})) -\/- rs2)))
-- union0 {{o}} {{dio}} rs1@(RS ranges@(r1 ∷ rg1)) rs2@(RS []) {{ne}} = 
--   begin
--     (rSetRanges (rs1 -\/- rs2))
--   =⟨⟩
--     rSetRanges rs1 
--   =⟨⟩ 
--     (r1 ∷ rg1)
--   =⟨⟩ 
--     ((head ranges {{ne}}) ∷ (tail ranges {{ne}}))
--   =⟨⟩ 
--     ((head ranges {{ne}}) ∷ (rSetRanges (RS (tail ranges {{ne}}))))    
--   =⟨ cong ((head ranges {{ne}}) ∷_) (cong rSetRanges (sym (unionWithEmptySet (RS (tail ranges {{ne}}))))) ⟩ 
--     ((head (rSetRanges rs1) {{ne}}) ∷ (rSetRanges ((RS (tail (rSetRanges rs1) {{ne}})) -\/- (RS []))))
--    =⟨⟩ 
--     ((head (rSetRanges rs1) {{ne}}) ∷ (rSetRanges ((RS (tail (rSetRanges rs1) {{ne}})) -\/- rs2)))  
--   end   
-- union0 {{o}} {{dio}} rs1@(RS ranges@(r1 ∷ rg1)) rs2@(RS ranges2@(r2 ∷ rg2)) {{ne}} = 
--   begin
--     (rSetRanges (rs1 -\/- rs2))
--   =⟨⟩
--     ((head (rSetRanges rs1) {{ne}}) ∷ (rSetRanges (RS (tail (rSetRanges rs1) {{ne}}) -\/- rs2)))  
--     end

singletonRangeSetHas : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) -> (v : a) 
  -> {prf : IsTrue (validRangeList (r ∷ []))}
  -> (rSetHas (RS (r ∷ []) {prf}) v) ≡ rangeHas r v
singletonRangeSetHas r v {prf} = 
  begin 
    (rSetHas (RS (r ∷ []) {prf}) v)
  =⟨⟩  
    rangeHas r v 
  end


-- rangeHasSym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (r : Range a) -> (rs : RSet a) -> (v : a) 
--                              -> {prf1 : IsTrue }
--                              -> ((RS (r ∷ (rSetRanges rs))) -?- v) ≡ ((rangeHas r v) || (rs -?- v))
-- rangeHasSym r rs@(RS []) v = refl
-- rangeHasSym r rs@(RS ranges) v = 
--   begin 
--     ((RS (r ∷ (rSetRanges rs))) -?- v)
--   =⟨⟩
--     ((rangeHas r v) || ((RS (rSetRanges rs)) -?- v))
--   =⟨ cong ((rangeHas r v) ||_) (cong (_-?- v) (rangeSetCreation rs)) ⟩
--     ((rangeHas r v) || (rs -?- v))
--   end

unionWithEmptySet : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) 
  -> {prf : IsTrue (validRangeList (rSetRanges rs1))} 
  -> (rSetUnion rs1 {prf} (RS [] {empty {{o}} {{dio}}}) {empty {{o}} {{dio}}}) ≡ rs1
unionWithEmptySet {{o}} {{dio}} rs1@(RS []) {prf} = 
  begin 
    rSetUnion rs1 {prf} (RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}) {empty {{o}} {{dio}}}
  =⟨⟩  
    RS []
  =⟨ rangesEqiv {{o}} {{dio}} (RS []) rs1 (eq00 {{o}} {{dio}} {[]} {[]} refl) ⟩  
    rs1    
  end  
unionWithEmptySet {{o}} {{dio}} rs1@(RS ranges@(h ∷ t)) {prf} = 
  begin 
    rSetUnion rs1 {prf} (RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}) {empty {{o}} {{dio}}}
  =⟨⟩  
    rs1
  end



postulate
  emptyIntersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              -> IsFalse (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)

  emptyIntersection2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 b3 : Boundary a)
              -> IsFalse (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)           
   
  orderedBoundaries2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            -> IsFalse (b2 < b1)              
  orderedBoundaries3 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b1 b2 : Boundary a)
            -> IsTrue (b1 < b2)               
         


{-# TERMINATING #-}
lemma0 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) 
    -> {prf : IsTrue (validRangeList (rSetRanges rs))}
    → (ranges1 (bounds1 (rSetRanges rs))) ≡ (rSetRanges rs)
lemma0 {{o}} {{dio}} rs@(RS []) {_} = 
    begin
      (ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} (rSetRanges rs)))
    =⟨⟩
      (ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} []))
    =⟨⟩
      (ranges1 {{o}} {{dio}} [])
    =⟨⟩
      [] 
    =⟨⟩
      rSetRanges rs      
    end
lemma0 {{o}} {{dio}} rs@(RS (r@(Rg l u) ∷ rgs)) {prf} = 
    begin
      (ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} (rSetRanges rs)))
    =⟨⟩
      (ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} (r ∷ rgs)))
    =⟨⟩
      (ranges1 {{o}} {{dio}} ((rangeLower {{dio}} r) ∷ ((rangeUpper {{dio}} r) ∷ (bounds1 {{o}} {{dio}} rgs))))
    =⟨⟩
      ((Rg l u) ∷ ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} rgs))    
    =⟨⟩
      (r ∷ ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} rgs))
    =⟨ cong (r ∷_) (lemma0 {{o}} {{dio}} (RS rgs {headandtail rs prf}) {headandtail rs prf}) ⟩
      (r ∷ rgs)   
    =⟨⟩
      rSetRanges rs
    end


rangeEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (x : Boundary a) -> rangeIsEmpty (Rg x x) ≡ true
rangeEmpty {{o}} {{dio}} BoundaryBelowAll = refl
rangeEmpty {{o}} {{dio}} BoundaryAboveAll = refl
rangeEmpty {{o}} {{dio}} b@(BoundaryBelow m) =
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 {{o}} refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end
rangeEmpty {{o}} {{dio}} b@(BoundaryAbove m) = 
  begin 
    rangeIsEmpty (Rg b b)
   =⟨⟩
    ((BoundaryBelow m) <= (BoundaryBelow m))
   =⟨⟩      
    ((compare b b == LT) || (compare b b == EQ))
   =⟨⟩      
    ((compare m m == LT) || (compare m m == EQ))
   =⟨ cong ((compare m m == LT) ||_) (eq4 {{o}} refl) ⟩      
    ((compare m m == LT) || true)   
   =⟨⟩      
    ((compare m m == LT) || true)
   =⟨ prop_or_false3 (compare m m == LT) ⟩      
    true  
 end





merge2Empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) -> {{ne : NonEmpty bs}}
          -> filter (λ x -> rangeIsEmpty x == false) (merge2 (ranges1 (tail bs {{ne}})) (ranges1 bs)) ≡ []

merge2Empty2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) -> {{ne : NonEmpty bs}}
          -> filter (λ x -> rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (tail bs {{ne}}))) ≡ []  
merge2Empty2 {{o}} {{dio}} bounds@(b@(BoundaryAboveAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []
    =⟨⟩
      []      
    end
merge2Empty2 {{o}} {{dio}} bounds@(b@(BoundaryAbove x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []
    =⟨⟩
      []      
    end    
merge2Empty2 {{o}} {{dio}} bounds@(b@(BoundaryBelow x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []
    =⟨⟩
      []      
    end     
merge2Empty2 {{o}} {{dio}} bounds@(b@(BoundaryBelowAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b ∷ [])) (ranges1 []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []
    =⟨⟩
      []      
    end        
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ []))  (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 [])) [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 (ranges1 bounds) (ranges1 bss))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3' {{o}} {((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))}
        {(filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))}
      (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 {{o}} {{dio}} b1 b2 b3) ⟩
      
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2  (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2  ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ false (merge2 [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll))
        ∷ (merge2 ((Rg b1 b2) ∷ []) []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2  (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2  ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2  (ranges1 bs) (ranges1 (b2 ∷ bs))) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss) )))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end  
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b1 ∷ b2 ∷ [])) (ranges1 (b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b1 b2) ∷ (ranges1 [])) ((Rg b2 BoundaryAboveAll) ∷ []))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b1 b2) ∷ []) ((Rg b2 BoundaryAboveAll) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (if_then_else_ (b2 < BoundaryAboveAll) (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ [])) (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2  BoundaryAboveAll)) 
        ∷ (if_then_else_  true (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))  (merge2 ((Rg b1 b2) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ (merge2  [] ((Rg b2 BoundaryAboveAll) ∷ []))) 
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])  

    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 BoundaryAboveAll)) == false)) (emptyIntersection2 {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty2 {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2  (ranges1 bounds) (ranges1 (tail bounds {{ne}})))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b1 ∷ b2 ∷ bs)) (ranges1 (b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) ((Rg b2 b3) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (if_then_else_ (b2 < b3) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))  (merge2 ((Rg b1 b2) ∷ (ranges1 bs)) (ranges1 bss))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷_) 
        (propIf2 (b2 < b3) (orderedBoundaries3 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false)  
        ((rangeIntersection (Rg b1 b2) (Rg b2 b3)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs)))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b1 b2) (Rg b2 b3)) == false) (emptyIntersection2 {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b2 ∷ bs))))
    =⟨ merge2Empty {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end 

-- merge2Empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) -> {{ne : NonEmpty bs}}
          -- -> filter (λ x -> rangeIsEmpty x == false) (merge2 (ranges1 (tail bs {{ne}})) (ranges1 bs)) ≡ []
merge2Empty {{o}} {{dio}} bounds@(b ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []
    =⟨⟩
      []      
    end
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []     
    =⟨⟩
      []      
    end 
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAboveAll) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3' {{o}} {((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))}
        {(filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))}
      (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false) (emptyIntersection {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end           
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelowAll) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryAbove x) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end      
    
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ []) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 (b2 ∷ [])) (ranges1 (b1 ∷ b2 ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ (ranges1 [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) ((Rg b1 b2) ∷ []))      
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_ (BoundaryAboveAll < b2) (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (if_then_else_  false (merge2 [] ((Rg b1 b2) ∷ [])) (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ (merge2 ((Rg b2 BoundaryAboveAll) ∷ []) [])) 
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) 
        ∷ [])               
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
       (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])   
    =⟨ propIf3 ((rangeIsEmpty (rangeIntersection (Rg b2 BoundaryAboveAll) (Rg b1 b2)) == false)) (emptyIntersection {{o}} {{dio}} b1 b2 BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []      
    end
merge2Empty {{o}} {{dio}} bounds@(b1 ∷ b2@(BoundaryBelow x) ∷ bs@(b3 ∷ bss)) {{ne}} = 
    begin
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (tail bounds {{ne}})) (ranges1 bounds))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 (b1 ∷ b2 ∷ bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b2 b3) ∷ (ranges1 bss)) ((Rg b1 b2) ∷ (ranges1 bs)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (if_then_else_ (b3 < b2) (merge2 (ranges1 bss) ((Rg b1 b2) ∷ (ranges1 bs))) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
   
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) (cong ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷_) 
        (propIf3 (b3 < b2) (orderedBoundaries2 {{o}} {{dio}} b2 b3))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) 
        ∷ (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)  
        ((rangeIntersection (Rg b2 b3) (Rg b1 b2)) ∷ 
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs))))
         
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b2 b3) (Rg b1 b2)) == false)(emptyIntersection {{o}} {{dio}} b1 b2 b3) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 (b2 ∷ bs)) (ranges1 bs)))
    =⟨ merge2Empty2 {{o}} {{dio}} (b2 ∷ bs) ⟩ -- induction here!!!! merge2Empty ..
      []      
    end         


lemma2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (bs : List (Boundary a)) 
               -> (filter (λ x -> rangeIsEmpty x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs)))) ≡ []
lemma2 {{o}} {{dio}} [] =
    begin
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 []) (ranges1 (setBounds1 []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] (ranges1 (BoundaryBelowAll ∷ []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []    
    end

lemma2 {{o}} {{dio}} bs@(BoundaryBelowAll ∷ []) =
    begin
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (BoundaryBelowAll ∷ [])))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  (ranges1 [])))
    =⟨⟩
     (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])  []))
    =⟨⟩    
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []    
    end

lemma2 {{o}} {{dio}} bs@(BoundaryAboveAll ∷ []) =
    begin
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)(merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 [] (ranges1 (setBounds1 (BoundaryAboveAll ∷ [])))))
    =⟨⟩    
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    =⟨⟩
      []    
    end

lemma2 {{o}} {{dio}} bs@(b@(BoundaryBelow x) ∷ []) = 
    begin
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 ((BoundaryBelow x) ∷ [])))))
    =⟨⟩    
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection {{o}} {{dio}} BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 {{o}} {{dio}} bs@(b@(BoundaryAbove x) ∷ []) =
    begin
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)  (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (setBounds1 (b ∷ [])))))
    =⟨⟩    
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) (ranges1 (BoundaryBelowAll ∷ (b ∷ [])))))
    =⟨⟩  
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg b BoundaryAboveAll) ∷ []) ((Rg BoundaryBelowAll b) ∷ [])))          
    =⟨⟩         
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ (BoundaryAboveAll < b) (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (if_then_else_ false (merge2 [] ((Rg BoundaryBelowAll b) ∷ [])) (merge2 ((Rg b BoundaryAboveAll) ∷ []) []))))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (merge2 ((Rg b BoundaryAboveAll) ∷ []) [])))
    =⟨⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ []))   
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) 
       ((rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
        (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])
    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg b BoundaryAboveAll) (Rg BoundaryBelowAll b)) == false) (emptyIntersection {{o}} {{dio}} BoundaryBelowAll b BoundaryAboveAll) ⟩
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])       
    =⟨⟩
      []                   
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryAboveAll) ∷ (b ∷ bss)) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 {{o}} {{dio}} a b))) ⟩
      
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3' {{o}}
        {((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))}
          {(filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))}
        (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection {{o}} {{dio}} BoundaryBelowAll a b) ⟩      
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 {{o}} {{dio}} bs ⟩
      []                         
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelow x) ∷ (b ∷ bss)) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 {{o}} {{dio}} a b))) ⟩
      
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection {{o}} {{dio}} BoundaryBelowAll a b) ⟩      
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 {{o}} {{dio}} bs ⟩
      []                         
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryAbove x) ∷ (b ∷ bss)) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (setBounds1 (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) (ranges1 (BoundaryBelowAll ∷ (a ∷ (b ∷ bss)))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bss)) ((Rg BoundaryBelowAll a) ∷ ranges1 (b ∷ bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (if_then_else_ (b < a) (merge2 (ranges1 bss) (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false))
        (cong ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) ∷_) (propIf3 (b < a) (orderedBoundaries2 {{o}} {{dio}} a b))) ⟩
      
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
        ∷ (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))) 
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)  
        ((rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) 
          ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss)))))  
            (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg BoundaryBelowAll a)) == false)
        (emptyIntersection {{o}} {{dio}} BoundaryBelowAll a b) ⟩      
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (b ∷ bss))))   
    =⟨ merge2Empty2 {{o}} {{dio}} bs ⟩
      []                         
    end   

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelowAll) ∷ b ∷ bs2@(c ∷ bss)) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) (ranges1 (b ∷ bs2)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 bs2)) ((Rg b c) ∷ (ranges1 bss)))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (if_then_else_ (b < c) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))) (merge2 (ranges1 bs) (ranges1 bss)))) 
    
    =⟨ cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false))
        (cong ((rangeIntersection (Rg a b) (Rg b c)) ∷_) (propIf2 (b < c) (orderedBoundaries3 {{o}} {{dio}} b c))) ⟩
     
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b c)) 
        ∷ (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false)  
       ((rangeIntersection (Rg a b) (Rg b c)) ∷
         (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2)))))  
         (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b c)) == false) (emptyIntersection2 {{o}} {{dio}} a b c) ⟩   
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs2) (ranges1 (b ∷ bs2))))
    =⟨ merge2Empty {{o}} {{dio}} (b ∷ bs2) ⟩ 
      []                    
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAboveAll) ∷ []) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)(merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) [])
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []      
    =⟨⟩
      []    
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelowAll) ∷ []) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
           (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])    
    =⟨ propIf3' {{o}}
      {((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))}
      {(filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []) }
      (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 {{o}} {{dio}} a b BoundaryAboveAll) ⟩         
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryAbove x) ∷ []) =
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
           (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 {{o}} {{dio}} a b BoundaryAboveAll) ⟩         
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])  
    =⟨⟩         
      []       
    end

lemma2 {{o}} {{dio}} bs@(a@(BoundaryBelowAll) ∷ b@(BoundaryBelow x) ∷ []) =
          (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 bs) (ranges1 (setBounds1 bs))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ (ranges1 [])) (ranges1 (setBounds1 (a ∷ b ∷ []))))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) (ranges1 (b ∷ [])))
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ((Rg a b) ∷ []) ((Rg b BoundaryAboveAll) ∷ []))
    =⟨⟩
     filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ (b < BoundaryAboveAll) (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))    
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (if_then_else_ true (merge2 [] (ranges1 (setBounds1 bs))) (merge2 (ranges1 bs) [])))       
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) 
        ∷ (merge2 [] (ranges1 (setBounds1 bs))))             
    =⟨⟩
      filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ [])      
    =⟨⟩
      if_then_else_ (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false)  
          ((rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) ∷ (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) []))
           (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])    
    =⟨ propIf3 (rangeIsEmpty (rangeIntersection (Rg a b) (Rg b BoundaryAboveAll)) == false) (emptyIntersection2 {{o}} {{dio}} a b BoundaryAboveAll) ⟩         
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) [])  
    =⟨⟩         
      []       
    end   


merge2' : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Range a) -> List (Range a)
merge2' ms1 ms2 = merge2 ms2 ms1


prop_empty_intersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  -> {prf : IsTrue (validRangeList (rSetRanges rs))} → 
  rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)}) ≡ true

prop_empty_intersection {{o}} {{dio}} rs@(RS ranges) {prf} =
    begin
      rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs {prf} (negation rs prf)})
    =⟨⟩
      rSetIsEmpty (rSetIntersection rs {prf}
       (RS (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))) {negation rs prf}) 
        {negation2 rs {prf} (negation rs prf)} )
    
    =⟨⟩    
      rSetIsEmpty (RS (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) 
        (merge2 ranges (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))))) 
              {intersection0 rs (RS (ranges1 (setBounds1 (bounds1 ranges))) {negation rs prf}) prf (negation rs prf)}) 
    =⟨⟩ 
      rangesAreEmpty (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 ranges (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))))) 
    =⟨ cong rangesAreEmpty (cong (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false)) 
              (cong (merge2' (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges)))) (sym (lemma0 rs {prf})))) ⟩  
      rangesAreEmpty (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 (ranges1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges)) 
          (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges)))))             
    =⟨ cong rangesAreEmpty (lemma2 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges)) ⟩ 
     rangesAreEmpty {{o}} {{dio}} []  
    =⟨⟩           
      true
   end  


prop_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  -> {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubset rs {prf} rs {prf} ≡ true
prop_subset {{o}} {{dio}} rs {prf} = 
   begin
    rSetIsSubset rs {prf} rs {prf}
   =⟨⟩
    rSetIsEmpty (rSetDifference rs {prf} rs {prf})
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})
   =⟨ prop_empty_intersection {{o}} {{dio}} rs {prf} ⟩
     true   
   end 

prop_strictSubset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a)
  -> {prf : IsTrue (validRangeList (rSetRanges rs))} → rSetIsSubsetStrict rs {prf} rs {prf} ≡ false
prop_strictSubset {{o}} {{dio}} rs {prf} = 
   begin
    rSetIsSubsetStrict rs {prf} rs {prf}
   =⟨⟩
    rSetIsEmpty (rSetDifference rs {prf} rs {prf}) && (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))
   =⟨⟩
     rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)}) 
      && (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))
   =⟨ cong (_&& (not (rSetIsEmpty (rSetDifference rs {prf} rs {prf})))) (prop_empty_intersection {{o}} {{dio}} rs {prf}) ⟩
    true && (not (rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})))
   =⟨⟩
    (not (rSetIsEmpty (rSetIntersection rs {prf} (rSetNegation rs {prf}) {negation2 rs (negation rs prf)})))
   =⟨ cong not (prop_empty_intersection {{o}} {{dio}} rs {prf}) ⟩  
     not true 
   =⟨⟩    
     false   
   end 
-- prop_union : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) → (v : a) → (rs1 -?- v || rs2 -?- v) ≡  ((rs1 -\/- rs2) -?- v)
-- prop_union {{o}} {{dio}} rs1@(RS []) rs2@(RS []) v = 
--    begin
--     ((rs1 -?- v) || (rs2 -?- v))
--    =⟨⟩
--     (false || false)
--    =⟨⟩
--      false
--    =⟨⟩
--      ((RS []) -?- v) 
--    =⟨⟩
--      ((rSetUnion rs1 rs2) -?- v)      
--    end 
-- prop_union {{o}} {{dio}} rs1@(RS []) rs2@(RS rg1@(r1 ∷ rss1)) v = 
--    begin
--     ((rs1 -?- v) || (rs2 -?- v))
--    =⟨⟩
--     (false || (rs2 -?- v))
--    =⟨⟩
--      (rs2 -?- v)
--    =⟨⟩
--      ((rSetUnion rs1 rs2) -?- v) 
--    end 
-- prop_union {{o}} {{dio}} rs1@(RS rg@(r1 ∷ rss1)) rs2@(RS []) v = 
--    begin
--     ((rs1 -?- v) || (rs2 -?- v))
--    =⟨⟩
--     ((rs1 -?- v) || false)
--    =⟨ prop_or_false2 (rs1 -?- v) ⟩
--      (rs1 -?- v)
--    =⟨⟩
--      ((rSetUnion rs1 rs2) -?- v) 
--    end    
-- prop_union {{o}} {{dio}} rs1@(RS rg1@(r1 ∷ rss1)) rs2@(RS rg2@(r2 ∷ rss2)) v = 
--    begin
--     ((rs1 -?- v) || (rs2 -?- v))
--    =⟨⟩
--     (((rangeHas r1 v) || (rSetHas (RS rss1) v)) || (rs2 -?- v))
--    =⟨ prop_or_assoc (rangeHas r1 v) (rSetHas (RS rss1) v)  (rs2 -?- v) ⟩
--      ((rangeHas r1 v) || (rSetHas (RS rss1) v) || (rs2 -?- v))
--    =⟨ cong ((rangeHas r1 v) ||_) (prop_union (RS rss1) rs2 v) ⟩
--      ((rangeHas r1 v) || (((RS rss1) -\/- rs2) -?- v)) 
--    =⟨ sym (rangeHasSym r1 ((RS rss1) -\/- rs2) v) ⟩
--      RS (r1 ∷ (rSetRanges ((RS rss1) -\/- rs2))) -?- v
--    =⟨ cong (_-?- v) (cong RS (union0 r1 (RS rss1) rs2)) ⟩       
--      RS (rSetRanges ((RS (r1 ∷ rss1)) -\/- rs2)) -?- v
--    =⟨ cong (_-?- v) (sym (rangeSetCreation ((RS (r1 ∷ rss1)) -\/- rs2))) ⟩
--      ((rs1 -\/- rs2) -?- v)    
--    end

-- prop_union_has_sym : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ 
--   → (rs1 : RSet a) → (rs2 : RSet a) → (v : a) 
--   → ((rs1 -\/- rs2) -?- v) ≡ ((rs2 -\/- rs1) -?- v)
-- prop_union_has_sym {{o}} {{dio}} rs1@(RS ranges1) rs2@(RS ranges2) v = 
--   begin 
--     ((rs1 -\/- rs2) -?- v) 
--   =⟨ sym (prop_union rs1 rs2 v) ⟩ 
--     ((rs1 -?- v) || (rs2 -?- v))
--   =⟨ prop_or_sym (rs1 -?- v) (rs2 -?- v) ⟩
--     ((rs2 -?- v) || (rs1 -?- v))
--   =⟨ prop_union rs2 rs1 v ⟩
--     ((rs2 -\/- rs1) -?- v) 
--   end  

-- prop_union_same_set : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) -> (v : a) → ((rs1 -\/- rs1) -?- v) ≡ (rs1 -?- v)
-- prop_union_same_set {{o}} {{dio}} rs1@(RS ranges1) v = 
--   begin 
--     ((rs1 -\/- rs1) -?- v) 
--   =⟨ sym (prop_union rs1 rs1 v) ⟩ 
--     ((rs1 -?- v) || (rs1 -?- v))
--   =⟨ prop_or_same_value (rs1 -?- v) ⟩
--     (rs1 -?- v) 
--   end  

prop_validNormalisedEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} []) ≡ true
prop_validNormalisedEmpty {{o}} {{dio}} = 
  begin 
    validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} []) 
  =⟨⟩ 
    validRangeList {{o}} {{dio}} []
  =⟨⟩
    true 
  end  

prop_emptyRange : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ -> (r : Range a) -> not (rangeIsEmpty r) ≡ (rangeLower r <= rangeUpper r)
prop_emptyRange {{o}} {{dio}} r@(Rg l u) = 
  begin 
    not (rangeIsEmpty r) 
  =⟨⟩ 
    not (u <= l)
  =⟨ eq2 u l ⟩
    l < u
  =⟨ lteq l u ⟩
    l <= u
  end 

prop_validNormalisedSingleton1 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ -> (r : Range a) 
              -> {{ re : IsTrue (not (rangeIsEmpty r)) }}
              → validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} (r ∷ [])) ≡ true
prop_validNormalisedSingleton1 {{o}} {{dio}} r {{re}} = 
  begin 
    validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} (r ∷ [])) 
  =⟨⟩ 
    validRangeList {{o}} {{dio}} (normalise (sort (filter (λ x -> (rangeIsEmpty x) == false) (r ∷ []))))
  =⟨⟩
    validRangeList {{o}} {{dio}} (normalise (sort (if ((rangeIsEmpty r) == false) then (r ∷ (filter (λ x -> (rangeIsEmpty x) == false) [])) else (filter (λ x -> (rangeIsEmpty x) == false) []))))
  =⟨ cong validRangeList (cong normalise (cong sort (propIf2 ((rangeIsEmpty r) == false) (truth2 re)))) ⟩
    validRangeList {{o}} {{dio}} (normalise (sort (r ∷ (filter (λ x -> (rangeIsEmpty x) == false) []))))
  =⟨⟩  
    validRangeList {{o}} {{dio}} (normalise (sort (r ∷ [])))
  =⟨⟩
    validRangeList {{o}} {{dio}} (normalise (r ∷ []))
  =⟨⟩  
    validRangeList {{o}} {{dio}} (r ∷ [])
  =⟨⟩    
    (rangeLower r) <= (rangeUpper r)   
  =⟨ truth (prop_emptyRange r) {{re}} ⟩    
    true 
  end  

prop_validNormalisedSingleton2 : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ -> (r : Range a) 
              -> {{ re : IsFalse ((rangeIsEmpty r) == false) }}
              → validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} (r ∷ [])) ≡ true
prop_validNormalisedSingleton2 {{o}} {{dio}} r {{re}} = 
  begin 
    validRangeList {{o}} {{dio}} (normaliseRangeList {{o}} {{dio}} (r ∷ [])) 
  =⟨⟩ 
    validRangeList {{o}} {{dio}} (normalise (sort (filter (λ x -> (rangeIsEmpty x) == false) (r ∷ []))))
  =⟨⟩
    validRangeList {{o}} {{dio}} (normalise (sort (if ((rangeIsEmpty r) == false) then (r ∷ (filter (λ x -> (rangeIsEmpty x) == false) [])) else (filter (λ x -> (rangeIsEmpty x) == false) []))))
  =⟨ cong validRangeList (cong normalise (cong sort (propIf3 ((rangeIsEmpty r) == false) re))) ⟩
    validRangeList {{o}} {{dio}} (normalise (sort (filter (λ x -> (rangeIsEmpty x) == false) [])))
  =⟨⟩  
    validRangeList {{o}} {{dio}} (normalise (sort []))
  =⟨⟩
    validRangeList {{o}} {{dio}} (normalise [])
  =⟨⟩  
    validRangeList {{o}} {{dio}} []
  =⟨⟩     
    true 
  end  

-- -- prop_union_commutes : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) -> (rs2 : RSet a) -> (rs1 -\/- rs2) ≡ (rs2 -\/- rs1)
-- -- prop_union_commutes (RS []) (RS []) = refl
-- -- prop_union_commutes (RS ranges@(r ∷ rs)) (RS []) = refl
-- -- prop_union_commutes (RS []) (RS ranges@(r ∷ rs)) = refl
-- -- prop_union_commutes RS1@(RS ranges1@(r1 ∷ rs1)) RS2@(RS ranges2@(r2 ∷ rs2)) = refl

-- -- prop_difference : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) → (rs2 : RSet a) → (v : a) 
-- --                     -> (rs1 -?- v && not (rs2 -?- v)) ≡ ((rs1 -!- rs2) -?- v)
-- -- prop_difference {{o}} {{dio}} rs1@(RS rg1@(r1 ∷ rss1)) rs2@(RS rg2@(r2 ∷ rss2)) v =
-- --    begin
-- --     (rs1 -?- v && not (rs2 -?- v))
-- --    =⟨⟩
-- --     (((rangeHas r1 v) || (rSetHas (RS rss1) v)) && not (rs2 -?- v))
-- --    =⟨ prop_distr (rangeHas r1 v) (rSetHas (RS rss1) v)  (not (rs2 -?- v)) ⟩
-- --      (((rangeHas r1 v) && not (rs2 -?- v)) || ((rSetHas (RS rss1) v) && not (rs2 -?- v)))
-- --    =⟨ cong (((rangeHas r1 v) && not (rs2 -?- v)) ||_) (prop_difference (RS rss1) rs2 v) ⟩
-- --      (((rangeHas r1 v) && not (rs2 -?- v)) || (((RS rss1) -!- rs2) -?- v)) 
   
-- --    =⟨ rangeHasSym r1 ((RS rss1) -\/- rs2) v ⟩
-- --      RS (r1 ∷ (rSetRanges ((RS rss1) -\/- rs2))) -?- v
-- --    =⟨ cong (_-?- v) (cong RS (union0 r1 (RS rss1) rs2)) ⟩       
-- --      RS (rSetRanges ((RS (r1 ∷ rss1)) -\/- rs2)) -?- v
-- --    =⟨ cong (_-?- v) (sym (rangeSetCreation ((RS (r1 ∷ rss1)) -\/- rs2))) ⟩
-- --      ((rs1 -\/- rs2) -?- v)    
-- --    end

-- -- prop_intersection : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs1 : RSet a) -> (rs2 : RSet a) -> (v : a) 
-- --                     → (rs1 -?- v && rs2 -?- v) ≡  ((rs1 -/\- rs2) -?- v)
-- -- prop_intersection {{o}} {{dio}} rs1@(RS rgs@(h ∷ t)) rs2@(RS []) v = 
-- --    begin
-- --     ((rs1 -?- v) && (rs2 -?- v))
-- --    =⟨⟩
-- --     ((rs1 -?- v) && false) 
-- --    =⟨ prop_and_false (rs1 -?- v) ⟩
-- --     false
-- --    =⟨⟩
-- --     ((RS []) -?- v)
-- --    =⟨⟩
-- --     ((rs1 -/\- rs2) -?- v) 
-- --    end      

-- -- prop_intersection {{o}} {{dio}} rs1@(RS []) rs2@(RS rgs@(h ∷ t)) v = 
-- --    begin
-- --     ((rs1 -?- v) && (rs2 -?- v))
-- --    =⟨⟩
-- --     (false && (rs2 -?- v)) 
-- --    =⟨⟩
-- --     false 
-- --    =⟨⟩
-- --     ((RS []) -?- v)
-- --    =⟨⟩
-- --     ((rs1 -/\- rs2) -?- v) 
-- --    end       
-- -- prop_intersection {{o}} {{dio}} rs1@(RS []) rs2@(RS []) v = 
-- --    begin
-- --     ((rs1 -?- v) && (rs2 -?- v))
-- --    =⟨⟩
-- --     (false && (rs2 -?- v)) 
-- --    =⟨⟩
-- --     false 
-- --    =⟨⟩
-- --     ((RS []) -?- v)
-- --    =⟨⟩
-- --     ((rs1 -/\- rs2) -?- v) 
-- --    end    
-- -- prop_intersection {{o}} {{dio}} rs1@(RS rg1@(r1 ∷ rss1)) rs2@(RS rg2@(r2 ∷ rss2)) v = 
-- --    begin
-- --     ((rs1 -?- v) && (rs2 -?- v))
-- --    =⟨⟩
-- --     (((rangeHas r1 v) || (rSetHas (RS rss1) v)) && (rs2 -?- v))
-- --    =⟨ prop_distr (rangeHas r1 v) (rSetHas (RS rss1) v)  (rs2 -?- v) ⟩
-- --      (((rangeHas r1 v) && (rs2 -?- v)) || ((rSetHas (RS rss1) v) && (rs2 -?- v)))
-- --    =⟨ cong (((rangeHas r1 v) && (rs2 -?- v)) ||_) (prop_intersection (RS rss1) rs2 v) ⟩
-- --      (((rangeHas r1 v) && (rs2 -?- v)) || (((RS rss1) -/\- rs2) -?- v)) 
-- --    =⟨ cong (_|| (((RS rss1) -/\- rs2) -?- v)) (cong (_&& (rs2 -?- v)) (sym (singletonRangeSetHas r1 v))) ⟩
-- --      ((((RS (r1 ∷ [])) -?- v) && (rs2 -?- v)) || (((RS rss1) -/\- rs2) -?- v))
-- --    =⟨ cong (_|| (((RS rss1) -/\- rs2) -?- v)) (prop_intersection (RS (r1 ∷ [])) rs2 v) ⟩       
-- --      ((((RS (r1 ∷ [])) -/\- rs2) -?- v) || (((RS rss1) -/\- rs2) -?- v))
-- --    =⟨ prop_union ((RS (r1 ∷ [])) -/\- rs2) ((RS rss1) -/\- rs2) v ⟩
-- --      ((((RS (r1 ∷ [])) -/\- rs2) -\/- ((RS rss1) -/\- rs2)) -?- v)  
-- --    =⟨ cong (_-?- v) (unionIntersectionDistr (RS (r1 ∷ [])) (RS rss1) rs2) ⟩
-- --      ((((RS (r1 ∷ [])) -\/- (RS rss1)) -/\- rs2) -?- v) 
-- --    =⟨ cong (_-?- v) (cong (_-/\- rs2) (sym (rangeSetAsUnion rs1))) ⟩
-- --      ((rs1 -/\- rs2) -?- v)       
-- --    end


-- -- prop_subset : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) → (rs -<=- rs) ≡ true
-- -- prop_subset rs = refl

-- -- prop_not_empty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (rs : RSet a) -> (v : a) -> ((rs -?- v) ≡ true) -> not (rSetIsEmpty rs) ≡ true
-- -- prop_not_empty rs v = 
-- --    begin
-- --     (rs -?- v)
-- --    =⟨⟩

-- --    =⟨⟩  
   
-- --    =⟨⟩

-- --    =⟨⟩

-- --    =⟨⟩     
-- --    end

-- -- prop_empty_intersection : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> rSetIsEmpty (rs -/\- rSetNegation rs) ≡ true
-- -- prop_empty_intersection rs = refl

-- -- prop_validNormalised : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rg : List (Range a)) -> validRangeList (normaliseRangeList {{o}} {{dio}} rg) ≡ true
-- -- prop_validNormalised {{o}} {{dio}} ls = 
-- --    begin
-- --       validRangeList (normaliseRangeList rg)
-- --      =⟨⟩ 
-- --       (rangeHas (Rg (BoundaryBelow v1) (BoundaryAbove v1)) v2)
-- --      =⟨⟩
-- --       ((v2 />/ (BoundaryBelow v1)) && (not (v2 />/ (BoundaryAbove v1))))
-- --      =⟨⟩
-- --       ((v2 >= v1) && (not (v2 > v1)))
-- --      =⟨ eq1 v2 v1 ⟩
-- --       true
-- --    end