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

infixl 7 _-/\-_
infixl 6 _-\/-_ _-!-_
infixl 5 _-<=-_ _-<-_ _-?-_

okAdjacent : {{Ord a}} -> {{DiscreteOrdered a}} -> Range a -> Range a -> Bool
okAdjacent (Rg lower1 upper1) (Rg lower2 upper2) = lower1 <= upper1 && upper1 <= lower2 && lower2 <= upper2

validRangeList : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> Bool
validRangeList [] = true
validRangeList (x ∷ []) = (rangeLower x) <= (rangeUpper x)
validRangeList (x ∷ rs@(r1 ∷ rss)) = (okAdjacent x r1) && (validRangeList rs)

validBoundaryList : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Boundary a) -> Bool
validBoundaryList [] = true
validBoundaryList (x ∷ []) = true
validBoundaryList (x ∷ rs@(r1 ∷ rss)) = (x <= r1) && (validBoundaryList rs)

data RSet (a : Set) : Set where
    RS : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rg : List (Range a)) 
         -> {.(IsTrue (validRangeList rg))} -> RSet a

rSetRanges : RSet a -> List (Range a)
rSetRanges (RS ranges) = ranges

overlap1 : {{ Ord a }} -> {{ DiscreteOrdered a }} -> Range a -> Range a -> Bool
overlap1 (Rg _ upper1) (Rg lower2 _) = (upper1 >= lower2)

normalise : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Range a)
normalise (r1 ∷ r2 ∷ rs) = 
   if_then_else_ (overlap1 r1 r2) 
      (normalise ((Rg (rangeLower r1) (max (rangeUpper r1) (rangeUpper r2))) ∷ rs)) 
         (r1 ∷ (normalise (r2 ∷ rs)))
normalise rs = rs

normaliseRangeList : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Range a)
normaliseRangeList [] = []
normaliseRangeList rs@(r1 ∷ rss) = normalise (sort (filter (λ r -> (rangeIsEmpty r) == false) rs))

-- makeRangedSet : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> RSet a
-- makeRangedSet rs = RS (normaliseRangeList rs)

unsafeRangedSet : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rg : List (Range a)) 
   -> {IsTrue (validRangeList {{o}} {{dio}} rg)} -> RSet a
unsafeRangedSet rs {prf}  = RS rs {prf}

ranges3 : Maybe (Boundary a) -> (Boundary a -> Boundary a) -> (Boundary a -> Maybe (Boundary a)) -> List (Range a)
{-# TERMINATING #-}
ranges2 : Boundary a -> (Boundary a -> Boundary a) -> (Boundary a -> Maybe (Boundary a)) -> List (Range a)
ranges2 b upperFunc succFunc = (Rg b (upperFunc b)) ∷ (ranges3 (succFunc b) upperFunc succFunc)

ranges3 (Just b1) upperFunc succFunc = ranges2 b1 upperFunc succFunc
ranges3 Nothing _ _ = []

setBounds1 : {{Ord a}} -> {{DiscreteOrdered a}} -> (xs : List (Boundary a)) -> List (Boundary a)
setBounds1 (BoundaryBelowAll ∷ xs) = xs 
setBounds1 xs = (BoundaryBelowAll ∷ xs)

bounds1 : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Boundary a)
bounds1 (r ∷ rs) = (rangeLower r) ∷ (rangeUpper r) ∷ (bounds1 rs)
bounds1 _ = []

ranges1 : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Boundary a) -> List (Range a)
ranges1 (b1 ∷ b2 ∷ bs) = (Rg b1 b2) ∷ (ranges1 bs)
ranges1 (BoundaryAboveAll ∷ [])  = []
ranges1 (b ∷ []) = (Rg b BoundaryAboveAll) ∷ []
ranges1 _ = []

merge1 : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Range a) -> List (Range a)
merge1 ms1 [] = ms1
merge1 [] ms2 = ms2
merge1 ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = if_then_else_ (h1 < h2) (h1 ∷ (merge1 t1 ms2)) (h2 ∷ (merge1 ms1 t2))
      
merge2 : {{Ord a}} -> {{DiscreteOrdered a}} -> List (Range a) -> List (Range a) -> List (Range a)
merge2 ms1@(h1 ∷ t1) ms2@(h2 ∷ t2) = 
   (rangeIntersection h1 h2) ∷ (if_then_else_ (rangeUpper h1 < rangeUpper h2) (merge2 t1 ms2) (merge2 ms1 t2))
merge2 _ _ = []


-- intersection00 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs1 : RSet a) -> (rs2 : RSet a) 
--                   -> validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2))) ≡ true
-- intersection00 rs1@(RS ranges) rs2@(RS []) =                  
--    begin
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2)))
--    =⟨⟩
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 ranges [])) 
--    =⟨⟩
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) []) 
--    =⟨⟩
--     validRangeList []
--    =⟨⟩
--     true    
--    end

-- intersection00 rs1@(RS []) rs2@(RS ranges) =                  
--    begin
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2)))
--    =⟨⟩
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 [] ranges)) 
--    =⟨⟩
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) []) 
--    =⟨⟩
--     validRangeList []
--    =⟨⟩
--     true    
--    end

-- intersection00 rs1@(RS ranges1@(r1 ∷ rss1)) rs2@(RS ranges2@(r2 ∷ rss2)) =                  
--    begin
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2)))
--    =⟨⟩
--     validRangeList (filter (λ x -> (rangeIsEmpty x == false))  
--       ((rangeIntersection r1 r2) ∷ (if_then_else_ (rangeUpper r1 < rangeUpper r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
--    =⟨⟩
--     validRangeList (
--        if_then_else_ (rangeIsEmpty (rangeIntersection r1 r2) == false)
      
--       ((rangeIntersection r1 r2) ∷ (filter (λ x -> (rangeIsEmpty x == false))
--        (if_then_else_ (rangeUpper r1 < rangeUpper r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))) 
       
--        (filter (λ x -> (rangeIsEmpty x == false)) 
--          (if_then_else_ (rangeUpper r1 < rangeUpper r2) (merge2 rss1 ranges2) (merge2 ranges1 rss2)))
--       ) 
--    =⟨⟩
--     validRangeList []
   -- =⟨⟩
   --  true    
   -- end

postulate
   -- TO PROVE
   intersection0 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs1 : RSet a) -> (rs2 : RSet a)
      -> IsTrue (validRangeList (rSetRanges rs1)) -> IsTrue (validRangeList (rSetRanges rs2))
      -> IsTrue (validRangeList (filter (λ x -> (rangeIsEmpty x == false)) (merge2 (rSetRanges rs1) (rSetRanges rs2))))
   
   headandtail : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a }} -> (rs : RSet a) 
      -> {{ne : NonEmpty (rSetRanges rs)}} -> (IsTrue (validRangeList (rSetRanges rs))) 
      -> (IsTrue (validRangeList (tail (rSetRanges rs) {{ne}})))

BoundaryBelowAllSmaller :  {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (b : Boundary a)
      -> (BoundaryBelowAll <= b) ≡ true
BoundaryBelowAllSmaller BoundaryBelowAll = refl
BoundaryBelowAllSmaller BoundaryAboveAll = refl
BoundaryBelowAllSmaller (BoundaryBelow _) = refl
BoundaryBelowAllSmaller (BoundaryAbove _)  = refl

validRanges1 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (bs : List (Boundary a)) ->
            validRangeList (ranges1 bs) ≡ validBoundaryList bs
validRanges1 {{o}} {{dio}} [] = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 [])
   =⟨⟩ 
      validRangeList {{o}} {{dio}} [] 
   =⟨⟩ 
      true 
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} []
   end 
validRanges1 {{o}} {{dio}} (BoundaryAboveAll ∷ []) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (BoundaryAboveAll  ∷ []))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} [] 
   =⟨⟩ 
      true 
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} (BoundaryAboveAll ∷ [])
   end  
validRanges1 {{o}} {{dio}} (BoundaryBelowAll ∷ []) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (BoundaryBelowAll ∷ []))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ [])
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} (BoundaryBelowAll ∷ [])
   end     
validRanges1 {{o}} {{dio}} ((BoundaryAbove x) ∷ []) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} ((BoundaryAbove x) ∷ []))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg (BoundaryAbove x) BoundaryAboveAll) ∷ [])
   =⟨⟩ 
      (BoundaryAbove x) <= BoundaryAboveAll 
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} ((BoundaryAbove x) ∷ [])
   end     
validRanges1 {{o}} {{dio}} ((BoundaryBelow x) ∷ []) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} ((BoundaryBelow x) ∷ []))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg (BoundaryBelow x) (BoundaryAboveAll)) ∷ [])
   =⟨⟩ 
      (BoundaryBelow x) <= BoundaryAboveAll
   =⟨⟩ 
      true       
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} ((BoundaryBelow x) ∷ [])
   end   

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ []) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (b1 ∷ b2 ∷ []))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ ranges1([]))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ [])      
   =⟨⟩ 
      (b1 <= b2)  
   =⟨ sym (prop_and_true (b1 <= b2)) ⟩ 
      ((b1 <= b2) && true)        
   =⟨⟩ 
      ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} []))        
   =⟨⟩    
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ [])
   end   

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs@(b3@(BoundaryBelow x) ∷ [])) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (ranges1 {{o}} {{dio}} bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && (validRangeList {{o}} {{dio}} []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ bs)
   end   

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs@(b3@(BoundaryAbove x) ∷ [])) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (ranges1 {{o}} {{dio}} bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && (validRangeList {{o}} {{dio}} []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 BoundaryAboveAll)) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= BoundaryAboveAll)) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ bs)
   end 

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs@(b3@(BoundaryBelowAll) ∷ [])) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (ranges1 {{o}} {{dio}} bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (Rg b3 (BoundaryAboveAll)) ∷ [])      
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && (validRangeList {{o}} {{dio}} []))
   =⟨⟩ 
      ((okAdjacent (Rg b1 b2) (Rg b3 (BoundaryAboveAll))) && true)
   =⟨⟩      
      (((b1 <= b2) && (b2 <= b3) && (b3 <= (BoundaryAboveAll))) && true)
   =⟨ prop_and_true ((b1 <= b2) && (b2 <= b3) && (b3 <= (BoundaryAboveAll))) ⟩ 
      ((b1 <= b2) && (b2 <= b3) && true)                        
   =⟨⟩       
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList {{o}} {{dio}} (b3 ∷ [])))        
   =⟨⟩    
       ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} (b2 ∷ b3 ∷ [])))        
   =⟨⟩     
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ bs)
   end 

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs@(b3@(BoundaryAboveAll) ∷ [])) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}}  (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (ranges1 {{o}} {{dio}}  bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}}  ((Rg b1 b2) ∷ [])      
   =⟨⟩ 
      (b1 <= b2)
   =⟨ sym (prop_and_true (b1 <= b2)) ⟩ 
      ((b1 <= b2) && true)
   =⟨⟩ 
      ((b1 <= b2) && (b2 <= b3))                     
   =⟨ sym (prop_and_true ((b1 <= b2) && (b2 <= b3))) ⟩       
      (((b1 <= b2) && (b2 <= b3)) && (validBoundaryList {{o}} {{dio}}  (b3 ∷ [])))        
   =⟨ prop_and_assoc (b1 <= b2) (b2 <= b3) (validBoundaryList {{o}} {{dio}}  (b3 ∷ [])) ⟩    
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList {{o}} {{dio}}  (b3 ∷ []))) 
   =⟨⟩    
      ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} (b2 ∷ b3 ∷ []))) 
   =⟨⟩    
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ bs)      
   end 

validRanges1 {{o}} {{dio}} (b1 ∷ b2 ∷ bs@(b3 ∷ bss@(b4 ∷ bsss))) = 
   begin 
      validRangeList {{o}} {{dio}} (ranges1 {{o}} {{dio}}  (b1 ∷ b2 ∷ bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}} ((Rg b1 b2) ∷ (ranges1 {{o}} {{dio}}  bs))
   =⟨⟩ 
      validRangeList {{o}} {{dio}}  ((Rg b1 b2) ∷ (Rg b3 b4) ∷ (ranges1 {{o}} {{dio}} bsss))      
   =⟨⟩ 
      (okAdjacent (Rg b1 b2) (Rg b3 b4)) && validRangeList ((Rg b3 b4) ∷ (ranges1 {{o}} {{dio}} bsss))
   =⟨⟩ 
      (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) && (validRangeList ((Rg b3 b4) ∷ (ranges1 {{o}} {{dio}} bsss))))
   =⟨⟩ 
      (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) && (validRangeList (ranges1 {{o}} {{dio}} bs)))                    
   =⟨ cong (((b1 <= b2) && (b2 <= b3) && (b3 <= b4)) &&_) (validRanges1 {{o}} {{dio}} bs) ⟩       
      (((b1 <= b2) && ((b2 <= b3) && (b3 <= b4))) && (validBoundaryList {{o}} {{dio}} bs))      
   =⟨ prop_and_assoc (b1 <= b2) ((b2 <= b3) && (b3 <= b4)) (validBoundaryList {{o}} {{dio}} bs) ⟩    
      ((b1 <= b2) && (((b2 <= b3) && (b3 <= b4)) && (validBoundaryList {{o}} {{dio}} bs)))  
   =⟨ cong ((b1 <= b2) &&_) (prop_and_assoc (b2 <= b3) (b3 <= b4) (validBoundaryList {{o}} {{dio}} bs)) ⟩    
      ((b1 <= b2) && ((b2 <= b3) && (b3 <= b4) && (validBoundaryList {{o}} {{dio}} bs)))  
   =⟨⟩    
      ((b1 <= b2) && ((b2 <= b3) && (b3 <= b4) && (b3 <= b4 && (validBoundaryList {{o}} {{dio}} bss))))  
   =⟨ cong ((b1 <= b2) &&_) (cong (b2 <= b3 &&_) (prop_and_cancel (b3 <= b4))) ⟩   
      ((b1 <= b2) && (b2 <= b3) && (b3 <= b4) && (validBoundaryList {{o}} {{dio}} bss))  
   =⟨⟩   
      ((b1 <= b2) && (b2 <= b3) && (validBoundaryList {{o}} {{dio}} bs))  
   =⟨⟩ 
      ((b1 <= b2) && (validBoundaryList {{o}} {{dio}} (b2 ∷ bs)))  
   =⟨⟩ 
      validBoundaryList {{o}} {{dio}} (b1 ∷ b2 ∷ bs)      
   end 



validSetBounds : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (bs : List (Boundary a)) ->
           validBoundaryList (setBounds1 bs) ≡ validBoundaryList bs
validSetBounds {{o}} {{dio}} [] = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} [])
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} []
   end           

validSetBounds {{o}} {{dio}} bs@(BoundaryBelowAll ∷ []) = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} bs)
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} []
  =⟨⟩ 
   true   
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} bs  
   end   

validSetBounds {{o}} {{dio}} bs@(b0@(BoundaryBelowAll) ∷ bss@(b1 ∷ b2)) = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} bs)
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} bss
  =⟨⟩ 
    (true && (validBoundaryList {{o}} {{dio}} bss))
  =⟨ cong (_&& (validBoundaryList {{o}} {{dio}} bss)) (sym (BoundaryBelowAllSmaller {{o}} {{dio}} b1)) ⟩ 
    ((BoundaryBelowAll <= b1) && (validBoundaryList bss))    
  =⟨⟩ 
    validBoundaryList bs     
  end   

validSetBounds {{o}} {{dio}} bs@(b@(BoundaryBelow x) ∷ bss) = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} bs)
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end   

validSetBounds {{o}} {{dio}} bs@(b@(BoundaryAboveAll) ∷ bss) = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} bs)
  =⟨⟩ 
    validBoundaryList (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end  
validSetBounds {{o}} {{dio}} bs@(b@(BoundaryAbove x) ∷ bss) = 
  begin 
    validBoundaryList {{o}} {{dio}} (setBounds1 {{o}} {{dio}} bs)
  =⟨⟩ 
    validBoundaryList {{o}} {{dio}} (BoundaryBelowAll ∷ bs)
  =⟨⟩ 
    ((BoundaryBelowAll <= b) && (validBoundaryList bs)) 
  =⟨⟩ 
    (true && (validBoundaryList bs))   
  =⟨⟩ 
    (validBoundaryList bs)             
   end  


{-# TERMINATING #-}
valid : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) 
   -> {IsTrue (validRangeList (rSetRanges rs))}
   -> (validRangeList (rSetRanges rs)) ≡ (validBoundaryList (bounds1 (rSetRanges rs)))
valid {{o}} {{dio}} rs@(RS []) {_} = 
  begin 
     validRangeList {{o}} {{dio}} (rSetRanges rs)
  =⟨⟩ 
    validRangeList {{o}} {{dio}} []
  =⟨⟩
    true
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} []
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} [])
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} (rSetRanges rs))
  end  
valid {{o}} {{dio}} rs@(RS (r ∷ [])) {_} = 
  begin 
     validRangeList {{o}} {{dio}} (rSetRanges rs)
  =⟨⟩ 
     validRangeList {{o}} {{dio}} (r ∷ [])
  =⟨⟩
    ((rangeLower {{dio}} r) <= (rangeUpper {{dio}} r))
  =⟨ sym (prop_and_true ((rangeLower {{dio}} r) <= (rangeUpper {{dio}} r))) ⟩
    (((rangeLower {{dio}} r) <= (rangeUpper {{dio}} r)) && true)    
  =⟨⟩  
    (((rangeLower {{dio}} r) <= (rangeUpper {{dio}} r)) && (validBoundaryList {{o}} {{dio}} []))    
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} ((rangeLower {{dio}} r) ∷ (rangeUpper {{dio}} r) ∷ [])
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} (r ∷ []))
  =⟨⟩  
    validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} (rSetRanges rs))
  end  

valid {{o}} {{dio}} rs@(RS ranges@(r@(Rg l1 u1) ∷ r1@(r2@(Rg l2 u2) ∷ rss))) {prf} = 
  begin 
     validRangeList {{o}} {{dio}} (rSetRanges rs)
  =⟨⟩ 
     validRangeList {{o}} {{dio}} (r ∷ (r2 ∷ rss))
  =⟨⟩ 
     ((okAdjacent r r2) && (validRangeList {{o}} {{dio}} r1))   
  =⟨⟩
    ((l1 <= u1 && (u1 <= l2 && l2 <= u2)) && (validRangeList {{o}} {{dio}} r1))
  =⟨ cong ((l1 <= u1 && u1 <= l2 && l2 <= u2) &&_) (valid {{o}} {{dio}} (RS r1 {headandtail rs prf}) {headandtail rs prf}) ⟩  
     ((l1 <= u1 && (u1 <= l2 && l2 <= u2)) && (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} r1)))
  =⟨ prop_and_assoc (l1 <= u1) (u1 <= l2 && l2 <= u2) (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} r1)) ⟩  
    (l1 <= u1 && ((u1 <= l2  && l2 <= u2) && (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} r1))))
  =⟨ cong (l1 <= u1 &&_) (prop_and_assoc (u1 <= l2) (l2 <= u2) (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} r1))) ⟩       
    (l1 <= u1 && u1 <= l2  && (l2 <= u2  && (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} r1))))
  =⟨⟩       
    (l1 <= u1 && u1 <= l2  && (l2 <= u2  
         && (validBoundaryList {{o}} {{dio}} ((rangeLower {{dio}} r2) ∷ (rangeUpper {{dio}} r2) ∷ (bounds1 {{o}} {{dio}} rss)))))       
  =⟨⟩       
    (l1 <= u1 && u1 <= l2 && l2 <= u2 && l2 <= u2 
         && (validBoundaryList {{o}} {{dio}} ((rangeUpper {{dio}} r2) ∷ (bounds1 {{o}} {{dio}} rss))))    
  =⟨ cong (l1 <= u1 &&_) (cong (u1 <= l2 &&_) (prop_and_cancel (l2 <= u2))) ⟩       
    (l1 <= u1 && u1 <= l2 && ((l2 <= u2) && (validBoundaryList {{o}} {{dio}} (u2 ∷ (bounds1 {{o}} {{dio}} rss)))))   
  =⟨⟩       
    (l1 <= u1 && u1 <= l2 && (validBoundaryList {{o}} {{dio}} (l2 ∷ (u2 ∷ (bounds1 {{o}} {{dio}} rss))))) 
  =⟨⟩       
    (l1 <= u1 && (validBoundaryList {{o}} {{dio}} (u1 ∷ l2 ∷ u2 ∷ (bounds1 {{o}} {{dio}} rss)))) 
  =⟨⟩ 
   (validBoundaryList {{o}} {{dio}} (l1 ∷ u1 ∷ l2 ∷ u2 ∷ (bounds1 {{o}} {{dio}} rss)))    
  =⟨⟩ 
   (validBoundaryList {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))                   
  end 

-- proofs that the invariant holds
subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

-- isTrue&&₂ : {x y : Bool} -> IsTrue (x && y) -> IsTrue y
-- isTrue&&₂ {true} p = p
-- isTrue&&₂ {false} ()

-- headandtail0 : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a }} -> (rs : RSet a) 
--       -> {{ne : NonEmpty (rSetRanges rs)}} -> (IsTrue (validRangeList (rSetRanges rs))) 
--       -> (IsTrue (validRangeList (tail (rSetRanges rs) {{ne}})))
-- headandtail0 rs@(RS (r ∷ [])) prf = IsTrue.itsTrue
-- headandtail0 rs@(RS (r ∷ rss)) prf = isTrue&&₂ prf

prop0 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> 
         IsTrue (validRangeList (rSetRanges rs)) -> IsTrue (validBoundaryList (bounds1 (rSetRanges rs)))
prop0 {{o}} {{dio}} rs prf = subst IsTrue (valid {{o}} {{dio}} rs {prf})  prf 

prop1 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (bs : List (Boundary a)) ->
           IsTrue (validBoundaryList bs) -> IsTrue (validBoundaryList (setBounds1 bs))  
prop1 {{o}} {{dio}} bs prf = subst IsTrue (sym (validSetBounds {{o}} {{dio}} bs)) prf 

prop2 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (bs : List (Boundary a)) ->
           IsTrue (validBoundaryList bs) -> IsTrue (validRangeList (ranges1 bs))  
prop2 {{o}} {{dio}} bs prf = subst IsTrue (sym (validRanges1 {{o}} {{dio}} bs)) prf

prop3 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> 
         IsTrue (validRangeList (rSetRanges rs)) 
         -> validRangeList (rSetRanges rs) ≡ validBoundaryList (setBounds1 (bounds1 (rSetRanges rs)))
prop3 {{o}} {{dio}} rs prf = trans (valid {{o}} {{dio}} rs {prf}) (sym (validSetBounds {{o}} {{dio}} (bounds1 (rSetRanges rs))))         

prop4 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> 
         IsTrue (validRangeList (rSetRanges rs)) 
         -> validRangeList (rSetRanges rs) ≡ validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))
prop4 {{o}} {{dio}} rs prf = trans (prop3 {{o}} {{dio}} rs prf) (sym (validRanges1 {{o}} {{dio}} (setBounds1 (bounds1 (rSetRanges rs)))))         

negation : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a)
      -> (IsTrue (validRangeList (rSetRanges rs))) -> (IsTrue (validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))))
negation {{o}} {{dio}} rs prf = subst IsTrue (prop4 {{o}} {{dio}} rs prf) prf      

-- empty range is valid
emptyRangeValid : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (validRangeList {{o}} {{dio}} []) ≡ true
emptyRangeValid = refl 
empty : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> IsTrue (validRangeList {{o}} {{dio}} [])
empty {{o}} {{dio}} = subst IsTrue (sym (emptyRangeValid {{o}} {{dio}})) IsTrue.itsTrue

-- full range is valid 
fullRangeValid : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> 
      (validRangeList {{o}} {{dio}} (fullRange {{o}} {{dio}} ∷ [])) ≡ true
fullRangeValid {{o}} {{dio}} = 
  begin 
     validRangeList {{o}} {{dio}} (fullRange {{o}} {{dio}} ∷ [])
  =⟨⟩ 
    ((rangeLower (fullRange {{o}} {{dio}})) <= (rangeUpper (fullRange {{o}} {{dio}}))) 
  =⟨⟩  
    true
  end  

full0 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> 
      IsTrue (validRangeList {{o}} {{dio}} ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []))
full0 {{o}} {{dio}} = subst IsTrue (sym (fullRangeValid {{o}} {{dio}})) IsTrue.itsTrue

-- any singleton range is valid
singletonRangeValid0 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (x : a) -> (validRangeList ((singletonRange x) ∷ [])) ≡ true
singletonRangeValid0 {{o}} {{dio}} x = 
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
singletonRangeValid : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (x : a) -> IsTrue (validRangeList ((singletonRange x) ∷ [])) 
singletonRangeValid x = subst IsTrue (sym (singletonRangeValid0 x)) IsTrue.itsTrue


rSingleton : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> a -> RSet a
rSingleton {{o}} {{dio}} a = RS ((singletonRange a) ∷ []) {singletonRangeValid a}

rangesAreEmpty : ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → List (Range a) -> Bool
rangesAreEmpty [] = true 
rangesAreEmpty (r ∷ rs) = (rangeIsEmpty r) && (rangesAreEmpty rs)

rSetIsEmpty : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a }} -> (rs : RSet a) -> Bool
rSetIsEmpty {{o}} {{dio}} rset@(RS ranges) = rangesAreEmpty {{o}} {{dio}} ranges

rSetNegation : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rg : RSet a) -> {(IsTrue (validRangeList (rSetRanges rg)))} -> RSet a
rSetNegation {{o}} {{dio}} set@(RS ranges) {prf} = 
   RS {{o}} {{dio}} (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))) {negation set prf}

rSetIsFull : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) 
      -> {IsTrue (validRangeList (rSetRanges rs))} -> Bool
rSetIsFull set {prf} = rSetIsEmpty (rSetNegation set {prf}) 

rSetEmpty : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> RSet a
rSetEmpty {{o}} {{dio}} = RS [] {empty {{o}} {{dio}}} 

rSetFull : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> RSet a
rSetFull {{o}} {{dio}} = RS ((Rg BoundaryBelowAll BoundaryAboveAll) ∷ []) {full0 {{o}} {{dio}}}

rSetHas : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> a -> Bool
rSetHas (RS []) _ = false
rSetHas {{o}} {{dio}} (RS ls@(r ∷ [])) value = rangeHas {{o}} r value 
rSetHas {{o}} {{dio}} (RS ls@(r ∷ rs)) value = or $ map (λ r -> (rangeHas {{o}} r value)) ls
-- rSetHas (RS ls@(r ∷ rs)) value = if_then_else_ (value />/ (rangeLower r)) ((rangeHas r value) || (rSetHas (RS rs) value)) false

_-?-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a) -> a -> Bool
_-?-_ rs = rSetHas rs 

postulate
      -- TO PROVE
      unionn : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs1 : RSet a) -> (rs2 : RSet a)
         -> IsTrue (validRangeList (rSetRanges rs1)) -> IsTrue (validRangeList (rSetRanges rs2))
         -> IsTrue (validRangeList (normalise (merge1 (rSetRanges rs1) (rSetRanges rs2))))

negationHelper : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a)
         -> {tr0 : IsTrue (validRangeList (rSetRanges rs))}
         -> validRangeList (rSetRanges (rSetNegation rs {tr0})) ≡ validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs))))
negationHelper {{o}} {{dio}} rs@(RS ranges) {prf} =   
  begin 
     validRangeList (rSetRanges (rSetNegation rs {prf})) 
  =⟨⟩ 
     validRangeList (rSetRanges (RS {{o}} {{dio}} (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges))) {negation rs prf}))
  =⟨⟩
    validRangeList (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} ranges)))
  =⟨⟩  
    validRangeList (ranges1 {{o}} {{dio}} (setBounds1 {{o}} {{dio}} (bounds1 {{o}} {{dio}} (rSetRanges rs))))
  end  

negation2 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (rs : RSet a)
         -> {tr0 : IsTrue (validRangeList (rSetRanges rs))}
         -> (tr : IsTrue (validRangeList (ranges1 (setBounds1 (bounds1 (rSetRanges rs)))))) 
         -> IsTrue (validRangeList (rSetRanges (rSetNegation rs {tr0})))
negation2 rs {prf0} prf = subst IsTrue (sym (negationHelper rs {prf0})) prf


rSetUnion : {{o : Ord a}} -> {{dio : DiscreteOrdered a}}
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
rSetUnion r1@(RS []) r2@(RS ls2@(h ∷ t)) = r2
rSetUnion r1@(RS ls1@(h ∷ t)) r2@(RS []) = r1
rSetUnion {{o}} {{dio}} r1@(RS []) r2@(RS []) = RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}
rSetUnion {{o}} {{dio}} r1@(RS ls1@(r0 ∷ rs1)) {prf1} r2@(RS ls2@(r ∷ rs2)) {prf2} = 
   RS {{o}} {{dio}} (normalise {{o}} {{dio}} (merge1 {{o}} {{dio}} ls1 ls2)) {unionn r1 r2 prf1 prf2}

_-\/-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}}
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
_-\/-_ rs1 {prf1} rs2 {prf2} = rSetUnion rs1 {prf1} rs2 {prf2}

rSetIntersection : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
-- rSetIntersection {{o}} {{dio}} (RS []) (RS ls2@(h ∷ t)) = RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}
-- rSetIntersection {{o}} {{dio}} (RS ls1@(h ∷ t)) (RS []) = RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}
-- rSetIntersection {{o}} {{dio}} (RS []) (RS []) = RS {{o}} {{dio}} [] {empty {{o}} {{dio}}}
rSetIntersection {{o}} {{dio}} rs1@(RS ls1) {prf1} rs2@(RS ls2) {prf2} =
    RS {{o}} {{dio}} 
      (filter (λ x -> rangeIsEmpty {{o}} {{dio}} x == false) (merge2 {{o}} {{dio}} ls1 ls2)) 
         {intersection0 rs1 rs2 prf1 prf2}


_-/\-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
_-/\-_ rs1 {prf1} rs2 {prf2} = rSetIntersection rs1 {prf1} rs2 {prf2}


rSetDifference : {{o : Ord a}} -> {{dio : DiscreteOrdered a}}
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
rSetDifference {{o}} {{dio}} rs1 {prf1} rs2 {prf2} = 
   rSetIntersection rs1 {prf1} (rSetNegation rs2 {prf2}) {negation2 rs2 (negation rs2 prf2)}

_-!-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> RSet a
_-!-_ rs1 {prf1} rs2 {prf2} = rSetDifference rs1 {prf1} rs2 {prf2}


rSetIsSubset : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> Bool
rSetIsSubset rs1 {prf1} rs2 {prf2} = rSetIsEmpty (rSetDifference rs1 {prf1} rs2 {prf2})

_-<=-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> Bool
_-<=-_ rs1 {prf1} rs2 {prf2}  = rSetIsSubset rs1 {prf1} rs2 {prf2} 

rSetIsSubsetStrict : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> Bool
rSetIsSubsetStrict rs1 {prf1} rs2 {prf2} = rSetIsEmpty 
   (rSetDifference rs1 {prf1} rs2 {prf2}) && not (rSetIsEmpty (rSetDifference rs2 {prf2} rs1 {prf1}))

_-<-_ : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} 
      -> (rs1 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs1))} 
      -> (rs2 : RSet a) -> {IsTrue (validRangeList (rSetRanges rs2))} -> Bool
_-<-_ rs1 {prf1} rs2 {prf2} = rSetIsSubsetStrict rs1 {prf1} rs2 {prf2}

-- instance 
--     isRangedSetSemigroup : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> Semigroup (RSet a) 
--     isRangedSetSemigroup ._<>_ r1@(RS l1 {prf1}) r2@(RS l2 {prf2}) = rSetUnion r1 {prf1} r2 {prf2}

--     isRangedSetMonoid : {{Ord a}} -> {{DiscreteOrdered a}} -> Monoid (RSet a)
--     isRangedSetMonoid .mempty = rSetEmpty


postulate 
   unfold : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (bound : Boundary a) 
      -> (u : (Boundary a -> Boundary a)) -> (s : (Boundary a -> Maybe (Boundary a))) 
      -> IsTrue (validRangeList (normalise (ranges2 bound u s)))


rSetUnfold : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> Boundary a 
   -> (Boundary a -> Boundary a) -> (Boundary a -> Maybe (Boundary a)) -> RSet a
rSetUnfold {a} bound upperFunc succFunc = RS (normalise (ranges2 bound upperFunc succFunc)) {unfold bound upperFunc succFunc}

   
      
