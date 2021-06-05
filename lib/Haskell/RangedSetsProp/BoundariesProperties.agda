module Haskell.RangedSetsProp.BoundariesProperties where

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

open import Haskell.RangedSets.Boundaries

prop_no_boundary_smaller : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a}} -> (r1 : Boundary a) -> (r1 < BoundaryBelowAll) ≡ false 
prop_no_boundary_smaller BoundaryBelowAll = refl
prop_no_boundary_smaller BoundaryAboveAll = refl
prop_no_boundary_smaller (BoundaryAbove x) = refl
prop_no_boundary_smaller (BoundaryBelow x) = refl

prop_no_boundary_greater : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a}} -> (r1 : Boundary a) -> (r1 > BoundaryAboveAll) ≡ false 
prop_no_boundary_greater BoundaryBelowAll = refl
prop_no_boundary_greater BoundaryAboveAll = refl
prop_no_boundary_greater (BoundaryAbove x) = refl
prop_no_boundary_greater (BoundaryBelow x) = refl

BoundaryBelowAllSmaller :  ⦃ o : Ord a ⦄ → ⦃ dio : DiscreteOrdered a ⦄ → (b : Boundary a)
      → (BoundaryBelowAll <= b) ≡ true
BoundaryBelowAllSmaller BoundaryBelowAll = refl
BoundaryBelowAllSmaller BoundaryAboveAll = refl
BoundaryBelowAllSmaller (BoundaryBelow _) = refl
BoundaryBelowAllSmaller (BoundaryAbove _)  = refl

postulate
  prop_max_sym : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a}} -> (r1 : Boundary a) -> (r2 : Boundary a) -> max r1 r2 ≡ max r2 r1 
  prop_min_sym : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a}} -> (r1 : Boundary a) -> (r2 : Boundary a) -> min r1 r2 ≡ min r2 r1 
  
-- prop_max_sym : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a}} -> (r1 : Boundary a) -> (r2 : Boundary a) -> max r1 r2 ≡ max r2 r1 
-- prop_max_sym {{o}} {{dio}} r1 r2 = 
--     begin
--         max r1 r2
--     =⟨⟩   
--         if (compare x y == GT) then x else y
--     =⟨⟩   
--         if (compare y x == GT) then y else x     
--     =⟨⟩ 
--         max r2 r1 
--     end            