module Haskell.RangedSetsProp.library where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.List
open import Haskell.RangedSets.Boundaries
open import Haskell.RangedSets.Ranges


-- symmetry of equality
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- transitivity of equality
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A}
       → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix   1  begin_
infix   3  _end
infixr  2  _=⟨_⟩_
infixr  2  _=⟨⟩_

propIf : {a b : Set} -> {x y : a} (f : a -> b) (c : Bool) -> f (if c then x else y) ≡ (if c then f x else f y)
propIf f false = refl
propIf f true = refl

propIf2 : {{Ord a}} -> {x y : a} (c : Bool) -> IsTrue c -> (if c then x else y) ≡ x
propIf2 true f = refl

propIf3 : {{Ord a}} -> {x y : a} (c : Bool) -> IsFalse c -> (if c then x else y) ≡ y
propIf3 false f = refl

propIf2' : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a }} ->  {x y : List (Range a)} (c : Bool) -> IsTrue c -> (if c then x else y) ≡ x
propIf2' true f = refl

propIf3' : {{ o : Ord a }} -> {{ dio : DiscreteOrdered a }} ->  {x y : List (Range a)} (c : Bool) -> IsFalse c -> (if c then x else y) ≡ y
propIf3' false f = refl

propIsFalse : (x : Bool) -> IsFalse x -> x ≡ false 
propIsFalse false f = refl

propIsTrue : (x : Bool) -> IsTrue x -> x ≡ true 
propIsTrue true f = refl


postulate 
   truth : ∀ {x y : Bool} -> (x ≡ y) -> {{IsTrue x}} -> y ≡ true
   truth2 : ∀ {x : Bool} -> IsTrue (not x) -> IsTrue (x == false)
   gteq : {{o : Ord a}} -> ∀ {x y : a} -> (x ≡ y) -> (_>=_ {{o}} x y) ≡ true

   lt : {{o : Ord a}} -> (x y : a) -> (x ≡ y) -> IsFalse (_>_ {{o}} x y) 

   lteq : {{o : Ord a}} -> (x y : a) -> (_<_ {{o}} x y) ≡ (_<=_ {{o}} x y)
   gt : {{o : Ord a}} -> ∀ {x y : a} -> (x ≡ y) -> not (_>_ {{o}} x y) ≡ true

   eq4 : {{o : Ord a}} -> ∀ {x y : a} -> (x ≡ y) -> ((compare x y) == EQ) ≡ true

   eq5 : {{o : Ord a}} -> ∀ {x y : a} -> (x ≡ y) -> IsTrue ((compare x y) == EQ)
   eq : (x : Bool) -> IsFalse x ≡ IsTrue (not x)
   eq00 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> ∀ {x y : (List (Range a))} -> (x ≡ y) -> IsTrue (x == y)
   eq0 : {{o : Ord a}} -> ∀ {x y : a} -> (x ≡ y) -> IsTrue (x == y)
   eq1 : {{o : Ord a}} -> (x y : a) -> ((_>=_ {{o}} x y) && (not (_>_ {{o}} x y))) ≡ (y == x)
   eq2 : {{o : Ord a}} -> (x y : a) -> not (_<=_ {{o}} x y) ≡ (_<_ {{o}} y x)
   eq3 : {{o : Ord a}} -> (x y i j : a) -> {{IsTrue ((_<_ {{o}} i x) && (_<_ {{o}} j y))}} -> ((min {{o}} x y) <= (max {{o}} i j)) ≡ ((_<=_ {{o}} x j) || (_<=_ {{o}} y i))
   boundaries0 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (x : a) -> (b c : Boundary a) -> ((x />/ b) && (x />/ c)) ≡ (x />/ (max b c))
   boundaries1 : {{o : Ord a}} -> {{dio : DiscreteOrdered a}} -> (x : a) -> (b c : Boundary a) -> ((x />/ b) || (x />/ c)) ≡ (x />/ (min b c))

prop_and_assoc : (a b c : Bool) -> ((a && b) && c) ≡ (a && (b && c))
prop_and_assoc true b c = 
   begin
     ((true && b) && c)
   =⟨⟩
     (b && c)
   =⟨⟩
     (true && (b && c))
   end
prop_and_assoc false b c = 
   begin
     ((false && b) && c)
   =⟨⟩
     (false && c)
   =⟨⟩
     false 
   =⟨⟩
     (false && (b && c))
   end

prop_and_cancel : (a : Bool) {b : Bool} -> (a && a && b) ≡ (a && b)
prop_and_cancel true = refl
prop_and_cancel false = refl

prop_or_assoc : (a b c : Bool) -> ((a || b) || c) ≡ (a || (b || c))
prop_or_assoc true b c = refl
prop_or_assoc false b c = refl

prop_or_sym : (a b : Bool) -> (a || b) ≡ (b || a)
prop_or_sym true true = refl
prop_or_sym true false = refl
prop_or_sym false true = refl
prop_or_sym false false = refl

prop_or_same_value : (a : Bool) -> (a || a) ≡ a
prop_or_same_value true = refl
prop_or_same_value false = refl

prop_and_false : (a : Bool) -> (a && false) ≡ false
prop_and_false true = refl
prop_and_false false = refl

prop_and_true : (a : Bool) -> (a && true) ≡ a
prop_and_true true = refl
prop_and_true false = refl

prop_or_false : (a : Bool) -> (false || a) ≡ a
prop_or_false true = refl
prop_or_false false = refl

prop_or_false2 : (a : Bool) ->  (a || false) ≡ a
prop_or_false2 true = refl
prop_or_false2 false = refl

prop_or_false3 : (a : Bool) ->  (a || true) ≡ true
prop_or_false3 true = refl
prop_or_false3 false = refl

prop_or_true : (a : Bool) -> (true || a) ≡ true
prop_or_true true = refl
prop_or_true false = refl

prop_and_comm : (a b : Bool) -> (a && b) ≡ (b && a)
prop_and_comm false b = 
   begin
     (false && b)
   =⟨⟩
     false 
   =⟨ sym (prop_and_false b) ⟩
     (b && false)
   end
prop_and_comm true b = 
   begin
     (true && b)
   =⟨⟩
     b 
   =⟨ sym (prop_and_true b) ⟩
     (b && true)
   end

prop_distr : (a b c : Bool) -> ((a || b) && c) ≡ ((a && c) || (b && c))
prop_distr true b true = refl
prop_distr true true false = refl
prop_distr true false false = refl
prop_distr false true true = refl
prop_distr false true false = refl 
prop_distr false false false = refl 
prop_distr false false true = refl 

prop_dnf : (a b c d : Bool) -> ((a || b) && (c || d)) ≡ ((a && c) || (b && d) || (b && c) || (a && d))
prop_dnf true b true d = refl 
prop_dnf true true false true = refl 
prop_dnf true false false true = refl 
prop_dnf true true false false = refl 
prop_dnf true false false false = refl 
prop_dnf false true true true = refl
prop_dnf false true false true = refl
prop_dnf false false true true = refl 
prop_dnf false false true false = refl 
prop_dnf false false false true = refl 
prop_dnf false false false false = refl 
prop_dnf false true true false = refl
prop_dnf false true false false = refl

prop_demorgan2 : (a b : Bool) -> ((not a) && (not b)) ≡ (not (a || b))
prop_demorgan2 false b = refl
prop_demorgan2 true b = refl

prop_demorgan : (a b : Bool) -> (not (a && b)) ≡ ((not a) || (not b))
prop_demorgan false b = refl
prop_demorgan true b = refl

not-not : (b : Bool) → b ≡ not (not b)
not-not false = refl

not-not true =
   begin
      not (not true)
     =⟨⟩ 
      not false
     =⟨⟩
     true
   end

demorgan3 : (a b c d : Bool) -> (not (a || b || c || d)) ≡ ((not a) && (not b) && (not c) && (not d))
demorgan3 true b c d = refl
demorgan3 false true c d = refl
demorgan3 false false true d = refl
demorgan3 false false false true = refl
demorgan3 false false false false = refl