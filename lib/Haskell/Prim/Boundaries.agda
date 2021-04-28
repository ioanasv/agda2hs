module Haskell.Prim.Boundaries where

open import Agda.Builtin.Nat as Nat hiding (_==_; _<_; _+_; _-_)
open import Agda.Builtin.Char
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Enum
open import Haskell.Prim.Num
open import Haskell.Prim.Eq
open import Haskell.Prim.Functor
open import Haskell.Prim.Monoid
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative
open import Haskell.Prim.Int
open import Haskell.Prim.List
open import Haskell.Prim.Integer
open import Haskell.Prim.Tuple
open import Haskell.Prim.Double
open import Haskell.Prim.Bounded

open import Agda.Builtin.Char

record DiscreteOrdered (a : Set) : Set where
    field
        adjacent : a -> a -> Bool
        adjacentBelow : a -> Maybe a


open DiscreteOrdered ⦃ ... ⦄ public

orderingToInteger : Ordering -> Integer
orderingToInteger LT = intToInteger 0
orderingToInteger EQ = intToInteger 1
orderingToInteger GT = intToInteger 2

orderingFromInteger : Integer -> Ordering
orderingFromInteger (pos 0) = LT
orderingFromInteger (pos 1) = EQ
orderingFromInteger _       = GT


-- boundedBelow : {{Ord a}} -> {{BoundedBelow a}} -> {{e : Enum a}} -> (x : a)
--      → {{ IfBoundedBelow (BoundedBelowEnum {{e}}) (IsFalse (fromEnum x == fromEnum minBound)) }} 
--      -> Maybe a
-- boundedBelow x  = if_then_else_ (x == minBound) Nothing (Just $ pred x)

-- boundedAdjacent : {{Ord a}} -> {{e : Enum a}} → (x : a) -> (y : a)
--      → {{ IfBoundedAbove (BoundedAboveEnum {{e}}) (IsFalse (fromEnum x == fromEnum maxBound)) }}  -> Bool
-- boundedAdjacent x y = if_then_else_ (x < y) (succ x == y) false

-- enumAdjacent : {{Ord a}} -> {{e : Enum a}} -> {{ IfBoundedAbove (BoundedAboveEnum {{e}}) (IsFalse (fromEnum a == fromEnum maxBound)) }} -> a -> a -> Bool
-- enumAdjacent x y = (succ x == y)

boundedAdjacentBool : (x y : Bool) -> Bool
boundedAdjacentBool x y = if_then_else_ (x < y) true false

boundedBelowBool : (x : Bool) -> Maybe Bool
boundedBelowBool x = if_then_else_ (x == false) Nothing (Just false)

boundedAdjacentOrdering : (x y : Ordering) -> Bool
boundedAdjacentOrdering x y = if_then_else_ (x < y && x < GT) ((orderingToInteger x) + (intToInteger 1) == (orderingToInteger y)) false

boundedBelowOrdering : (x : Ordering) -> Maybe Ordering
boundedBelowOrdering x = if_then_else_ (x == LT) Nothing (Just (orderingFromInteger ((orderingToInteger x) - (intToInteger 1))))

boundedAdjacentChar : (x y : Char) -> Bool
boundedAdjacentChar x y = if_then_else_ (x < y && x /= '\1114111') (((primCharToNat x) + 1) == primCharToNat y) false

boundedBelowChar : (x : Char) -> Maybe Char
boundedBelowChar x = if_then_else_ (x == '\0') Nothing (Just (primNatToChar (Nat._-_ (primCharToNat x) 1)))

boundedAdjacentInt : (x y : Int) -> Bool
boundedAdjacentInt x y = if_then_else_ (x < y && x /= 9223372036854775807) (x + 1 == y) false

boundedBelowInt : (x : Int) -> Maybe Int
boundedBelowInt x = if_then_else_ (x == -9223372036854775808) Nothing (Just (x - 1))

boundedAdjacentInteger : (x y : Integer) -> Bool
boundedAdjacentInteger x y = ((fromEnum x) + 1 == (fromEnum y))

boundedBelowInteger : (x : Integer) -> Maybe Integer
boundedBelowInteger x = Just (x - (intToInteger 1))

constructTuple : ⦃ Ord a ⦄ → {{DiscreteOrdered b}} -> a -> Maybe b -> Maybe (a × b)
constructTuple _ Nothing = Nothing
constructTuple a (Just value) = Just (a , value)

constructTriple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ -> {{DiscreteOrdered c}} -> a -> b -> Maybe c -> Maybe (a × b × c)
constructTriple _ _ Nothing = Nothing
constructTriple a b (Just value) = Just (a , b , value)

constructQuadtruple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ -> {{ Ord c }} -> {{DiscreteOrdered d}} -> a -> b -> c -> Maybe d -> Maybe (a × b × c × d)
constructQuadtruple _ _ _ Nothing = Nothing
constructQuadtruple a b c (Just value) = Just (a , b , c , value)

instance
    isDiscreteOrderedBool : DiscreteOrdered Bool
    isDiscreteOrderedBool . adjacent = boundedAdjacentBool
    isDiscreteOrderedBool . adjacentBelow = boundedBelowBool

    isDiscreteOrderedOrdering : DiscreteOrdered Ordering
    isDiscreteOrderedOrdering . adjacent = boundedAdjacentOrdering
    isDiscreteOrderedOrdering . adjacentBelow = boundedBelowOrdering

    isDiscreteOrderedChar : DiscreteOrdered Char
    isDiscreteOrderedChar . adjacent = boundedAdjacentChar
    isDiscreteOrderedChar . adjacentBelow = boundedBelowChar

    isDiscreteOrderedInt : DiscreteOrdered Int
    isDiscreteOrderedInt . adjacent = boundedAdjacentInt
    isDiscreteOrderedInt . adjacentBelow = boundedBelowInt

    isDiscreteOrderedInteger : DiscreteOrdered Integer
    isDiscreteOrderedInteger . adjacent = boundedAdjacentInteger
    isDiscreteOrderedInteger . adjacentBelow = boundedBelowInteger

    isDiscreteOrderedDouble : DiscreteOrdered Double
    isDiscreteOrderedDouble . adjacent x y = false
    isDiscreteOrderedDouble . adjacentBelow x = Nothing

    isDiscreteOrderedList : ⦃ Ord a ⦄ → DiscreteOrdered (List a)
    isDiscreteOrderedList . adjacent x y = false
    isDiscreteOrderedList . adjacentBelow x = Nothing

    isDiscreteOrderedTuple : ⦃ Ord a ⦄ → {{DiscreteOrdered b}} → DiscreteOrdered (a × b)
    isDiscreteOrderedTuple . adjacent (x1 , x2) (y1 , y2) = (x1 == y1) && (adjacent x2 y2)
    isDiscreteOrderedTuple . adjacentBelow (x1 , x2) = constructTuple x1 (adjacentBelow x2)

    isDiscreteOrderedTriple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ → {{DiscreteOrdered c}} → DiscreteOrdered (a × b × c)
    isDiscreteOrderedTriple . adjacent (x1 , x2 , x3) (y1 , y2 , y3) = (x1 == y1) && (x2 == y2) && (adjacent x3 y3)
    isDiscreteOrderedTriple . adjacentBelow (x1 , x2 , x3) = constructTriple x1 x2 (adjacentBelow x3)

    isDiscreteOrderedQuadtruple : ⦃ Ord a ⦄ → ⦃ Ord b ⦄ -> {{ Ord c }} → {{DiscreteOrdered d}} → DiscreteOrdered (a × b × c × d)
    isDiscreteOrderedQuadtruple . adjacent (x1 , x2 , x3 , x4) (y1 , y2 , y3 , y4) = (x1 == y1) && (x2 == y2) && (x3 == y3) && (adjacent x4 y4)
    isDiscreteOrderedQuadtruple . adjacentBelow (x1 , x2 , x3 , x4) = constructQuadtruple x1 x2 x3 (adjacentBelow x4)

data Boundary (a : Set) : Set where
    BoundaryAbove    : a -> Boundary a
    BoundaryBelow    : a -> Boundary a
    BoundaryAboveAll : Boundary a
    BoundaryBelowAll : Boundary a

above : {{ Ord a }} -> Boundary a -> a -> Bool
above (BoundaryAbove b) a    = a > b
above (BoundaryBelow b) a    = a >= b
above BoundaryAboveAll _     = false
above BoundaryBelowAll _     = true


infixr 4 _/>/_
_/>/_ : {{ Ord a }} -> a -> Boundary a -> Bool
_/>/_ a (BoundaryAbove b) = a > b
_/>/_ a (BoundaryBelow b) = a >= b
_/>/_ _ BoundaryAboveAll = false
_/>/_ _ BoundaryBelowAll = true


instance
    isBoundaryEq : ⦃ Ord a ⦄ -> ⦃ DiscreteOrdered a ⦄ → Eq (Boundary a)
    isBoundaryEq . _==_ (BoundaryAbove b1) (BoundaryAbove b2) = (b1 == b2)
    isBoundaryEq . _==_ (BoundaryAbove b1) (BoundaryBelow b2) = if_then_else_ (b1 < b2 && (adjacent b1 b2)) true false
    isBoundaryEq . _==_ (BoundaryBelow b1) (BoundaryBelow b2) = (b1 == b2)
    isBoundaryEq . _==_ (BoundaryBelow b1) (BoundaryAbove b2) = if_then_else_ (b1 > b2 && (adjacent b2 b1)) true false
    isBoundaryEq . _==_ BoundaryAboveAll BoundaryAboveAll = true
    isBoundaryEq . _==_ BoundaryBelowAll BoundaryBelowAll = true
    isBoundaryEq . _==_ _ _ = false

    isBoundaryOrd : ⦃ Ord a ⦄ -> ⦃ DiscreteOrdered a ⦄ → Ord (Boundary a)
    isBoundaryOrd . compare (BoundaryAbove b1) (BoundaryAbove b2) = compare b1 b2
    isBoundaryOrd . compare (BoundaryAbove b1) (BoundaryBelow b2) = if_then_else_ (b1 < b2) (if_then_else_ (adjacent b1 b2) EQ LT) GT
    isBoundaryOrd . compare (BoundaryAbove b1) BoundaryAboveAll = LT
    isBoundaryOrd . compare (BoundaryAbove b1) BoundaryBelowAll = GT
    isBoundaryOrd . compare (BoundaryBelow b1) (BoundaryBelow b2) = compare b1 b2
    isBoundaryOrd . compare (BoundaryBelow b1) (BoundaryAbove b2) = if_then_else_ (b1 > b2) (if_then_else_ (adjacent b2 b1) EQ GT) LT
    isBoundaryOrd . compare (BoundaryBelow b1) BoundaryAboveAll = LT
    isBoundaryOrd . compare (BoundaryBelow b1) BoundaryBelowAll = GT
    isBoundaryOrd . compare BoundaryAboveAll BoundaryAboveAll = EQ
    isBoundaryOrd . compare BoundaryAboveAll _ = GT
    isBoundaryOrd . compare BoundaryBelowAll BoundaryBelowAll = EQ
    isBoundaryOrd . compare BoundaryBelowAll _ = LT
    isBoundaryOrd ._<_ x y = compare x y == LT
    isBoundaryOrd ._>_ x y = compare x y == GT
    isBoundaryOrd ._<=_ x y = (compare x y == LT) || (compare x y == EQ)
    isBoundaryOrd ._>=_ x y = (compare x y == GT) || (compare x y == EQ)
    isBoundaryOrd .max x y = if (compare x y == GT) then x else y
    isBoundaryOrd .min x y = if (compare x y == LT) then x else y
    
