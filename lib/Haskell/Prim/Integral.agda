module Haskell.Prim.Integral where

open import Haskell.Prim
open import Haskell.Prim.Ord
open import Haskell.Prim.Enum
open import Haskell.Prim.Num
open import Haskell.Prim.Eq
open import Haskell.Prim.Int
open import Haskell.Prim.Integer

-- infixr 8  _^_ _^^_
-- infixl 7  _/_ _`quot`_ _`rem`_ _`div`_ _`mod`_
-- infixl 7  _%_

data Ratio (a : Set) : Set where
    _:%_ : a -> a -> Ratio a


record Integral (a : Set) : Set where
  field
    toInteger : a -> Integer
    

open Integral ⦃ ... ⦄ public

instance
    isIntegralInt : Integral Int
    isIntegralInt . toInteger n = intToInteger n

infinity : Ratio Integer
notANumber : Ratio Integer
infinity   = (toInteger 1) :% (toInteger 0)
notANumber = (toInteger 0) :% (toInteger 0)

-- _%_ : {{Integral a}} -> a -> a -> Ratio a

numerator : Ratio a -> a

denominator : Ratio a -> a

-- reduce : {{Integral a}} -> a -> a -> Ratio a

numerator (x :% _) =  x
denominator (_ :% y) =  y