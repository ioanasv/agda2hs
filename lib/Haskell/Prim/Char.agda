module Haskell.Prim.Char where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Char 
open import Agda.Builtin.Bool
open import Agda.Builtin.Int using (pos; negsuc)

open import Haskell.Prim
open import Haskell.Prim.Int
open import Haskell.Prim.Integer
open import Haskell.Prim.Enum
open import Haskell.Prim.Real

ord : Char -> Int
ord c = fromEnum ((pos ∘ primCharToNat) c)

chr1 : Integer -> Char 
chr1 (pos n) = primNatToChar n
chr1 _ = '_'

chr : Int -> Char 
chr n = chr1 (toInteger n)
