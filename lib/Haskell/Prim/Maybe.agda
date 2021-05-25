
module Haskell.Prim.Maybe where

open import Agda.Builtin.List public

open import Haskell.Prim
open import Haskell.Prim.List

--------------------------------------------------
-- Maybe

data Maybe {ℓ} (a : Set ℓ) : Set ℓ where
  Nothing : Maybe a
  Just    : a -> Maybe a

maybe : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → b → (a → b) → Maybe a → b
maybe n j Nothing  = n
maybe n j (Just x) = j x

mapMaybe : (a -> Maybe b) -> List a -> List b 
mapMaybe _ [] = []
mapMaybe f (x ∷ xs) = 
  case f x of λ where
    Nothing -> mapMaybe f xs
    (Just v) -> v ∷ (mapMaybe f xs)