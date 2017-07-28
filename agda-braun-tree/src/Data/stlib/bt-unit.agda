module Data.stlib.bt-unit where

open import Data.stlib.bt-level
open import Data.stlib.bt-eq

data ⊤ : Set where
  triv : ⊤

{-# COMPILED_DATA ⊤ () ()  #-}

single-range : ∀{U : Set}{g : U → ⊤} → ∀{u : U} → g u ≡ triv
single-range {U}{g}{u} with g u
... | triv = refl
