open import Data.stlib.bt-bool

module Data.braun-tree-simple where

open import Data.stlib.bt-bool-thms
open import Data.stlib.bt-eq
open import Data.stlib.bt-nat
open import Data.stlib.bt-nat-thms
open import Data.stlib.bt-product
open import Data.stlib.bt-sum

postulate
  A    : Set
  _<A_ : A → A → 𝔹 

data BraunTree : (n : ℕ) → Set where
  empty : BraunTree 0
  node  : ∀ {m n}
        → A → BraunTree m → BraunTree n
        → m ≡ n ∨ m ≡ suc n
        → BraunTree (suc (m + n))


{- we will keep smaller (_<A_) elements closer to the root of the Braun tree as we insert -}
btInsert : ∀ {n} → A → BraunTree n → BraunTree (suc n)
btInsert x empty = node x empty empty (inj₁ refl)
btInsert x (node{m}{n} y treeₗ treeᵣ p)
  rewrite +comm m n
  with    p        | if x <A y then (x , y) else (y , x)
...  | inj₁ m≡n    | (v₁ , v₂) = node v₁ (btInsert v₂ treeᵣ) treeₗ (inj₂ (cong suc (sym m≡n)))
...  | inj₂ m≡sucn | (v₁ , v₂) = node v₁ (btInsert v₂ treeᵣ) treeₗ (inj₁ (sym m≡sucn))
