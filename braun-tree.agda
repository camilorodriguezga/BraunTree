open import Data.stlib.bt-bool

module Data.braun-tree{ℓ} (A : Set ℓ) (_<A_ : A → A → 𝔹) where

open import Data.stlib.bt-bool-thms
open import Data.stlib.bt-eq
open import Data.stlib.bt-nat
open import Data.stlib.bt-nat-thms
open import Data.stlib.bt-product
open import Data.stlib.bt-sum

-- the index n is the size of the tree (number of elements of type A)
data BraunTree : (n : ℕ) → Set ℓ where
  bt-empty : BraunTree 0
  bt-node : ∀ {n m : ℕ} → 
            A → BraunTree n → BraunTree m → 
            n ≡ m ∨ n ≡ suc m → 
            BraunTree (suc (n + m))


{- we will keep smaller (_<A_) elements closer to the root of the Braun tree as we insert -}
btInsert : ∀ {n : ℕ} → A → BraunTree n → BraunTree (suc n)

btInsert a bt-empty = bt-node a bt-empty bt-empty (inj₁ refl)

btInsert a (bt-node{n}{m} a' l r p) 
  rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
btInsert a (bt-node{n}{m} a' l r _) | inj₁ p | (a1 , a2) 
  rewrite p = (bt-node a1 (btInsert a2 r) l (inj₂ refl))
btInsert a (bt-node{n}{m} a' l r _) | inj₂ p | (a1 , a2) = 
  (bt-node a1 (btInsert a2 r) l (inj₁ (sym p)))


btReplaceMin : ∀{n : ℕ} → A → BraunTree (suc n) → BraunTree (suc n)
btReplaceMin a (bt-node _ bt-empty bt-empty u) = (bt-node a bt-empty bt-empty u)
btReplaceMin a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₁ ()))
btReplaceMin a (bt-node _ bt-empty (bt-node _ _ _ _) (inj₂ ()))
btReplaceMin a (bt-node _ (bt-node _ _ _ _) bt-empty (inj₁ ()))
btReplaceMin a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) with a <A x
btReplaceMin a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | tt = (bt-node a (bt-node x l r u) bt-empty (inj₂ y))
btReplaceMin a (bt-node a' (bt-node x l r u) bt-empty (inj₂ y)) | ff = 
 (bt-node x (btReplaceMin a (bt-node x l r u)) bt-empty (inj₂ y))
btReplaceMin a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) with a <A x && a <A x' 
btReplaceMin a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | tt = 
 (bt-node a (bt-node x l r u) (bt-node x' l' r' u') v)
btReplaceMin a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff with x <A x'  
btReplaceMin a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | tt = 
 (bt-node x (btReplaceMin a (bt-node x l r u)) (bt-node x' l' r' u') v)
btReplaceMin a (bt-node a' (bt-node x l r u) (bt-node x' l' r' u') v) | ff | ff = 
 (bt-node x' (bt-node x l r u) (btReplaceMin a (bt-node x' l' r' u')) v)
 

{- thanks to Matías Giovannini for the excellent post
     http://alaska-kamtchatka.blogspot.com/2010/02/braun-trees.html
   explaining how to do delete -}
btDeleteMin : ∀ {p : ℕ} → BraunTree (suc p) → BraunTree p
btDeleteMin (bt-node a bt-empty bt-empty u) = bt-empty
btDeleteMin (bt-node a bt-empty (bt-node _ _ _ _) (inj₁ ()))
btDeleteMin (bt-node a bt-empty (bt-node _ _ _ _) (inj₂ ()))
btDeleteMin (bt-node a (bt-node{n'}{m'} a' l' r' u') bt-empty u) rewrite +0 (n' + m') = bt-node a' l' r' u'
btDeleteMin (bt-node a
                (bt-node{n}{m} x l1 r1 u1)
                (bt-node{n'}{m'} x' l2 r2 u2) u) 
  rewrite +suc(n + m)(n' + m') | +suc n (m + (n' + m')) 
        | +comm(n + m)(n' + m') = 
  if (x <A x') then
    (bt-node x (bt-node x' l2 r2 u2)
      (btDeleteMin (bt-node x l1 r1 u1)) (lem{n}{m}{n'}{m'} u))
  else
    (bt-node x' (btReplaceMin x (bt-node x' l2 r2 u2))
      (btDeleteMin (bt-node x l1 r1 u1)) (lem{n}{m}{n'}{m'} u))
  where lem : {n m n' m' : ℕ} → suc (n + m) ≡ suc (n' + m') ∨ suc (n + m) ≡ suc (suc (n' + m')) → 
              suc (n' + m') ≡ n + m ∨ suc (n' + m') ≡ suc (n + m)
        lem{n}{m}{n'}{m'} (inj₁ x) = inj₂ (sym x)
        lem (inj₂ y) = inj₁ (sym (suc-inj y))

btRemoveMin : ∀ {p : ℕ} → BraunTree (suc p) → A × BraunTree p
btRemoveMin (bt-node a l r u) = a , btDeleteMin (bt-node a l r u)
