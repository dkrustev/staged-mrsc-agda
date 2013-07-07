module Util where

open import Level
  using ()
open import Data.Nat
  hiding(_⊔_)
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty

open import Relation.Nullary
open import Relation.Unary
  using () renaming (Decidable to Decidable₁)

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import Algebra
  using (module CommutativeSemiring)

module *+ = CommutativeSemiring Data.Nat.Properties.commutativeSemiring


-- AnyV

AnyV : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
AnyV P xs = ∃ λ i → P (lookup i xs) 

-- anyV

anyV : ∀ {n a p} {A : Set a} {P : A → Set p} →
  Decidable₁ P → Decidable₁ (AnyV {n} P)

anyV {P = P} dp [] = no helper
  where helper : AnyV P [] → ⊥
        helper (() , _)

anyV {P = P} dp (x ∷ xs) with dp x
... | yes px = yes (zero , px)
... | no ¬px with anyV dp xs
... | yes (i , py) = yes (suc i , py)
... | no ¬ipy = no helper
  where helper : AnyV P (x ∷ xs) → ⊥
        helper (zero , px) = ¬px px
        helper (suc i , py) = ¬ipy (i , py)

-- VecAny

VecAny : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
VecAny P [] = Level.Lift ⊥
VecAny P (x ∷ xs) = P x ⊎ VecAny P xs

-- vecAny

vecAny : ∀ {n a ℓ} {A : Set a} {P : A → Set ℓ} →
  Decidable₁ P → Decidable₁ (VecAny {n} P)
vecAny dp [] = no Level.lower
vecAny dp (x ∷ xs) with dp x
... | yes dpx = yes (inj₁ dpx)
... | no ¬dpx with vecAny dp xs
... | yes dpxs = yes (inj₂ dpxs)
... | no ¬dpxs = no [ ¬dpx , ¬dpxs ]′

-- m+1+n≡1+m+n

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

-- m∸n+n≡m

m∸n+n≡m : (m n : ℕ) → n ≤ m → m ∸ n + n ≡ m
m∸n+n≡m m .0 z≤n = begin
  m ∸ 0 + 0
    ≡⟨⟩
  m + 0
    ≡⟨ proj₂ *+.+-identity m ⟩
  m
  ∎
  where open ≡-Reasoning
m∸n+n≡m .(suc n) .(suc m) (s≤s {m} {n} n≤m) = begin
  suc n ∸ suc m + suc m
    ≡⟨⟩
  n ∸ m + suc m
    ≡⟨ m+1+n≡1+m+n (n ∸ m) m ⟩
  suc (n ∸ m + m)
    ≡⟨ cong suc (m∸n+n≡m n m n≤m) ⟩
  suc n
  ∎
  where open ≡-Reasoning

-- Cartesian product

-- cartesian2

cartesian2 : ∀ {A : Set} → List A → List (List A) → List (List A)
cartesian2 [] yss = []
cartesian2 (x ∷ xs) yss = map (_∷_ x) yss ++ cartesian2 xs yss

-- cartesian

cartesian : ∀ {A : Set} (xss : List (List A)) → List (List A)
cartesian [] = [ [] ]
cartesian (xs ∷ xss) = cartesian2 xs (cartesian xss)

-- Cartesian product for vectors

-- vec-cartesian2

vec-cartesian2 : ∀ {k} {A : Set} → List A → List (Vec A k) →
  List (Vec A (suc k))

vec-cartesian2 [] yss = []
vec-cartesian2 (x ∷ xs) yss = map (_∷_ x) yss ++ vec-cartesian2 xs yss

-- vec-cartesian

vec-cartesian : ∀ {k} {A : Set} (xss : Vec (List A) k) → List (Vec A k)
vec-cartesian [] = [ [] ]
vec-cartesian (xs ∷ xss) = vec-cartesian2 xs (vec-cartesian xss)
