module AlmostFullRel where

open import Level
  using ()

open import Data.Empty
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Binary
  using (Rel; _⇒_) renaming (Decidable to Decidable₂)
open import Function.Inverse as Inv
  using (_↔_; module Inverse)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)
import Relation.Binary.Sigma.Pointwise as Σ

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to P[_])

--
-- Almost-full relations
--

data Almost-full {ℓ} {A : Set ℓ} : Rel A ℓ → Set (Level.suc ℓ) where
  now   : ∀ {_≫_} → (z : ∀ x y → x ≫ y) →
               Almost-full _≫_
  later : ∀ {_≫_} → (s : ∀ c → Almost-full (λ x y → x ≫ y ⊎ c ≫ x)) →
               Almost-full _≫_

-- af-⇒

af-⇒ : 
  ∀ {ℓ} {A : Set ℓ} {P Q : Rel A ℓ} →
    (p⇒q : P ⇒ Q) →
    Almost-full P → Almost-full Q

af-⇒ p⇒q (now z) =
  now (λ x y → p⇒q (z x y))
af-⇒ p⇒q (later s) =
  later (λ c → af-⇒ (Sum.map p⇒q p⇒q) (s c))

-- af-⊎

af-⊎ : 
  ∀ {ℓ} {A : Set ℓ} {P Q : Rel A ℓ} →
    Almost-full P → Almost-full (λ x y → P x y ⊎ Q x y)
af-⊎ afP = af-⇒ inj₁ afP

-- af-×

{- The following has a complicated proof in the sources 
   for the "Stop when you are almost-full" paper -}
postulate 
  af-× : ∀ {ℓ} {A : Set ℓ} {P Q : Rel A ℓ} →
    Almost-full P → Almost-full Q → Almost-full (λ x y → P x y × Q x y)

--
-- Well-founded trees
--

data WFT {ℓ} (A  :  Set ℓ) : Set ℓ where 
  now   : WFT A
  later : (s : A → WFT A) → WFT A

--
-- _⟱_ (secure by)
-- The tree can be separated from the relation.
--
-- (This is a form of "staging", a wft being a "program" that
-- transforms a relation.)
--

infix 4 _⟱_

-- _⟱_

_⟱_ : ∀ {ℓ} {A : Set ℓ} (_≫_ : Rel A ℓ) (t :  WFT A) → Set ℓ
_≫_ ⟱ now = ∀ x y → x ≫ y
_≫_ ⟱ later g = ∀ c → (λ x y → x ≫ y ⊎ c ≫ x) ⟱ g c

-- Almost-full⟱

Almost-full⟱ : ∀ {ℓ} {A : Set ℓ} (R : Rel A ℓ) → Set ℓ
Almost-full⟱ {A = A} R = ∃ λ t → R ⟱ t

-- af⟱→af

af⟱→af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full⟱ R → Almost-full R

af⟱→af (now , R⟱) =
  now R⟱
af⟱→af (later s , R⟱) =
  later (λ c → af⟱→af (s c , R⟱ c))

-- af→af⟱

af→af⟱ : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full R → Almost-full⟱ R

af→af⟱ (now z) =
  now , z
af→af⟱ {R = R} (later s) =
  later (λ c → proj₁ (af→af⟱ (s c))) , (λ c → proj₂ (af→af⟱ (s c)))

-- af⟱⇔af

af⟱⇔af : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full⟱ R ⇔ Almost-full R

af⟱⇔af = equivalence af⟱→af af→af⟱


-- Given `Almost-full R`, we can extract the corresponding wft tree.

-- af⇒wft

wft : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → Almost-full R → WFT A

wft (now z) = now
wft (later s) = later (λ c → wft (s c))

-- af⇒wft is sound.

-- af⇒⟱

af⇒⟱ : ∀ {ℓ} {A : Set ℓ} {R : Rel A ℓ} → (af : Almost-full R) →
           R ⟱ (wft af)

af⇒⟱ (now z) = z
af⇒⟱ (later s) = λ c → af⇒⟱ (s c)

--
-- In some proofs there appear expressons of the form
--     f (af-⇒ p⇒q (s c))
-- so that the termination checker cannot see that the argument of f
-- is smaller than `(later s)` . But the function f is total, because
-- `wft (s c)` is smaller than `wft (s c)` and
--      wft (af-⇒ p⇒q (s c)) ≡ wft (s c)
-- This is made explicit in the signature of ⟱-⇒ ,
-- so that we can use induction on t, rather than on `Almost-full R` .

-- ⟱-⇒

⟱-⇒ :
  ∀ {ℓ} {A : Set ℓ} {P : Rel A ℓ} {Q : Rel A ℓ} 
    (p⇒q : P ⇒ Q) (t : WFT A) → P ⟱ t → Q ⟱ t

⟱-⇒ p⇒q now P⟱t =
  λ x y → p⇒q (P⟱t x y)

⟱-⇒ p⇒q (later s) P⟱t =
  λ c → ⟱-⇒ (Sum.map p⇒q p⇒q) (s c) (P⟱t c)

-- af-inverseImage

cofmap : ∀ {ℓ} {A B : Set ℓ} (f : B → A) (t : WFT A) → WFT B
cofmap f now = now
cofmap f (later s) = later (λ x → cofmap f (s (f x)))

cofmap⟱ : ∀ {ℓ} {A B : Set ℓ} (f : B → A) (t : WFT A) (R : Rel A ℓ) →
            R ⟱ t → (λ x y → R (f x) (f y)) ⟱ cofmap f t
cofmap⟱ f now R R⟱t = λ x y → R⟱t (f x) (f y)
cofmap⟱ f (later s) R R⟱t = λ c → 
  cofmap⟱ f (s (f c)) (λ x y → R x y ⊎ R (f c) x) (R⟱t (f c))

af-inverseImage : ∀ {ℓ} {A B : Set ℓ} {f : B → A} {R : Rel A ℓ} →
    Almost-full R → Almost-full (λ x y → R (f x) (f y))
af-inverseImage {f = f} {R = R} af =
  af⟱→af ((cofmap f (wft af)) , cofmap⟱ f (wft af) R (af⇒⟱ af))

-- af⇒wf

open import Induction.WellFounded

tr-clos : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) → Rel X ℓ
tr-clos R = _<⁺_
  where open Transitive-closure R

data TrClos1n {a} {A : Set a} (R : Rel A a) : Rel A a where
  step1n : ∀ x y → R x y → TrClos1n R x y
  trans1n : ∀ x y z → R x y → TrClos1n R y z → TrClos1n R x z

TrClos1n⇒tr-clos : ∀ {a} {A : Set a} (R : Rel A a) x y → TrClos1n R x y → tr-clos R x y
TrClos1n⇒tr-clos R x y (step1n .x .y x₁) = Transitive-closure.[ x₁ ]
TrClos1n⇒tr-clos R x y (trans1n .x z .y xRz p) = 
  Transitive-closure.trans Transitive-closure.[ xRz ] (TrClos1n⇒tr-clos R z y p)

tr-clos⇒TrClos1n : ∀ {a} {A : Set a} (R : Rel A a) x y → tr-clos R x y → TrClos1n R x y
tr-clos⇒TrClos1n R x y Transitive-closure.[ xRy ] = step1n x y xRy
tr-clos⇒TrClos1n R x y (Transitive-closure.trans {.x} {z} {.y} tr1 tr2) = 
  helper x z (tr-clos⇒TrClos1n R x z tr1) tr1 tr2 (tr-clos⇒TrClos1n R z y tr2)
  where
    helper : ∀ u v → TrClos1n R u v → tr-clos R u v → tr-clos R v y → 
      TrClos1n R v y → TrClos1n R u y
    helper u v (step1n .u .v x₁) uv vy v1y = 
      trans1n u v y x₁ v1y
    helper u v (trans1n .u y₁ .v uRy₁ u1v) uv vy v1y = 
      trans1n u y₁ y uRy₁ 
        (helper y₁ v u1v (TrClos1n⇒tr-clos R y₁ v u1v) vy v1y)

rt-clos : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) → Rel X ℓ
rt-clos R x y = x ≡ y ⊎ tr-clos R x y

tr-clos-left : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) z y z0 →
             R z y -> rt-clos R z0 z -> tr-clos R z0 y
tr-clos-left R z y z0 Rzy (inj₁ z0≡z) rewrite z0≡z = 
  Transitive-closure.[ Rzy ]
tr-clos-left R z y z0 Rzy (inj₂ trRz0z) = 
  Transitive-closure.trans trRz0z Transitive-closure.[ Rzy ]

rt-clos-left : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) z y z0 →
             R z y -> rt-clos R z0 z -> rt-clos R z0 y
rt-clos-left R z y z0 Rzy rtRz0z = inj₂ (tr-clos-left R z y z0 Rzy rtRz0z)

af⇒Acc : ∀ {ℓ} {X : Set ℓ} (R T : Rel X ℓ) (t : WFT X) → R ⟱ t → ∀ y →
  (∀ x z → rt-clos T z y → tr-clos T x z × R z x → ⊥) → Acc T y
af⇒Acc R T now R⟱t y p = acc (λ y₁ Ty₁y → 
  ⊥-elim (p y₁ y (inj₁ refl) (Transitive-closure.[ Ty₁y ] , R⟱t y y₁)))
af⇒Acc R T (later s) R⟱t y p = acc (λ z Tzy → 
  af⇒Acc (λ y₀ z → R y₀ z ⊎ R y y₀) T (s y) (R⟱t y) z (helper z Tzy))
  where
    helper : ∀ z → T z y → ∀ x z₀ → rt-clos T z₀ z → tr-clos T x z₀ × (R z₀ x ⊎ R y z₀) → ⊥
    helper z Tzy x z₀ rtcTz₀z (tcTxz₀ , inj₁ Rz₀x) =
      p x z₀ (rt-clos-left T z y z₀ Tzy rtcTz₀z) (tcTxz₀ , Rz₀x)
    helper z Tzy x z₀ rtcTz₀z (tcTxz₀ , inj₂ Ryz₀) = 
      p x z₀ (rt-clos-left T z y z₀ Tzy rtcTz₀z) 
        (tcTxz₀ , ⊥-elim (p z₀ y (inj₁ refl) 
          (tr-clos-left T z y z₀ Tzy rtcTz₀z , Ryz₀)))

af⇒wf : ∀ {ℓ} {X : Set ℓ} (R T : Rel X ℓ) →
  (∀ x y → tr-clos T x y × R y x → ⊥) → ∀ (t : WFT X) → R ⟱ t → Well-founded T
af⇒wf R T p t s = λ x → 
  af⇒Acc R T t s x (λ x₁ z rtTzx trTx₁z∧Rzx₁ → p x₁ z trTx₁z∧Rzx₁)

