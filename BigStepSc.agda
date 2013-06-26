module BigStepSc where

{- ### Schemes of different types of big-step supercompilation ### -}

{-
A variation of the scheme presented in the paper

Ilya G. Klyuchnikov, Sergei A. Romanenko. Formalizing and Implementing
Multi-Result Supercompilation.
In Third International Valentin Turchin Workshop on Metacomputation
(Proceedings of the Third International Valentin Turchin Workshop on
Metacomputation. Pereslavl-Zalessky, Russia, July 5-9, 2012).
A.V. Klimov and S.A. Romanenko, Ed. - Pereslavl-Zalessky: Ailamazyan
University of Pereslavl, 2012, 260 p. ISBN 978-5-901795-28-6, pages
142-164. 
-}

open import Level
  using (Level; _⊔_)
open import Data.Nat
  hiding(_⊔_)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Relation.Binary.Vec.Pointwise
  using (Pointwise′; []; _∷_)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Unary
  using (Decidable; _∈_)
open import Relation.Binary
  using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_)

-- AnyV

AnyV : ∀ {n a ℓ} {A : Set a} (P : A → Set ℓ) (xs : Vec A n) → Set ℓ
AnyV P xs = ∃ λ i → P (lookup i xs) 

-- anyV

anyV : ∀ {n a p} {A : Set a} {P : A → Set p} →
  Decidable P → Decidable (AnyV {n} P)

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

-- ScWorld

record ScWorld : Set₁ where

  field

    -- Configurations.
    Conf : Set

    -- The equality of configurations is decidable.
    _≟Conf_ : (c₁ c₂ : Conf) → Dec (c₁ ≡ c₂)

    -- c ⊑ c′ means that c′ is more general than c.
    _⊑_ : (c c′ : Conf) → Set

    -- ⊑ is decidable.
    _⊑?_ : (c c′ : Conf) → Dec (c ⊑ c′)

    -- Contractions (currently they are not taken into account).
    --Contr : Set

    -- Driving a configuration leads to a finite number of new ones.
    _⇉_ : (c : Conf) {k : ℕ} (cs : Vec Conf k) → Set

    -- Rebuilding a configuration replaces it with an equivalent one.
    -- We suppose that the number of possible rebuildings is finite!
    _↴_ : (c : Conf) {k : ℕ} (cs : Vec Conf k) → Set

  conf-setoid : Setoid _ _
  conf-setoid = P.setoid Conf

  conf-decSetoid : DecSetoid _ _
  conf-decSetoid = P.decSetoid _≟Conf_

  History : ℕ → Set
  History n = Vec Conf n

  Foldable : ∀ {n} (h : History n) (c : Conf) → Set
  Foldable {n} h c = AnyV (_⊑_ c) h

  foldable? : ∀ {n} (h : History n) (c : Conf) → Dec (Foldable h c)
  foldable? h c = anyV (_⊑?_ c) h

  data Graph : (n : ℕ) → Set where
    case    : ∀ {n k} (c : Conf) (gs : Vec (Graph (suc n)) k) → Graph n
    back    : ∀ {n} (c : Conf) (b : Fin n) → Graph n
    rebuild : ∀ {n} (c : Conf) (g : Graph (suc n)) → Graph n

-- BigStepNDSC

module BigStepNDSC (scWorld : ScWorld) where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ : {n : ℕ}
    (h : History n) (c : Conf) (g : Graph n) → Set where
    ndsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c (proj₁ f)
    ndsc-drive : ∀ {n h c k}
      {cs : Vec Conf k} {gs : Vec (Graph (suc n)) k}
      (ds : c ⇉ cs) →
      --(∀ i → c ∷ h ⊢NDSC (lookup i cs) ↪ (lookup i gs)) →
      Pointwise′ (_⊢NDSC_↪_ (c ∷ h)) cs gs →
      h ⊢NDSC c ↪ (case c gs)
    ndsc-rebuild : ∀ {n h c k}
      {cs : Vec Conf k} {g : Graph (suc n)}
      (r : c ↴ cs) (i : Fin k) →
      c ∷ h ⊢NDSC (lookup i cs) ↪ g →
      h ⊢NDSC c ↪ rebuild c g

-- ScWorld3

module ScWorld3 where

  -- This is a silly world with 3 possible configurations.
  -- (Just for testing.)

  data Conf3 : Set where
    c0 c1 c2 : Conf3

  _≟Conf_ : (c c′ : Conf3) → Dec (c ≡ c′)
  c0 ≟Conf c0 = yes P.refl
  c0 ≟Conf c1 = no (λ ())
  c0 ≟Conf c2 = no (λ ())
  c1 ≟Conf c0 = no (λ ())
  c1 ≟Conf c1 = yes P.refl
  c1 ≟Conf c2 = no (λ ())
  c2 ≟Conf c0 = no (λ ())
  c2 ≟Conf c1 = no (λ ())
  c2 ≟Conf c2 = yes P.refl

  infix 4 _⇉′_

  data _⇉′_ : (c : Conf3) {n : ℕ} (cs : Vec Conf3 n) → Set where
    c0⇉c1c2 : c0 ⇉′ c1 ∷ c2 ∷ []
    c1⇉c0   : c1 ⇉′ c0 ∷ []
    c2⇉c1   : c2 ⇉′ c1 ∷ []

  data _↴′_ : (c : Conf3) {k : ℕ} (cs : Vec Conf3 k) → Set where
    c0↴c1 : c0 ↴′ (c1 ∷ [])

  scWorld3 : ScWorld
  scWorld3 = record
    { Conf = Conf3
    ; _≟Conf_ = _≟Conf_
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟Conf_
    ; _⇉_ = _⇉′_
    ; _↴_ = _↴′_
    }

-- NDSC-test3

module NDSC-test3 where

  open ScWorld3
  open ScWorld scWorld3
  open BigStepNDSC scWorld3

  w3graph1 : [] ⊢NDSC c0 ↪
    case c0
      (case c1 (back c0 (suc zero) ∷ []) ∷
        case c2
          (case c1 (back c0 (suc (suc zero)) ∷ []) ∷ []) ∷ [])
  w3graph1 =
    ndsc-drive c0⇉c1c2
      ((ndsc-drive c1⇉c0
        ((ndsc-fold (suc zero , P.refl)) ∷ [])) ∷
      (ndsc-drive c2⇉c1
        (ndsc-drive c1⇉c0
          ((ndsc-fold (suc (suc zero) , P.refl)) ∷ [])
        ∷ [])) ∷ [])

  w3graph2 : [] ⊢NDSC c0 ↪
    rebuild c0 (case c1 (back c0 (suc zero) ∷ []))
  w3graph2 =
    ndsc-rebuild c0↴c1 zero
      (ndsc-drive c1⇉c0 (ndsc-fold (suc zero , P.refl) ∷ []))

--
-- Extracting the residual graph from a proof
--

module GraphExtraction (scWorld : ScWorld) where
  open ScWorld scWorld
  open BigStepNDSC scWorld

  -- getGraph

  getGraph : ∀ {n} {h : History n} {c : Conf} {g : Graph n}
    (p : h ⊢NDSC c ↪ g) → Graph n

  getGraph (ndsc-fold {c = c} (i , c⊑c′)) = back c i
  getGraph (ndsc-drive {c = c} {gs = gs} ds ps) = case c gs
  getGraph (ndsc-rebuild {c = c} {g = g} r i p) = rebuild c g

  -- getGraph-sound

  getGraph-sound : ∀ {n} {h : History n} {c : Conf} {g : Graph n}
    (p : h ⊢NDSC c ↪ g) → getGraph p ≡ g

  getGraph-sound (ndsc-fold f) = P.refl
  getGraph-sound (ndsc-drive ds x) = P.refl
  getGraph-sound (ndsc-rebuild r i p) = P.refl
