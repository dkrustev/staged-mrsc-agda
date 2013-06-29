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
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>)
open import Data.List as List
open import Data.List.Any
  using (Any; here; there)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; lookup)
open import Relation.Binary.List.Pointwise
  using ([]; _∷_)
  renaming (Rel to Pointwise)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Unary
  using (Decidable)
open import Relation.Binary
  using (Setoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import Util


-- Bar

-- The set of finite paths such that either
-- (1) B h is valid right now; or
-- (2) for all possible a₁ ∷ h either
--     (1) B (a₁ ∷ h) is valid right now; or
--     (2) for all possible a₂ ∷ a₁ ∷ h either ...

data Bar {A : Set} (B : ∀ {m} → Vec A m → Set) :
         {n : ℕ} (h : Vec A n) → Set where
  now   : ∀ {n} {h : Vec A n} (bz : B h) → Bar B h
  later : ∀ {n} {h : Vec A n} (bs : ∀ a → Bar B (a ∷ h)) → Bar B h

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
    _⇉ : (c : Conf) → List Conf

    -- Rebuilding a configuration replaces it with an equivalent one.
    -- We suppose that the number of possible rebuildings is finite!
    _↴ : (c : Conf) → List Conf


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

  field
    -- Whistles deal with histories

    -- Dangerous histories
    Dangerous : ∀ {n} (h : History n) → Set
    dangerous? : ∀ {n} (h : History n) → Dec (Dangerous h)

    -- Bar-induction
    bar[] : Bar Dangerous []

  data Graph : (n : ℕ) → Set where
    back    : ∀ {n} (c : Conf) (b : Fin n) → Graph n
    case    : ∀ {n} (c : Conf) (gs : List (Graph (suc n))) → Graph n
    rebuild : ∀ {n} (c : Conf) (g : Graph (suc n)) → Graph n


-- BigStepNDSC

module BigStepNDSC (scWorld : ScWorld) where

  open ScWorld scWorld

  infix 4 _⊢NDSC_↪_

  data _⊢NDSC_↪_ : {n} (h : History n) (c : Conf) (g : Graph n) → Set where
    ndsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢NDSC c ↪ back c (proj₁ f)
    ndsc-drive : ∀ {n h c}
      {gs : List (Graph (suc n))}
      (¬f : ¬ Foldable h c) →
      Pointwise (_⊢NDSC_↪_ (c ∷ h)) (c ⇉) gs →
      h ⊢NDSC c ↪ (case c gs)
    ndsc-rebuild : ∀ {n h c c′}
      {g : Graph (suc n)}
      (¬f : ¬ Foldable h c)
      (i : Any (_≡_ c′) (c ↴)) →
      c ∷ h ⊢NDSC c′ ↪ g →
      h ⊢NDSC c ↪ rebuild c g

-- BigStepMRSC

module BigStepMRSC (scWorld : ScWorld) where

  open ScWorld scWorld

  -- Relational big-step multi-result supercompilation.

  infix 4 _⊢MRSC_↪_

  data _⊢MRSC_↪_ : ∀ {n} (h : History n) (c : Conf) (g : Graph n) → Set where
    mrsc-fold  : ∀ {n} {h : History n} {c}
      (f : Foldable h c) →
      h ⊢MRSC c ↪ back c (proj₁ f)
    mrsc-drive : ∀ {n h c}
      {gs : List (Graph (suc n))}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ Dangerous h) →
      Pointwise (_⊢MRSC_↪_ (c ∷ h)) (c ⇉) gs →
      h ⊢MRSC c ↪ (case c gs)
    mrsc-rebuild : ∀ {n h c c′}
      {g : Graph (suc n)}
      (¬f : ¬ Foldable h c)
      (¬w : ¬ Dangerous h) →
      (i : Any (_≡_ c′) (c ↴)) →
      c ∷ h ⊢MRSC c′ ↪ g →
      h ⊢MRSC c ↪ rebuild c g

  -- Functional big-step multi-result supercompilation.
  -- (The naive version builds Cartesian products immediately.)

  -- naive-mrsc′

  naive-mrsc′ : ∀ {n} (h : History n) (b : Bar Dangerous h) (c : Conf) →
                  List (Graph n)
  naive-mrsc′ {n} h b c with foldable? h c
  ... | yes (i , c⊑hi) = [ back c i ]
  ... | no ¬f with dangerous? h
  ... | yes w = []
  ... | no ¬w with b
  ... | now bz = ⊥-elim (¬w bz)
  ... | later bs = drive! ++ rebuild!
    where
    drive! : List (Graph n)
    drive! =
      map (case c)
          (cartesian (map (naive-mrsc′ (c ∷ h) (bs c)) (c ⇉)))
    rebuild! : List (Graph n)
    rebuild! =
      map (rebuild c)
          (concat (map (naive-mrsc′ (c ∷ h) (bs c)) (c ↴)))
  
  -- naive-mrsc

  naive-mrsc : (c : Conf) → List(Graph 0)
  naive-mrsc c = naive-mrsc′ [] bar[] c

  -- "Lazy" multi-result supercompilation.
  -- (Cartesian products are not immediately built.)

  data LazyGraph : (n : ℕ) → Set where
    alt     : ∀ {n} (gs : List (LazyGraph n)) → LazyGraph n
    back    : ∀ {n} (c : Conf) (b : Fin n) → LazyGraph n
    case    : ∀ {n} (c : Conf) (gss : List (LazyGraph (suc n))) →
                LazyGraph n
    rebuild : ∀ {n} (c : Conf) (gs : LazyGraph (suc n)) →
                LazyGraph n

  -- lazy-mrsc′

  lazy-mrsc′ : ∀ {n} (h : History n) (b : Bar Dangerous h) (c : Conf) →
                  LazyGraph n
  lazy-mrsc′ {n} h b c with foldable? h c
  ... | yes (i , c⊑hi) = back c i
  ... | no ¬f with dangerous? h
  ... | yes w = alt []
  ... | no ¬w with b
  ... | now bz = ⊥-elim (¬w bz)
  ... | later bs = alt (drive! ∷ rebuild! ∷ [])
    where
    drive! : LazyGraph n
    drive! =
      case c (map (lazy-mrsc′ (c ∷ h) (bs c)) (c ⇉))
    rebuild! : LazyGraph n
    rebuild! =
      rebuild c (alt (map (lazy-mrsc′ (c ∷ h) (bs c)) (c ↴)))

  -- lazy-mrsc

  lazy-mrsc : (c : Conf) → LazyGraph 0
  lazy-mrsc c = lazy-mrsc′ [] bar[] c

  -- generate-graphs

  mutual

    get-graphs : ∀ {n} (gs : LazyGraph n) → List (Graph n)

    get-graphs (alt gss) =
      map-alt gss
    get-graphs (back c b) =
      [ back c b ]
    get-graphs (case c gss) =
      map (case c) (cartesian (map-list gss))
    get-graphs (rebuild c gs) =
      map (rebuild c) (get-graphs gs)

    map-alt : ∀ {n} (gss : List (LazyGraph n)) → List (Graph n)
    map-alt [] = []
    map-alt (gs ∷ gss) = get-graphs gs ++ map-alt gss

    map-list : ∀ {n} → (gss : List (LazyGraph n)) →
                List (List (Graph n))
    map-list [] = []
    map-list (gs ∷ gss) = get-graphs gs ∷ map-list gss


module MRSC→NDSC (scWorld : ScWorld) where

  open ScWorld scWorld
  open BigStepNDSC scWorld
  open BigStepMRSC scWorld

  MRSC→NDSC : ∀ {n h c g} → _⊢MRSC_↪_ {n} h c g → h ⊢NDSC c ↪ g
  MRSC→NDSC (mrsc-fold f) = ndsc-fold f
  MRSC→NDSC (mrsc-drive {n} {h} {c} {gs} ¬f ¬w ∀i⊢ci↪g) =
    ndsc-drive ¬f (pw-map ∀i⊢ci↪g)
    where
    pw-map : ∀ {cs : List Conf} {gs : List (Graph (suc n))}
               (qs : Pointwise (_⊢MRSC_↪_ (c ∷ h)) cs gs) →
             Pointwise (_⊢NDSC_↪_ (c ∷ h)) cs gs
    pw-map [] = []
    pw-map (q ∷ qs) = MRSC→NDSC q ∷ (pw-map qs)
  MRSC→NDSC (mrsc-rebuild ¬f ¬w i ⊢ci↪g) =
    ndsc-rebuild ¬f i (MRSC→NDSC ⊢ci↪g)


-- HistoryLengthWhistle

module HistoryLengthWhistle (A : Set) (l : ℕ) where

  --open ScWorld scWorld

  HLDangerous : ∀ {n} (h : Vec A n) → Set
  HLDangerous {n} h = l ≤ n

  hlDangerous? : ∀ {n} (h : Vec A n) → Dec (HLDangerous h)
  hlDangerous? {n} h = l ≤? n

  hlBar : ∀ m n (h : Vec A n) (d : m + n ≡ l) → Bar HLDangerous h
  hlBar zero .l h refl =
    now (≤′⇒≤ ≤′-refl)
  hlBar (suc m) n h d =
    later (λ c → hlBar m (suc n) (c ∷ h) m+1+n≡l)
    where
    open ≡-Reasoning
    m+1+n≡l = begin m + suc n ≡⟨ m+1+n≡1+m+n m n ⟩ suc (m + n) ≡⟨ d ⟩ l ∎

  hlBar[] : Bar HLDangerous []
  hlBar[] = hlBar l zero [] (l + zero ≡ l ∋ proj₂ *+.+-identity l)

-- ScWorld3

module ScWorld3 where

  -- This is a silly world with 3 possible configurations.
  -- (Just for testing.)

  data Conf3 : Set where
    c0 c1 c2 : Conf3

  _≟Conf3_ : (c c′ : Conf3) → Dec (c ≡ c′)
  c0 ≟Conf3 c0 = yes refl
  c0 ≟Conf3 c1 = no (λ ())
  c0 ≟Conf3 c2 = no (λ ())
  c1 ≟Conf3 c0 = no (λ ())
  c1 ≟Conf3 c1 = yes refl
  c1 ≟Conf3 c2 = no (λ ())
  c2 ≟Conf3 c0 = no (λ ())
  c2 ≟Conf3 c1 = no (λ ())
  c2 ≟Conf3 c2 = yes refl

  _⇉′ : (c : Conf3) → List Conf3

  c0 ⇉′ = c1 ∷ c2 ∷ []
  c1 ⇉′ = c0 ∷ []
  c2 ⇉′ = c1 ∷ []

  _↴′ : (c : Conf3) → List Conf3
  c0 ↴′ = c1 ∷ []
  _ ↴′  = []


  open HistoryLengthWhistle Conf3

  scWorld3 : ScWorld
  scWorld3 = record
    { Conf = Conf3
    ; _≟Conf_ = _≟Conf3_
    ; _⊑_ = _≡_
    ; _⊑?_ = _≟Conf3_
    ; _⇉ = _⇉′
    ; _↴ = _↴′
    ; Dangerous = HLDangerous 4
    ; dangerous? = hlDangerous? 4
    ; bar[] = hlBar[] 4
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
    ndsc-drive ¬f1
      ((ndsc-drive ¬f2
        ((ndsc-fold (suc zero , refl)) ∷ [])) ∷
      (ndsc-drive ¬f3
        ((ndsc-drive ¬f4
          ((ndsc-fold (suc (suc zero) , refl)) ∷ []))
        ∷ [])) ∷ [])
    where
    ¬f1 : ¬ Σ (Fin zero) (λ z → c0 ≡ lookup z [])
    ¬f1 (() , _)
    ¬f2 : ¬ Σ (Fin (suc zero)) (λ z → c1 ≡ lookup z (c0 ∷ []))
    ¬f2 (zero , ())
    ¬f2 (suc () , _)
    ¬f3 : ¬ Σ (Fin (suc zero)) (λ z → c2 ≡ lookup z (c0 ∷ []))
    ¬f3 (zero , ())
    ¬f3 (suc () , _)
    ¬f4 : ¬ Σ (Fin (suc (suc zero))) (λ z → c1 ≡ lookup z (c2 ∷ c0 ∷ []))
    ¬f4 (zero , ())
    ¬f4 (suc zero , ())
    ¬f4 (suc (suc ()) , _)

  w3graph2 : [] ⊢NDSC c0 ↪
    rebuild c0 (case c1 (back c0 (suc zero) ∷ []))
  w3graph2 =
    ndsc-rebuild ¬f1 (here refl)
      (ndsc-drive ¬f2 ((ndsc-fold (suc zero , refl)) ∷ []))
    where
    ¬f1 : Σ (Fin zero) (λ z → c0 ≡ lookup z []) → ⊥
    ¬f1 (() , _)
    ¬f2 : Σ (Fin (suc zero)) (λ z → c1 ≡ lookup z (c0 ∷ [])) → ⊥
    ¬f2 (zero , ())
    ¬f2 (suc () , _)


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
  getGraph (ndsc-drive {c = c} {gs = gs} ¬f ps) = case c gs
  getGraph (ndsc-rebuild {c = c} {g = g} ¬f i p) = rebuild c g

  -- getGraph-sound

  getGraph-sound : ∀ {n} {h : History n} {c : Conf} {g : Graph n}
    (p : h ⊢NDSC c ↪ g) → getGraph p ≡ g

  getGraph-sound (ndsc-fold f) = refl
  getGraph-sound (ndsc-drive ¬f ps) = refl
  getGraph-sound (ndsc-rebuild ¬f i p) = refl
