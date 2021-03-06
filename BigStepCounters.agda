module BigStepCounters where

open import Data.Nat as N
  using (ℕ; zero; suc)
open import Data.Nat.Properties as NP
  using (≤-step)
open import Data.List as List
  using (List; []; _∷_; [_])
open import Data.List.Any as Any
  using (Any; here; there; module Membership-≡)
open import Data.Vec as Vec
  using (Vec; []; _∷_)
open import Relation.Binary.Vec.Pointwise as Pointwise
  using (Pointwise; Pointwise-≡)
open import Data.Bool as Bool
  using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Empty
open import Data.Unit
  using (⊤; tt)
open import Data.Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)

open import Function
open import Function.Equivalence as FEQV
  using (module Equivalence)
open import Function.Equality as FEQU
  using (_⟨$⟩_)

open import Relation.Nullary
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Relation.Nullary.Negation
  using (¬?)
open import Relation.Nullary.Sum

open import Relation.Unary
  using () renaming (Decidable to Decidable₁; _⊆_ to _⋐_)
open import Relation.Binary
  using (Rel) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to P[_])

open import Util
open import BarWhistles
open import Graphs
open import BigStepSc
open import Cographs

-- ℕω

data ℕω : Set where
  ω  : ℕω
  #_ : (i : ℕ) → ℕω

infixl 8 _+_ _∸_

-- _+_

_+_ : (m n : ℕω) → ℕω

ω + n = ω
m + ω = ω
# i + # j = # (i N.+ j)

-- _∸_

_∸_ : (m n : ℕω) → ℕω

ω ∸ n = ω
m ∸ ω = ω
# i ∸ # j = # (i N.∸ j)

infix 4 _≥#_ _≥#?_ _=#_ _=#?_

-- _≥_

data _≥#_ : (m : ℕω) (j : ℕ) → Set where
  ω≥j   : ∀ {j : ℕ} → ω ≥# j
  #i≥j : ∀ {i j : ℕ} → (i≥j : i N.≥ j) → # i ≥# j

-- _≥?_

_≥#?_ : Decidable₂ _≥#_

ω ≥#? j = yes ω≥j

# i ≥#? j with j N.≤? i
... | yes j≤i = yes (#i≥j j≤i)
... | no ¬j≤i = no helper
  where helper : # i ≥# j → ⊥
        helper (#i≥j i≥j) = ¬j≤i i≥j

-- _=#_

data _=#_ : (m : ℕω) (j : ℕ) → Set where
  ω=j   : ∀ {j} → ω =# j
  #i=i : ∀ {i} → # i =# i

-- #i=j→i≡j

#i=#j→i≡j : ∀ {i j} → # i =# j → i ≡ j
#i=#j→i≡j #i=i = refl

-- _=#?_

_=#?_ : Decidable₂ _=#_

ω =#? n = yes ω=j
# i =#? j with i N.≟ j
... | yes i≡j rewrite i≡j = yes #i=i
... | no  i≢j = no helper
  where helper : # i =# j → ⊥
        helper #i=j = i≢j (#i=#j→i≡j #i=j)

-- m ⊑₁ n means that n is more general than m.

-- _⊑₁_

data _⊑₁_ : (m n : ℕω) → Set where
  m⊑₁ω : ∀ {m} → m ⊑₁ ω
  #i⊑₁#i : ∀ {i} → # i ⊑₁ # i

-- #i⊑₁#j→i≡j

#i⊑₁#j→i≡j : ∀ {i j} → # i ⊑₁ # j → i ≡ j
#i⊑₁#j→i≡j #i⊑₁#i = refl

-- _⊑₁?_

_⊑₁?_ : Decidable₂ _⊑₁_

m ⊑₁? ω =
  yes m⊑₁ω
ω ⊑₁? # i =
  no (λ ())
# i ⊑₁? # j with i N.≟ j
... | yes i≡j rewrite i≡j = yes #i⊑₁#i
... | no  i≢j = no helper
  where helper : # i ⊑₁ # j → ⊥
        helper #i⊑₁#j = i≢j (#i⊑₁#j→i≡j #i⊑₁#j)

#i≡#j→i≡j : ∀ {i j} → # i ≡ # j → i ≡ j
#i≡#j→i≡j refl = refl

-- _≟ω_

infix 4 _≟ω_

_≟ω_ : Decidable₂ {A = ℕω} _≡_

ω ≟ω ω = yes refl
ω ≟ω # i = no (λ ())
# i ≟ω ω = no (λ ())
# i ≟ω # j with i N.≟ j
... | yes i≡j rewrite i≡j = yes refl
... | no  i≢j = no (i≢j ∘ #i≡#j→i≡j)

--
-- "Worlds of counters"
-- (To be converted to worlds of supercompilation.)
--

record CntWorld {k : ℕ} : Set₁ where
  constructor
    ⟨⟨_,_,_⟩⟩

  Conf : Set
  Conf = Vec ℕω k

  field

    -- Initial configuration
    start : Conf

    -- Driving (deterministic)
    _⇊ : (c : Conf) → List Conf

    -- Which configurations are (semantically) unsafe?
    unsafe : (c : Conf) → Bool

--
-- Converting a world of counters to a world of supercompilation.
--

module CntSc {k : ℕ} (cntWorld : CntWorld {k})
  (maxℕ : ℕ) (maxDepth : ℕ) where

  open CntWorld cntWorld public

  _≟Conf_ : Decidable₂ (_≡_ {A = Conf})

  c ≟Conf c′ with  Pointwise.decidable _≟ω_ c c′
  ... | yes PW-c≡c′ = yes (Equivalence.to Pointwise-≡ ⟨$⟩ PW-c≡c′)
  ... | no ¬PW-c≡c′ = no (¬PW-c≡c′ ∘ _⟨$⟩_ (Equivalence.from Pointwise-≡))

  -- _⊑_

  _⊑_ : (c c′ : Conf) → Set

  _⊑_ c c′ = Pointwise _⊑₁_ c c′

  -- _⊑?_

  _⊑?_ : Decidable₂ _⊑_
  _⊑?_ = Pointwise.decidable _⊑₁?_

  -- Rebuildings

  -- _↷₁

  _↷₁ : ∀ (n : ℕω) → List ℕω
  ω ↷₁ = ω ∷ []
  (# i) ↷₁ = ω ∷ # i ∷ []

  -- _↷ 

  _↷ : (c : Conf) → List Conf
  _↷ c = remove-c (vec-cartesian (Vec.map _↷₁ c))
    where remove-c = List.filter (λ c′ → ⌊ ¬? (c ≟Conf c′) ⌋)

  -- TooBig₁

  TooBig₁ : (n : ℕω) → Set
  TooBig₁ ω = ⊥
  TooBig₁ (# i) = maxℕ N.≤ i

  -- tooBig₁?

  tooBig₁? : Decidable₁ TooBig₁
  tooBig₁? ω = no id
  tooBig₁? (# i) = maxℕ N.≤? i

  -- TooBig

  TooBig : (c : Conf) → Set
  TooBig c = Any TooBig₁ (Vec.toList c)

  tooBig? : Decidable₁ TooBig
  tooBig? c = Any.any tooBig₁? (Vec.toList c)


  mkScWorld : (cntWorld : CntWorld {k}) → ScWorld
  mkScWorld ⟨⟨ start , _⇊ , unsafe ⟩⟩ = record
    { Conf = Conf
    ; _⊑_ = _⊑_
    ; _⊑?_ = _⊑?_
    ; _⇉ = λ c → c ⇊ ∷ List.map [_] (c ↷) -- driving + rebuilding
    ; whistle = ⟨ (λ h → (maxDepth N.≤ List.length h) ⊎ (↯ h))
                , (λ c h → [ inj₁ ∘ ≤-step , inj₂ ∘ inj₂ ]′)
                , (λ h → (maxDepth N.≤? List.length h) ⊎-dec (↯? h))
                , bar[]
                ⟩
    }
    where

    ↯ : ∀ (h : List Conf) → Set

    ↯ [] = ⊥
    ↯ (c ∷ h) = TooBig c ⊎ ↯ h

    ↯? : Decidable₁ ↯
    ↯? [] = no id
    ↯? (c ∷ h) with ↯? h
    ... | yes dh = yes (inj₂ dh)
    ... | no ¬dh with tooBig? c
    ... | yes tb = yes (inj₁ tb)
    ... | no ¬tb = no [ ¬tb , ¬dh ]′

    -- The whistle is based on the combination of `pathLengthWhistle` and
    -- and `↯`.

    -- TODO: It is possible to construct a whistle based on the fact that
    -- the set of configurations such that `¬ TooBig l c` is finite.

    bar[] : Bar (λ h → maxDepth N.≤ List.length h ⊎ ↯ h) []
    bar[] = bar-⊎ [] (BarWhistle.bar[] (pathLengthWhistle Conf maxDepth))


  scWorld : ScWorld
  scWorld = mkScWorld cntWorld

  open BigStepMRSC scWorld public
  open BigStepMRSC∞ scWorld public
  open BigStepMRSC∞-Ø scWorld public

  cl-unsafe : ∀ (l : LazyGraph Conf) → LazyGraph Conf
  cl-unsafe = cl-bad-conf unsafe

  cl∞-unsafe : ∀ (l : LazyCograph Conf) → LazyCograph Conf
  cl∞-unsafe = cl∞-bad-conf unsafe


--
-- An alternative definition of a counter-system supercompiler
--

module CntSc' {k : ℕ} (cntWorld : CntWorld {k}) where
  open import Data.Product
  open import Data.Fin as Fin using (Fin) 
  open import Data.Vec hiding ([_])
  open import Induction.WellFounded
  open import Induction.Nat
--  open import VecWf
  open import AlmostFullRel


  open CntWorld cntWorld public

  _≟Conf_ : Decidable₂ (_≡_ {A = Conf})
  c ≟Conf c′ with  Pointwise.decidable _≟ω_ c c′
  ... | yes PW-c≡c′ = yes (Equivalence.to Pointwise-≡ ⟨$⟩ PW-c≡c′)
  ... | no ¬PW-c≡c′ = no (¬PW-c≡c′ ∘ _⟨$⟩_ (Equivalence.from Pointwise-≡))

  -- _⊑_

  _⊑_ : (c c′ : Conf) → Set
  _⊑_ c c′ = Pointwise _⊑₁_ c c′

  -- _⊑?_

  _⊑?_ : Decidable₂ _⊑_
  _⊑?_ = Pointwise.decidable _⊑₁?_

  data _<ω_ : (m n : ℕω) → Set where
    #<ω : ∀ {i} → # i <ω ω
    #<ω# : ∀ {i j} → i N.<′ j → # i <ω # j

  _<ω?_ : Decidable₂ _<ω_
  ω     <ω? _     = no (λ ())
  (# i) <ω? ω     = yes #<ω
  (# i) <ω? (# j) with (suc i) N.≤? j
  (# i) <ω? (# j) | yes lt = yes (#<ω# (NP.≤⇒≤′ lt))
  (# i) <ω? (# j) | no ¬lt = no (helper ¬lt)
    where
    helper : ∀ {i j} → ¬ i N.< j → # i <ω # j → ⊥
    helper ¬lt (#<ω# lt) = ¬lt (NP.≤′⇒≤ lt)

  <ω-trichotomy : ∀ m n → m <ω n ⊎ m ≡ n ⊎ n <ω m
  <ω-trichotomy ω ω = inj₂ (inj₁ refl)
  <ω-trichotomy ω (# i) = inj₂ (inj₂ #<ω)
  <ω-trichotomy (# i) ω = inj₁ #<ω
  <ω-trichotomy (# i) (# j) with i N.≤? j
  <ω-trichotomy (# i) (# j) | yes i≤j with i N.≟ j
  <ω-trichotomy (# i) (# j) | yes i≤j | yes i≡j rewrite i≡j = inj₂ (inj₁ refl)
  <ω-trichotomy (# i) (# j) | yes i≤j | no ¬i≡j = inj₁ (#<ω# (NP.≤⇒≤′ (helper i j i≤j ¬i≡j)))
    where
      helper1 : ∀ i j → i N.≤ j → i ≡ j ⊎ i N.< j
      helper1 .0 zero N.z≤n = inj₁ refl
      helper1 .0 (suc j₁) N.z≤n = inj₂ (N.s≤s N.z≤n)
      helper1 .(suc i) (suc j) (N.s≤s {i} le) with helper1 i j le
      helper1 .(suc m) (suc j₁) (N.s≤s {m} le) | inj₁ eq rewrite eq = inj₁ refl
      helper1 .(suc m) (suc j₁) (N.s≤s {m} le) | inj₂ lt = inj₂ (N.s≤s lt)
      helper : ∀ i j → i N.≤ j → ¬ i ≡ j → i N.< j
      helper i j le neq with helper1 i j le
      helper i₁ j₁ le neq | inj₁ eq = ⊥-elim (neq eq)
      helper i₁ j₁ le neq | inj₂ lt = lt
  <ω-trichotomy (# i) (# j) | no ¬i≤j = inj₂ (inj₂ (#<ω# (NP.≤⇒≤′ (NP.≰⇒> ¬i≤j))))

  _≤ω_ : (m n : ℕω) → Set
  m ≤ω n = m <ω n ⊎ m ≡ n

  _≤ω?_ : Decidable₂ _≤ω_
  _≤ω?_ m n with m ≟ω n
  m ≤ω? n | yes m≡n = yes (inj₂ m≡n)
  m ≤ω? n | no m≢n with m <ω? n
  m ≤ω? n | no m≢n | yes m<n = yes (inj₁ m<n)
  m ≤ω? n | no m≢n | no ¬m<n = no helper
    where 
      helper : m <ω n ⊎ m ≡ n → ⊥
      helper (inj₁ m<n) = ¬m<n m<n
      helper (inj₂ m≡n) = m≢n m≡n

  acc-# : ∀ i → Acc N._<′_ i → Acc _<ω_ (# i)
  acc-# i (acc rs) = acc helper
    where
      helper : ∀ n → n <ω (# i) → Acc _<ω_ n
      helper .(# j) (#<ω# {j} j<i) = acc-# j (rs j j<i)

  acc-ω : Well-founded N._<′_ → Acc _<ω_ ω
  acc-ω wfN = acc helper
    where
      helper : ∀ n → n <ω ω → Acc _<ω_ n
      helper .(# i) (#<ω {i}) = acc-# i (wfN i)

  <ω-wf : Well-founded _<ω_
  <ω-wf ω = acc-ω <-well-founded
  <ω-wf (# i) = acc-# i (<-well-founded i)

  ≤ω-af : Almost-full _≤ω_
  ≤ω-af = af-⇒ helper (af-from-wf <ω-wf _<ω?_)
    where
      helper : ∀ {m n} → ¬ n <ω m → m ≤ω n
      helper {m} {n} nlt with <ω-trichotomy m n
      helper {m} {n} nlt | inj₁ lt = inj₁ lt
      helper {m} {n} nlt | inj₂ (inj₁ eq) rewrite eq = inj₂ refl
      helper {m} {n} nlt | inj₂ (inj₂ lt) = ⊥-elim (nlt lt)


  -- Rebuildings

  -- _↷₁

  _↷₁ : ∀ (n : ℕω) → List ℕω
  ω ↷₁ = ω ∷ []
  (# i) ↷₁ = ω ∷ # i ∷ []

  -- _↷ 

  _↷ : (c : Conf) → List Conf
  _↷ c = remove-c (vec-cartesian (Vec.map _↷₁ c))
    where remove-c = List.filter (λ c′ → ⌊ ¬? (c ≟Conf c′) ⌋)

  -- whistle

  _≤C_ : ∀ {k} → Vec ℕω k → Vec ℕω k → Set
  c₁ ≤C c₂ = Pointwise _≤ω_ c₁ c₂

  _≤C?_ : ∀ {k} → Decidable₂ (_≤C_ {k})
  _≤C?_ = Pointwise.decidable _≤ω?_

  ≤C-af : ∀ {k} → Almost-full (_≤C_ {k})
  ≤C-af {n} = Pointwise-af _≤ω_ ≤ω-af n
   
  afWh : BarWhistle Conf
  afWh = 
    ⟨ 
      ⋑-World.⋑↯ ≤C-world , 
      (λ c h → inj₂) , 
      ⋑-World.⋑↯? ≤C-world , 
      bar⋑↯⇔af⋑≫.af⟱⋑→bar⋑↯ ≤C-world [] (proj₁ (helper k)) (proj₂ (helper k))
    ⟩
    where
      ≤C-world = record { _⋑_ = _≤C_; _⋑?_ = _≤C?_ }
      
      helper : ∀ k → Almost-full⟱ (_≤C_ {k})
      helper k = af→af⟱ ≤C-af

  mkScWorld : (cntWorld : CntWorld {k}) → ScWorld
  mkScWorld ⟨⟨ start , _⇊ , unsafe ⟩⟩ = record
    { Conf = Conf
    ; _⊑_ = _⊑_
    ; _⊑?_ = _⊑?_
    ; _⇉ = λ c → c ⇊ ∷ List.map [_] (c ↷) -- driving + rebuilding
    ; whistle = afWh
    }

  scWorld : ScWorld
  scWorld = mkScWorld cntWorld

  open BigStepMRSC scWorld public
  open BigStepMRSC∞ scWorld public
  open BigStepMRSC∞-Ø scWorld public

  cl-unsafe : ∀ (l : LazyGraph Conf) → LazyGraph Conf
  cl-unsafe = cl-bad-conf unsafe

  cl∞-unsafe : ∀ (l : LazyCograph Conf) → LazyCograph Conf
  cl∞-unsafe = cl∞-bad-conf unsafe



--
-- A "DSL" for encoding counter systems in a user-friendly form.
--

infix 7 _≥_ _==_
infix 5 ¶_⇒_□

-- _≥_

_≥_ : ∀ (m : ℕω) (j : ℕ) → Bool
m ≥ n =
  ⌊ m ≥#? n ⌋

-- _==_

_==_ : ∀ (m : ℕω) (j : ℕ) → Bool

m == j =
  ⌊ m =#? j ⌋

-- _⇒_□

¶_⇒_□ : ∀ {k} (p : Bool) (result : Vec ℕω k) → List (Vec ℕω k)

¶ p ⇒ r □ =
  if p then r ∷ [] else []
