{-
In our model of big-step supercompilation whistles are assumed to be
"inductive bars". See:

Thierry Coquand. About Brouwer's fan theorem. September 23, 2003.
Revue internationale de philosophie, 2004/4 n° 230, p. 483-489.

http://www.cairn.info/revue-internationale-de-philosophie-2004-4-page-483.htm
http://www.cairn.info/load_pdf.php?ID_ARTICLE=RIP_230_0483

-}

module BarWhistles where

open import Level
  using ()
open import Data.Nat
open import Data.Nat.Properties
  using (≤′⇒≤; ≤⇒≤′; ≰⇒>; ≤-step)
open import Data.List as List
open import Data.List.Any as Any
  using (Any)
open import Data.List.Any.Properties
  using (∷↔; ++↔)
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.Vec as Vec
  using (Vec; []; _∷_; here; there; lookup)
open import Data.Product as Prod
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty
open import Data.Unit using (⊤; tt)

open import Function
open import Function.Equivalence
  using (_⇔_; equivalence)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)
open import Function.Inverse using (module Inverse)
open import Function.Equality
  using (_⟨$⟩_)

open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary
  using (_∈_; _∪_; _⊆_)
  renaming (Decidable to Decidable₁)

open import Relation.Binary
  using (Rel; _⇒_)
  renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

open import Induction.WellFounded


open import Util
open import AlmostFullRel

-- Bar

-- The set of finite paths such that either
-- (1) D h is valid right now; or
-- (2) for all possible a₁ ∷ h either
--     (1) D (a₁ ∷ h) is valid right now; or
--     (2) for all possible a₂ ∷ a₁ ∷ h either ...

data Bar {A : Set} (D : List A → Set) :
         (h : List A) → Set where
  now   : {h : List A} (bz : D h) → Bar D h
  later : {h : List A} (bs : ∀ c → Bar D (c ∷ h)) → Bar D h


record BarWhistle (A : Set) : Set₁ where

  -- Bar whistles deal with sequences of some entities
  -- (which in our model of supercompilations are configurations).

  constructor
    ⟨_,_,_,_⟩
  field

    -- Dangerous histories
    ↯ : (h : List A) → Set
    ↯∷ : (c : A) (h : List A) → ↯ h → ↯ (c ∷ h)
    ↯? : (h : List A) → Dec (↯ h)

    -- Bar-induction
    -- (In Coquand's terms, `Bar ↯` is required to be "an inductive bar".)
    bar[] : Bar ↯ []


-- BarGen

-- This module shows the generation of finite sequences
-- by means of a bar whistle.

module BarGen {A : Set} (g : List A → A) (w : BarWhistle A) where

  open BarWhistle w

  barGen′ : ∀ (h : List A) (b : Bar ↯ h) →
              ∃ λ (h′ : List A) → ↯ h′
  barGen′ h (now bz) = h , bz
  barGen′ h (later bs) with g h
  ... | c = barGen′ (c ∷ h) (bs c)

  barGen : ∃ λ (h : List A) → ↯ h
  barGen = barGen′ [] bar[]


-- A fan, or an finitely branching tree, is a tree
-- each node of which has a finite number of immediate successor nodes.

data Fan (A : Set) : Set where
  fan : List (A × Fan A) → Fan A

-- BarFanGen

-- This module shows the generation of finitely branching trees
-- by means of a bar whistle.

module BarFanGen
  {A : Set} (_⇉ : List A → List A) (w : BarWhistle A)
  where
  open BarWhistle w

  fanGen′ : (h : List A) (b : Bar ↯ h) → Fan A
  fanGen′ h (now bz) =
    fan []
  fanGen′ h (later bs) =
    fan (map (λ c → c , fanGen′ (c ∷ h) (bs c)) (h ⇉))

  fanGen : Fan A
  fanGen = fanGen′ [] bar[]

--
-- Bar D h is "monotonic" with respect to D.
--

-- bar-mono

bar-mono : ∀ {A : Set}
  {D D′ : ∀ (h : List A) → Set} →
  D  ⊆ D′ →
  (h : List A) (b : Bar D h) → Bar D′ h
bar-mono D→D′ h (now bz) =
  now (D→D′ bz)
bar-mono D→D′ h (later bs) =
  later (λ c → bar-mono D→D′ (c ∷ h) (bs c))

-- bar-⊎

bar-⊎ : {A : Set}
  {D P : ∀ (h : List A) → Set} →
  (h : List A) →
  Bar D h → Bar (D ∪ P) h
bar-⊎ h b = bar-mono inj₁ h b


--
-- Bar whistles based on the length of the sequence
--

-- pathLengthWhistle

pathLengthWhistle : (A : Set) (l : ℕ) → BarWhistle A

pathLengthWhistle A l = ⟨ ↯ , ↯∷ , ↯? , bar[] ⟩
  where

  ↯ : (h : List A) → Set
  ↯ h = l ≤ length h

  ↯∷ : (c : A) (h : List A) → ↯ h → ↯ (c ∷ h)
  ↯∷ c h dh = ≤-step dh

  ↯? : (h : List A) → Dec (↯ h)
  ↯? h = l ≤? length h

  bar : ∀ m (h : List A) (d : m + length h ≡ l) → Bar ↯ h
  bar zero h d =
    now (subst (_≤_ l) (P.sym d) (≤′⇒≤ ≤′-refl))
  bar (suc m) h d =
    later (λ c → bar m (c ∷ h) m+1+n≡l)
    where
    open ≡-Reasoning
    m+1+n≡l = begin
      m + suc (length h) ≡⟨ m+1+n≡1+m+n m (length h) ⟩
      suc (m + length h) ≡⟨ d ⟩
      l ∎

  bar[] : Bar ↯ []
  bar[] = bar l [] (l + zero ≡ l ∋ proj₂ *+.+-identity l)

--
-- Bar whistles based on inverse image
--

-- inverseImageWhistle

inverseImageWhistle : {A B : Set} (f : A → B)
  (w : BarWhistle B) → BarWhistle A

inverseImageWhistle {A} {B} f ⟨ d , d∷ , d? , bd[] ⟩ =
  ⟨ d ∘ map f , ↯∷ , d? ∘ map f , bar [] bd[] ⟩
  where

  ↯∷ : (c : A) (h : List A) →
    d (map f h) → d (f c ∷ map f h)
  ↯∷ c h dh = d∷ (f c) (map f h) dh

  bar : (h : List A) (b : Bar d (map f h)) → Bar (d ∘ map f) h
  bar h (now bz) = now bz
  bar h (later bs) = later (λ c → bar (c ∷ h) (bs (f c)))

--
-- Bar whistles based on well-founded relations
--

-- wfWhistle

wfWhistle : ∀ {A : Set} (_<_ : Rel A Level.zero) → Decidable₂ _<_ →
              (wf : Well-founded _<_) → BarWhistle A
wfWhistle {A} _<_ _<?_ wf = ⟨ ↯ , ↯∷ , ↯? , bar[] ⟩
  where

  ↯ : (h : List A) → Set
  ↯ [] = ⊥
  ↯ (c ∷ []) = ⊥
  ↯ (c′ ∷ c ∷ h) = ¬ c′ < c ⊎ ↯ (c ∷ h)

  ↯∷ : (c : A) (h : List A) → ↯ h → ↯ (c ∷ h)
  ↯∷ c [] dh = dh
  ↯∷ c (c′ ∷ h) dh = inj₂ dh

  ↯? : (h : List A) → Dec (↯ h)
  ↯? [] = no id
  ↯? (c ∷ []) = no id
  ↯? (c′ ∷ c ∷ h) = helper (↯? (c ∷ h))
    where
    helper : Dec (↯ (c ∷ h)) → Dec (¬ (c′ < c) ⊎ ↯ (c ∷ h))
    helper (yes dch) = yes (inj₂ dch)
    helper (no ¬dch) with c′ <? c
    ... | yes c′<c = no [ (λ c′≮c → c′≮c c′<c) , ¬dch ]′
    ... | no  c′≮c = yes (inj₁ c′≮c)

  bar : ∀ c (h : List A) → Acc _<_ c → Bar ↯ (c ∷ h)
  bar c h (acc rs) with ↯? (c ∷ h)
  ... | yes dch = now dch
  ... | no ¬dch = later helper
    where helper : ∀ c′ → Bar ↯ (c′ ∷ c ∷ h)
          helper c′ with c′ <? c
          ... | yes c′<c = bar c′ (c ∷ h) (rs c′ c′<c)
          ... | no  c′≮c = now (inj₁ c′≮c)

  bar[] : Bar ↯ []
  bar[] = later (λ c → bar c [] (wf c))

-- wfGenWhistle

wfGen↯ : ∀ {A : Set} (_<_ : Rel A Level.zero) (h : List A) → Set
wfGen↯ _<_ [] = ⊥
wfGen↯ _<_ (c ∷ h) = Any (λ c' → ¬ c < c') h ⊎ wfGen↯ _<_ h

wfGenBarHelper : ∀ {A : Set} (_<_ : Rel A Level.zero) → Decidable₂ _<_ →
             ∀ c (h : List A) → Acc _<_ c → Bar (wfGen↯ _<_) (c ∷ h)
wfGenBarHelper {A} _<_ _<?_ c h (acc rs) with Any.any (λ c' → ¬? (c <? c')) h
wfGenBarHelper {A} _<_ _<?_ c h (acc rs) | yes dch = now (inj₁ dch)
wfGenBarHelper {A} _<_ _<?_ c h (acc rs) | no ¬dch = later helper
    where
    helper : (c' : A) → Bar (wfGen↯ _<_) (c' ∷ c ∷ h)
    helper c' with c' <? c
    helper c' | yes c'<c = wfGenBarHelper _<_ _<?_ c' (c ∷ h) (rs c' c'<c)
    helper c' | no ¬c'<c = now (inj₁ (Any.here ¬c'<c))

wfGenBar : ∀ {A : Set} (_<_ : Rel A Level.zero) → Decidable₂ _<_ →
             ∀ (h : List A) → Well-founded _<_ → Bar (wfGen↯ _<_) h
wfGenBar _<_ _<?_ h wf-c = later (λ c → wfGenBarHelper _<_ _<?_ c h (wf-c c)) 

wfGenWhistle : ∀ {A : Set} (_<_ : Rel A Level.zero) → Decidable₂ _<_ →
                (wf : Well-founded _<_) → BarWhistle A
wfGenWhistle {A} _<_ _<?_ wf = ⟨ ↯ , ↯∷ , ↯? , bar[] ⟩
  where

  ↯ = wfGen↯ _<_

  ↯∷ : (c : A) (h : List A) → ↯ h → ↯ (c ∷ h)
  ↯∷ c h dh = inj₂ dh

  ↯? : (h : List A) → Dec (↯ h)
  ↯? [] = no id
  ↯? (c ∷ h) with Any.any (λ c' → ¬? (c <? c')) h 
  ↯? (c ∷ h) | yes dch = yes (inj₁ dch)
  ↯? (c ∷ h) | no ¬dch with ↯? h
  ↯? (c ∷ h) | no ¬dch | yes dh = yes (inj₂ dh)
  ↯? (c ∷ h) | no ¬dch | no ¬dh = no (λ dch → helper ¬dch ¬dh dch)
    where
    helper : ¬(Any (λ c' → ¬ c < c') h) → ¬ (↯ h) → ↯ (c ∷ h) → ⊥
    helper ¬dch₁ ¬dh₁ (inj₁ dch) = ¬dch₁ dch
    helper ¬dch₁ ¬dh₁ (inj₂ dh) = ¬dh₁ dh

  bar[] : Bar ↯ []
  bar[] = wfGenBar _<_ _<?_ [] wf

--
-- Whistles based on the idea that some elements of the sequence
-- "cover" other elements.
-- c′ ⋑ c means that c′ "covers" c.
--

record ⋑-World (A : Set) : Set₁ where

  infix 4 _⋑_ _⋑?_ _⋑⋑_  _⋑⋑?_

  field
    _⋑_ : A → A → Set
    _⋑?_ : Decidable₂ _⋑_

  -- _⋑⋑_

  _⋑⋑_ : (h : List A) (c : A) → Set
  h ⋑⋑ c = Any (flip _⋑_ c) h

  -- ⋑↯

  ⋑↯ : (h : List A) → Set
  ⋑↯ [] = ⊥
  ⋑↯ (c ∷ h) = h ⋑⋑ c ⊎ ⋑↯ h

  -- _⋑⋑?_

  _⋑⋑?_ : (h : List A) (c : A) → Dec (h ⋑⋑ c)
  h ⋑⋑? c = Any.any (flip _⋑?_ c) h

  -- ⋑↯?

  ⋑↯? : (h : List A) → Dec (⋑↯ h)
  ⋑↯? [] = no id
  ⋑↯? (c ∷ h) with h ⋑⋑? c
  ... | yes ⋑c = yes (inj₁ ⋑c)
  ... | no ¬⋑c with ⋑↯? h
  ... | yes dh = yes (inj₂ dh)
  ... | no ¬dh = no [ ¬⋑c , ¬dh ]′

-- ⋑-whistle

⋑-whistle : {A : Set} (⋑-world : ⋑-World A)
            (⋑-bar[] : Bar (⋑-World.⋑↯ ⋑-world) []) → BarWhistle A
⋑-whistle ⋑-world ⋑-bar[] =
  ⟨ ⋑↯ , (λ c h → inj₂) , ⋑↯? , ⋑-bar[] ⟩
  where open ⋑-World ⋑-world


--
-- Almost-full relations
--

module bar⋑↯⇔af⋑≫ {A : Set} (⋑-world : ⋑-World A) where

  open ⋑-World ⋑-world

  ⋑≫ : (h : List A) (x y : A) → Set
  ⋑≫ h x y = ⋑↯ (x ∷ h) ⊎ (x ⋑ y)

  -- bar⋑↯→af⋑≫

  bar⋑↯→af⋑≫ : (h : List A) →
                  Bar ⋑↯ h → Almost-full (⋑≫ h)
  bar⋑↯→af⋑≫ h (now bz) =
    now (λ x y → inj₁ (inj₂ bz))
  bar⋑↯→af⋑≫ h (later bs) =
    later {_≫_ = ⋑≫ h} (λ c → af-⇒ (step c) (afch c))
    where
    open ∼-Reasoning
    afch : ∀ c → Almost-full (⋑≫ (c ∷ h))
    afch c = bar⋑↯→af⋑≫ (c ∷ h) (bs c)
    step : ∀ c {x} {y} → ⋑≫ (c ∷ h) x y → ⋑≫ h x y ⊎ ⋑≫ h c x
    step c {x} {y} =
      ⋑≫ (c ∷ h) x y
        ↔⟨ _ ∎ ⟩
      (⋑↯ (x ∷ c ∷ h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ((c ∷ h ⋑⋑ x ⊎ ⋑↯ (c ∷ h)) ⊎ x ⋑ y)
        ↔⟨ ((sym $ ∷↔ (flip _⋑_ x)) ⊎-cong ((h ⋑⋑ c ⊎ ⋑↯ h) ∎)) ⊎-cong
                            ((x ⋑ y) ∎) ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ (h ⋑⋑ c ⊎ ⋑↯ h)) ⊎ x ⋑ y)
        ∼⟨ [ [ [ inj₂ ∘ inj₂ , inj₁ ∘ inj₁ ∘ inj₁ ]′ ,
             [ inj₂ ∘ inj₁ ∘ inj₁ , inj₁ ∘ inj₁ ∘ inj₂ ]′ ]′
             , inj₁ ∘ inj₂ ]′ ⟩
      (((h ⋑⋑ x ⊎ ⋑↯ h) ⊎ x ⋑ y) ⊎ ((h ⋑⋑ c ⊎ ⋑↯ h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      ((⋑↯ (x ∷ h) ⊎ x ⋑ y) ⊎ (⋑↯ (c ∷ h) ⊎ c ⋑ x))
        ↔⟨ _ ∎ ⟩
      (⋑≫ h x y ⊎ ⋑≫ h c x)
      ∎

  -- af⟱⋑≫→bar⋑↯

  af⟱⋑≫→bar⋑↯ : (h : List A)
    (t : WFT A) → ⋑≫ h ⟱ t → Bar ⋑↯ h

  af⟱⋑≫→bar⋑↯ h now R⟱ =
    later (λ c → later (λ c′ → now (helper c′ c (R⟱ c c′))))
    where
    open ∼-Reasoning
    helper : ∀ c′ c → ⋑↯ (c ∷ h) ⊎ c ⋑ c′ → ⋑↯ (c′ ∷ c ∷ h)
    helper c′ c =
      (⋑↯ (c ∷ h) ⊎ c ⋑ c′)
        ∼⟨ [ inj₂ , inj₁ ∘ inj₁ ]′ ⟩
      ((c ⋑ c′ ⊎ (h ⋑⋑ c′)) ⊎ ⋑↯ (c ∷ h))
        ↔⟨ ∷↔ (flip _⋑_ c′) ⊎-cong (⋑↯ (c ∷ h) ∎) ⟩
      (c ∷ h ⋑⋑ c′ ⊎ ⋑↯ (c ∷ h))
        ↔⟨ _ ∎ ⟩
      ⋑↯ (c′ ∷ c ∷ h) ∎ 

  af⟱⋑≫→bar⋑↯ h (later s) R⟱ = later (λ c → helper c)
    where
    open ∼-Reasoning
    step : ∀ c {x y} → ⋑≫ h x y ⊎ ⋑≫ h c x → ⋑≫ (c ∷ h) x y
    step c {x} {y} =
      (⋑≫ h x y ⊎ ⋑≫ h c x)
        ↔⟨ _ ∎ ⟩
      ((⋑↯ (x ∷ h) ⊎ x ⋑ y) ⊎ ⋑↯ (c ∷ h) ⊎ c ⋑ x)
        ↔⟨ _ ∎ ⟩
      (((h ⋑⋑ x ⊎ ⋑↯ h) ⊎ x ⋑ y) ⊎ (h ⋑⋑ c ⊎ ⋑↯ h) ⊎ c ⋑ x)
        ∼⟨ [ [ [ inj₁ ∘ inj₁ ∘ inj₂ , inj₁ ∘ inj₂ ∘ inj₂ ]′ , inj₂ ]′ ,
             [ [ inj₁ ∘ inj₂ ∘ inj₁ , inj₁ ∘ inj₂ ∘ inj₂ ]′ ,
                 inj₁ ∘ inj₁ ∘ inj₁ ]′ ]′ ⟩
      (((c ⋑ x ⊎ h ⋑⋑ x) ⊎ h ⋑⋑ c ⊎ ⋑↯ h) ⊎ x ⋑ y)
        ↔⟨ ((∷↔ (flip _⋑_ x)) ⊎-cong ((h ⋑⋑ c ⊎ ⋑↯ h) ∎)) ⊎-cong
                (x ⋑ y ∎) ⟩
      ((c ∷ h ⋑⋑ x ⊎ ⋑↯ (c ∷ h)) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      (⋑↯ (x ∷ c ∷ h) ⊎ x ⋑ y)
        ↔⟨ _ ∎ ⟩
      ⋑≫ (c ∷ h) x y
      ∎

    helper : ∀ c → Bar ⋑↯ (c ∷ h)
    helper c =
      af⟱⋑≫→bar⋑↯ (c ∷ h) (s c) (⟱-⇒ (step c) (s c) (R⟱ c))

  -- af⋑≫→bar⋑↯

  af⋑≫→bar⋑↯ : (h : List A) → Almost-full (⋑≫ h) → Bar ⋑↯ h

  af⋑≫→bar⋑↯ h af with af→af⟱ af
  ... | t , R⟱ = af⟱⋑≫→bar⋑↯ h t R⟱

  --
  -- bar⋑↯⇔af⋑≫
  --

  bar⋑↯⇔af⋑≫ : (h : List A) →
    Bar ⋑↯ h ⇔ Almost-full (⋑≫ h)

  bar⋑↯⇔af⋑≫ h = equivalence (bar⋑↯→af⋑≫ h) (af⋑≫→bar⋑↯ h)

---
-- An alternative construction of a bar from an almost-full relation
---

{-
  af⟱⋑→bar⋑↯ : (∀ x y z → x ⋑ y → ¬ z ⋑ y → x ⋑ z) → (h : List A)
    (t : WFT A) → _⋑_ ⟱ t → Bar ⋑↯ h

  af⟱⋑→bar⋑↯ ⋑prop h t R⟱ = 
    bar-mono (λ {h} dh → wfGen↯⇒⋑↯ h dh) h 
      (wfGenBar (λ x y → ¬ y ⋑ x) ¬y⋑x-dec h 
        (af⇒wf _⋑_ (λ x y → ¬ y ⋑ x) (λ x y p → 
          helper x y 
            ((tr-clos⇒TrClos1n (λ x₁ y₁ → ¬ y₁ ⋑ x₁) x y (proj₁ p)) , (proj₂ p))) t R⟱))
    where
      ¬¬x⋑y⇒x⋑y : ∀ x y → ¬ ¬ x ⋑ y → x ⋑ y
      ¬¬x⋑y⇒x⋑y x y ¬¬x⋑y with x ⋑? y 
      ¬¬x⋑y⇒x⋑y x y ¬¬x⋑y | yes x⋑y = x⋑y
      ¬¬x⋑y⇒x⋑y x y ¬¬x⋑y | no ¬x⋑y = ⊥-elim (¬¬x⋑y ¬x⋑y)

      wfGen↯⇒⋑↯ : ∀ h → wfGen↯ (λ x y → ¬ y ⋑ x) h → ⋑↯ h
      wfGen↯⇒⋑↯ [] wfd[] = wfd[]
      wfGen↯⇒⋑↯ (c ∷ h) (inj₁ exc'h) = 
        inj₁ (Any.map (λ {c'} ¬¬c'⋑c → ¬¬x⋑y⇒x⋑y c' c ¬¬c'⋑c) exc'h)
      wfGen↯⇒⋑↯ (c ∷ h) (inj₂ dh) = inj₂ (wfGen↯⇒⋑↯ h dh)

      ¬y⋑x-dec : ∀ x y → Dec (¬ y ⋑ x)
      ¬y⋑x-dec x y with y ⋑? x
      ¬y⋑x-dec x y | yes y⋑x = no (λ z → z y⋑x)
      ¬y⋑x-dec x y | no ¬y⋑x = yes ¬y⋑x

      helper : (x y : A) → TrClos1n (λ x₁ y₁ → ¬ y₁ ⋑ x₁) x y × y ⋑ x → ⊥
      helper x y (step1n .x .y ¬y₁⋑x , y⋑x) = ¬y₁⋑x y⋑x
      helper x y (trans1n .x y₁ .y ¬y₁⋑x tr-y₁-y , y⋑x) = 
        helper y₁ y (tr-y₁-y , ⋑prop y x y₁ y⋑x ¬y₁⋑x)

  af⋑→bar⋑↯ : (∀ x y z → x ⋑ y → ¬ z ⋑ y → x ⋑ z) →
    (h : List A) → Almost-full _⋑_ → Bar ⋑↯ h
  af⋑→bar⋑↯ ⋑prop h af with af→af⟱ af
  ... | t , R⟱ = af⟱⋑→bar⋑↯ ⋑prop h t R⟱

-}

  af⟱⋑→bar⋑↯ : (h : List A) (t : WFT A) → _⋑_ ⟱ t → Bar ⋑↯ h

  af⟱⋑→bar⋑↯ h t R⟱ = wfRec _ body h
    where
      tryHd : ∀ {ℓ} {A : Set ℓ} → List A → A ⊎ ⊤
      tryHd [] = inj₂ tt
      tryHd (x ∷ xs) = inj₁ x

      afBarHelperAFRel : Rel (List A) Level.zero
      afBarHelperAFRel h1 h2 = sum-lift _⋑_ _≡_ (tryHd h1) (tryHd h2)

      afBarHelperAFRel-af : Almost-full afBarHelperAFRel
      afBarHelperAFRel-af = 
        af-inverseImage tryHd 
          (af-sum-lift _⋑_ _≡_ (af⟱→af (t , R⟱)) af-⊤)

      afBarStepRel : Rel (List A) Level.zero
      afBarStepRel h1 h2 = ∃ (λ c → h1 ≡ c ∷ h2 × ¬ Any (λ c' → c' ⋑ c) h2)

      TrClos-afBarStepRel-app : ∀ h1 h2 → TrClos1n afBarStepRel h1 h2 → ∃ (λ h → h1 ≡ h ++ h2)
      TrClos-afBarStepRel-app h1 h2 (step1n .h1 .h2 (c , h1≡c∷h2 , ¬Any)) rewrite h1≡c∷h2 = 
        c ∷ [] , refl
      TrClos-afBarStepRel-app h1 h2 (trans1n .h1 h .h2 (c , h1≡c∷h , ¬Any) trc) 
        with TrClos-afBarStepRel-app _ _ trc
      ... | h' , h≡h'++h2 rewrite h≡h'++h2 = c ∷ h' , h1≡c∷h

      afBarStepRel-wf : Well-founded afBarStepRel
      afBarStepRel-wf = af⇒wf afBarHelperAFRel afBarStepRel 
        afBarHelperAFRel-af (λ h1 h2 p → 
          helper h1 h2 ((TrClos⇒TrClos1n afBarStepRel h1 h2 (proj₁ p)) , proj₂ p))
        where
          helper1 : ∀ c c' h' h2 → c' ⋑ c → Any (λ c'' → c'' ⋑ c) (h' ++ c' ∷ h2)
          helper1 c c' h' h2 c'⋑c = 
            Inverse.to (++↔ {xs = h'} {ys = c' ∷ h2}) ⟨$⟩ inj₂ (Any.here c'⋑c)

          helper : (x y : List A) → TrClos1n afBarStepRel x y × afBarHelperAFRel y x → ⊥
          helper h1 [] (step1n .h1 .[] (c , h1≡c∷[] , ¬Any⋑h2) , Ryx) 
            rewrite h1≡c∷[] = Level.lower Ryx
          helper h1 (c' ∷ h2) (step1n .h1 .(c' ∷ h2) (c , h1≡c∷c'∷h2 , ¬Any⋑h2) , Ryx) 
            rewrite h1≡c∷c'∷h2 = ¬Any⋑h2 (Any.here Ryx)
          helper h1 h2 (trans1n .h1 h .h2 (c , h1≡c∷h , ¬Any⋑h) trcThh2 , Ryx) 
            with TrClos-afBarStepRel-app _ _ trcThh2
          helper h1 [] (trans1n .h1 h₁ .[] (c , h1≡c∷h , ¬Any⋑h) trcThh2 , Ryx) 
            | h' , h≡h'++h2 rewrite h≡h'++h2 | h1≡c∷h = Level.lower Ryx
          helper h1 (c' ∷ h2) (trans1n .h1 h₁ .(c' ∷ h2) (c , h1≡c∷h , ¬Any⋑h) trcThh2 , Ryx)
            | h' , h≡h'++h2 rewrite h≡h'++h2 | h1≡c∷h = ¬Any⋑h (helper1 c c' h' h2 Ryx) 

      open All afBarStepRel-wf

      body : ∀ h1 → (∀ h2 → afBarStepRel h2 h1 → Bar ⋑↯ h2) → Bar ⋑↯ h1
      body h rec = later body1
        where
          body1 : ∀ (c : A) → Bar ⋑↯ (c ∷ h)
          body1 c with Any.any (λ c' → c' ⋑? c) h
          body1 c | yes p = now (inj₁ p)
          body1 c | no ¬p = rec (c ∷ h) (c , (refl , ¬p))

