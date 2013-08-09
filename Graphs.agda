--
-- Graphs of configurations
--

module Graphs where

open import Algebra
  using (module Monoid)
open import Data.Bool
  using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.Fin as F
  using (Fin; zero; suc)
open import Data.List as List
open import Data.List.Properties
  using (∷-injective; map-compose)
open import Data.List.Any
  using (Any; here; there; module Membership-≡)
open import Data.List.Any.Properties
  using (Any-cong; Any↔; ++↔; return↔; map↔; concat↔; ⊎↔)
open import Data.List.Any.Membership as MB
  using (map-∈↔)
open import Data.Product
  using (_×_; _,_; ,_; proj₁; proj₂; Σ; ∃; ∃₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Maybe
  using (Maybe; nothing; just)
open import Data.Unit
  using (⊤; tt)

open import Function
open import Function.Inverse as Inv
  using (_↔_; module Inverse)
open import Function.Related as Related
  using ()
  renaming (module EquationalReasoning to ∼-Reasoning)

import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Relation.Binary.List.Pointwise as Pointwise
  using ([]; _∷_)

open import Relation.Nullary

open import Relation.Binary.PropositionalEquality as P
  hiding (sym)
  renaming ([_] to P[_])

private
  module LM {a} {A : Set a} = Monoid (List.monoid A)

open import Util

--
-- Graphs of configurations
--

-- A `Graph C` is supposed to represent a residual program.
-- Technically, a `Graph C` is a tree, with `back` nodes being
-- references to parent nodes.
-- 
-- A graph's nodes contain configurations. Here we abstract away
-- from the concrete structure of configurations.
-- In this model the arrows in the graph carry no information,
-- because, this information can be kept in nodes.
-- (Hence, this information is supposed to be encoded inside
-- "configurations".)
--
-- To simplify the machinery, back-nodes in this model of
-- supercompilation do not contain explicit references
-- to parent nodes. Hence, `back c` means that `c` is foldable
-- to a parent configuration (perhaps, to several ones).
-- 
-- * Back-nodes are produced by folding a configuration to another
--   configuration in the history.
-- * Split-nodes are produced by decomposing a configuration into
--   a number of other configurations (e.g. by driving or taking apart
--   a let-expression).
-- * Rebuild nodes are produced by rewriting a configuration by another
--   one (e.g. by generalization, introducing a let-expression or
--   applying a lemma during two-level supercompilation).

-- Graph

data Graph (C : Set) : Set where
  back    : ∀ (c : C) → Graph C
  split   : ∀ (c : C) (gs : List (Graph C)) → Graph C
  rebuild : ∀ (c : C) (g : Graph C) → Graph C

--
-- Lazy graphs of configuration
--

-- A `LazyGraph C` represents a finite set of graphs
-- of configurations (whose type is `Graph C`).
--
-- "Lazy" graphs of configurations will be produced
-- by the "lazy" (staged) version of multi-result
-- supercompilation.

-- LazyGraph

data LazyGraph (C : Set) : Set where
  ⁇      : ⊥ → LazyGraph C
  Ø       : LazyGraph C
  alt     : (gs₁ gs₂ : LazyGraph C) → LazyGraph C
  back    : ∀ (c : C) → LazyGraph C
  split   : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C
  rebuild : ∀ (c : C) (gss : List (LazyGraph C)) →
              LazyGraph C

-- The semantics of `LazyGraph C` is formally defined by
-- the function `⟪_⟫` that generates a list of `Graph C n`
-- from  a `LazyGraph C`.

mutual

  -- ⟪_⟫

  ⟪_⟫ : {C : Set} (gs : LazyGraph C) → List (Graph C)

  ⟪ ⁇ a⊥ ⟫ =
    ⊥-elim a⊥
  ⟪ Ø ⟫ =
    []
  ⟪ alt gs₁ gs₂ ⟫ =
    ⟪ gs₁ ⟫ ++ ⟪ gs₂ ⟫
  ⟪ back c ⟫ =
    [ back c ]
  ⟪ split c gss ⟫ =
    map (split c) (cartesian ⟪ gss ⟫*)
  ⟪ rebuild c gss ⟫ =
    map (rebuild c) (concat ⟪ gss ⟫*)

  -- ⟪_⟫*

  ⟪_⟫* : {C : Set} (gss : List (LazyGraph C)) →
              List (List (Graph C))
  ⟪ [] ⟫* = []
  ⟪ gs ∷ gss ⟫* = ⟪ gs ⟫ ∷ ⟪ gss ⟫*

-- `⟪_⟫*` has only been introduced to make the termination
-- checker happy. Actually, it is equivalent to `map ⟪_⟫`.

-- ⟪⟫*-is-map

⟪⟫*-is-map : {C : Set} (gss : List (LazyGraph C)) →
  ⟪ gss ⟫* ≡ map ⟪_⟫ gss

⟪⟫*-is-map [] = refl
⟪⟫*-is-map (gs ∷ gss) =
  cong (_∷_ ⟪ gs ⟫) (⟪⟫*-is-map gss)


--
-- Usually, we are not interested in the whole bag `⟪ gs ⟫`.
-- The goal is to find "the best" or "most interesting" graphs.
-- Hence, there should be developed some techniques of extracting
-- useful information from a `LazyGraph C n` without evaluating
-- `⟪ gs ⟫` directly.

-- This can be formulated in the following form.
-- Suppose that a function `select` filters bags of graphs,
-- removing "bad" graphs, so that
--
--     select ⟪ gs ⟫
--
-- generates the bag of "good" graphs.
-- Let us find a function `extract` such that
--
--     extract gs ≡ select ⟪ gs ⟫
--
-- In many cases, `extract` may be more efficient (by several orders
-- of magnityde) than the composition `select ∘ ⟪_⟫`.

-- Sometimes, `extract` can be formulated in terms of "cleaners" of
-- lazy graphs. Let `clean` be a function that transforms lazy graphs,
-- such that
--
--     ⟪ clean gs ⟫ ⊆ ⟪ gs ⟫
--
-- Then `extract` can be constructed in the following way:
--
--     extract gs = ⟪ clean gs ⟫
--
-- Theoretically speaking, `clean` is the result of "promoting" `select`:
--
--     select ∘ ⟪_⟫ ≡ ⟪_⟫ ∘ clean
--
-- The nice property of cleaners is that they are composable:
-- given `cleaner₁` and `cleaner₂`, `cleaner₂ ∘ cleaner₁` is also a cleaner.
--

--
-- Some cleaners
--

--
-- A cleaner that removes subtrees that represent empty sets of graphs.
--

mutual

  -- cl-empty′

  cl-empty′ : {C : Set} (gs : LazyGraph C) →
    Maybe (LazyGraph C)

  cl-empty′ (⁇ a⊥) =
    nothing
  cl-empty′ Ø =
    nothing
  cl-empty′ (alt gs₁ gs₂) with cl-empty′ gs₁ | cl-empty′ gs₂
  ... | nothing | gs₂′ = gs₂′
  ... | gs₁′ | nothing = gs₁′
  ... | just gs₁′ | just gs₂′ = just (alt gs₁′ gs₂′)
  cl-empty′ (back c) =
    just (back c)
  cl-empty′ (split c gss) with cl-empty-∧ gss
  ... | nothing = nothing
  ... | just gss′ = just (split c gss′)
  cl-empty′ (rebuild c gss) with cl-empty-∨ gss
  ... | [] = nothing
  ... | gss′ = just (rebuild c gss′)

  -- cl-empty-∨

  cl-empty-∨ : {C : Set} (gss : List (LazyGraph C)) →
    List (LazyGraph C)

  cl-empty-∨ [] = []
  cl-empty-∨ (gs ∷ gss) with cl-empty′ gs | cl-empty-∨ gss
  ... | nothing | gss′ = gss′
  ... | just gs′ | gss′ = gs′ ∷ gss′

  -- cl-empty-∧

  cl-empty-∧ : {C : Set} (gss : List (LazyGraph C)) →
    Maybe (List (LazyGraph C))

  cl-empty-∧ [] = just []
  cl-empty-∧ (gs ∷ gss) with cl-empty′ gs
  ... | nothing = nothing
  ... | just gs′ with cl-empty-∧ gss
  ... | nothing = nothing
  ... | just gss′ = just (gs′ ∷ gss′)

  -- cl-empty

  cl-empty : {C : Set} (gs : LazyGraph C) → LazyGraph C

  cl-empty gs with cl-empty′ gs
  ... | nothing = Ø
  ... | just gs′ = gs′

--
-- `cl-empty` is correct
--

mutual

  -- cl-empty-correct

  cl-empty-correct : ∀ {C : Set} (gs : LazyGraph C) →
    ⟪ cl-empty gs ⟫ ≡ ⟪ gs ⟫

  cl-empty-correct (⁇ a⊥) =
    ⊥-elim a⊥
  cl-empty-correct Ø =
    refl
  cl-empty-correct (alt gs₁ gs₂)
    rewrite P.sym $ cl-empty-correct gs₁
          | P.sym $ cl-empty-correct gs₂
    with cl-empty′ gs₁ | cl-empty′ gs₂
  ... | nothing | nothing = refl
  ... | nothing | just gs′₂ = refl
  ... | just gs′₁ | nothing = begin
    ⟪ gs′₁ ⟫
      ≡⟨ P.sym $ proj₂ LM.identity ⟪ gs′₁ ⟫ ⟩
    ⟪ gs′₁ ⟫ ++ []
    ∎ where open ≡-Reasoning
  ... | just gs′₁ | just gs′₂ = refl
  cl-empty-correct (back c) =
    refl
  cl-empty-correct (split c gss) with cl-empty-∧ gss | inspect cl-empty-∧ gss
  ... | nothing | P[ ≡nothing ]
    rewrite cl-empty-∧-nothing gss ≡nothing = refl
  ... | just gss′ | P[ ≡just ]
    rewrite cl-empty-∧-just gss gss′ ≡just = refl
  cl-empty-correct (rebuild c gss)
    with cl-empty-∨ gss | inspect cl-empty-∨ gss
  ... | [] | P[ ≡[] ] rewrite cl-empty-∨-correct gss [] ≡[] = refl
  ... | gs′ ∷ gss′ | P[ ≡gs′∷gss′ ]
    rewrite cl-empty-∨-correct gss (gs′ ∷ gss′) ≡gs′∷gss′ = refl

  -- cl-empty-∧-nothing

  cl-empty-∧-nothing : ∀ {C : Set} (gss : List (LazyGraph C)) →
    cl-empty-∧ gss ≡ nothing → cartesian ⟪ gss ⟫* ≡ []

  cl-empty-∧-nothing [] ()
  cl-empty-∧-nothing (gs ∷ gss) eq  with cl-empty′ gs | inspect cl-empty′ gs
  cl-empty-∧-nothing (gs ∷ gss) eq | nothing | P[ ≡nothing ]
    rewrite P.sym $ cl-empty-nothing gs ≡nothing = refl
  cl-empty-∧-nothing (gs ∷ gss) eq | just gs′ | P[ ≡gs′ ]
    with cl-empty-∧ gss | inspect cl-empty-∧ gss
  cl-empty-∧-nothing (gs ∷ gss) eq | just gs′ | P[ ≡gs′ ] | nothing | P[ ≡gss′ ]
    rewrite cl-empty-∧-nothing gss ≡gss′ | cartesian2[] (⟪ gs ⟫)
    = refl
  cl-empty-∧-nothing (gs ∷ gss) () | just gs′ | P[ ≡gs′ ] | just gss′ | _

  -- cl-empty-∧-just

  cl-empty-∧-just : ∀ {C : Set} (gss gss′ : List (LazyGraph C)) →
    cl-empty-∧ gss ≡ just gss′ → ⟪ gss ⟫* ≡ ⟪ gss′ ⟫*

  cl-empty-∧-just [] [] eq = refl
  cl-empty-∧-just [] (gs′ ∷ gss′) ()
  cl-empty-∧-just (gs ∷ gss) gss′ eq with cl-empty′ gs | inspect cl-empty′ gs
  cl-empty-∧-just (gs ∷ gss) gss′ () | nothing | _
  ... | just gs₁ | ≡just-gs₁
    with cl-empty-∧ gss | inspect cl-empty-∧ gss
  cl-empty-∧-just (gs ∷ gss) gss′ ()
    | just gs₁ | ≡just-gs₁ | nothing | _ 
  cl-empty-∧-just (gs ∷ gss) .(gs₁ ∷ gss₁) refl
    | just gs₁ | P[ ≡gs₁ ] | just gss₁ | P[ ≡gss₁ ]
    rewrite cl-empty-just gs gs₁ ≡gs₁ | cl-empty-∧-just gss gss₁ ≡gss₁ = refl

  -- cl-empty-∨-correct

  cl-empty-∨-correct :
    ∀ {C : Set} (gss : List (LazyGraph C)) (gss′ : List (LazyGraph C)) →
    cl-empty-∨ gss ≡ gss′ →
      concat ⟪ gss ⟫* ≡ concat ⟪ gss′ ⟫*

  cl-empty-∨-correct [] [] ≡gss′ = refl
  cl-empty-∨-correct [] (x ∷ gss′) ()
  cl-empty-∨-correct (gs ∷ gss) gss′ ≡gss′
    with cl-empty′ gs | inspect cl-empty′ gs
  ... | nothing | P[ ≡nothing ]
    rewrite P.sym $ cl-empty-nothing gs ≡nothing
          | cl-empty-∨-correct gss gss′ ≡gss′ = refl
  cl-empty-∨-correct (gs ∷ gss) [] () | just gs₁ | P[ ≡just ]
  cl-empty-∨-correct (gs ∷ gss) (gs′  ∷ gss′) ≡gs′∷gss′ | just gs₁ | P[ ≡just ]
    with ∷-injective ≡gs′∷gss′
  ... | gs₁≡gs′ , ≡gss′
    rewrite gs₁≡gs′
          | cl-empty-just gs gs′ ≡just | cl-empty-∨-correct gss gss′ ≡gss′
    = refl

  -- cl-empty-nothing

  cl-empty-nothing : ∀ {C : Set} (gs : LazyGraph C) →
    cl-empty′ gs ≡ nothing → [] ≡ ⟪ gs ⟫

  cl-empty-nothing gs ≡nothing with cl-empty-correct gs
  ... | []≡ rewrite ≡nothing = []≡

  -- cl-empty-just

  cl-empty-just : ∀ {C : Set} (gs gs′ : LazyGraph C) →
    cl-empty′ gs ≡ just gs′ → ⟪ gs′ ⟫ ≡ ⟪ gs ⟫

  cl-empty-just gs gs′ ≡just with cl-empty-correct gs
  ... | cl≡ rewrite ≡just  = cl≡

--
-- Removing graphs that contain "bad" configurations.
-- Configurations represent states of a computation process.
-- Some of these states may be "bad" with respect to the problem
-- that is to be solved by means of supercompilation.
--
-- The cleaner `cl-bad-conf` assumes "badness" to be monotonic,
-- in the sense that a single "bad" configuration spoils the whole
-- graph it appears in.

mutual

  -- cl-bad-conf

  cl-bad-conf : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
    LazyGraph C

  cl-bad-conf bad (⁇ a⊥) =
    ⁇ a⊥
  cl-bad-conf bad Ø =
    Ø
  cl-bad-conf bad (alt gs₁ gs₂) =
    alt (cl-bad-conf bad gs₁) (cl-bad-conf bad gs₂)
  cl-bad-conf bad (back c) =
    if bad c then Ø else (back c)
  cl-bad-conf bad (split c gss) =
    if bad c then Ø else (split c (cl-bad-conf* bad gss))
  cl-bad-conf bad (rebuild c gss) =
    if bad c then Ø else (rebuild c (cl-bad-conf* bad gss))

  -- cl-bad-conf*

  cl-bad-conf* : {C : Set} (bad : C → Bool)
    (gss : List (LazyGraph C)) → List (LazyGraph C)

  cl-bad-conf* bad [] = []
  cl-bad-conf* bad (gs ∷ gss) =
    (cl-bad-conf bad gs) ∷ cl-bad-conf* bad gss

--
-- `cl-bad-conf` is sound
--

module ClBadConfig-Sound where

  open Membership-≡

  -- cl-bad-conf*-is-map

  cl-bad-conf*-is-map :
    {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
    cl-bad-conf* bad gss ≡ map (cl-bad-conf bad) gss

  cl-bad-conf*-is-map bad [] =
    refl
  cl-bad-conf*-is-map bad (gs ∷ gss) =
    cong (_∷_ (cl-bad-conf bad gs)) (cl-bad-conf*-is-map bad gss)

  mutual

    cl-bad-conf-sound :
      {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
      ⟪ cl-bad-conf bad gs ⟫ ⊆ ⟪ gs ⟫

    cl-bad-conf-sound bad (⁇ a⊥) =
      ⊥-elim a⊥
    cl-bad-conf-sound bad Ø =
      id
    cl-bad-conf-sound bad (alt gs₁ gs₂) {g}
      with cl-bad-conf-sound bad gs₁ | cl-bad-conf-sound bad gs₂
    ... | cl-gs₁⊆gs₁ | cl-gs₂⊆gs₂ =
      g ∈ (⟪ cl-bad-conf bad gs₁ ⟫ ++ ⟪ cl-bad-conf bad gs₂ ⟫)
        ↔⟨ sym $ ++↔ ⟩
      (g ∈ ⟪ cl-bad-conf bad gs₁ ⟫ ⊎ g ∈ ⟪ cl-bad-conf bad gs₂ ⟫)
        ∼⟨ cl-bad-conf-sound bad gs₁ ⊎-cong cl-bad-conf-sound bad gs₂ ⟩
      (g ∈ ⟪ gs₁ ⟫ ⊎ g ∈ ⟪ gs₂ ⟫)
        ↔⟨ ++↔ ⟩
      g ∈ (⟪ gs₁ ⟫ ++ ⟪ gs₂ ⟫)
      ∎ where open ∼-Reasoning
    cl-bad-conf-sound bad (back c) with bad c
    ... | true = λ ()
    ... | false = id
    cl-bad-conf-sound bad (split c gss) {g} with bad c 
    ... | true = λ ()
    ... | false =
      g ∈ map (split c) (cartesian ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ map-∈↔ ⟩
      (∃ λ g′ → g′ ∈ cartesian ⟪ cl-bad-conf* bad gss ⟫* × (g ≡ split c g′))
        ∼⟨ Σ.cong Inv.id (cl-bad-conf-cartesian bad gss ×-cong id) ⟩
      (∃ λ g′ → g′ ∈ cartesian ⟪ gss ⟫* × (g ≡ split c g′))
        ↔⟨ map-∈↔ ⟩
      g ∈ map (split c) (cartesian ⟪ gss ⟫*)
      ∎ where open ∼-Reasoning
    cl-bad-conf-sound bad (rebuild c gss) {g} with bad c
    ... | true = λ ()
    ... | false =
      g ∈ map (rebuild c) (concat ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ map-∈↔ ⟩
      (∃ λ g′ → g′ ∈ concat ⟪ cl-bad-conf* bad gss ⟫* × (g ≡ rebuild c g′))
        ∼⟨ Σ.cong Inv.id (cl-bad-conf-concat bad gss ×-cong id) ⟩
      (∃ λ g′ → g′ ∈ concat ⟪ gss ⟫* × (g ≡ rebuild c g′))
        ↔⟨ map-∈↔ ⟩
      g ∈ map (rebuild c) (concat ⟪ gss ⟫*)
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-concat

    cl-bad-conf-concat :
      {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
      concat ⟪ cl-bad-conf* bad gss ⟫* ⊆ concat ⟪ gss ⟫*

    cl-bad-conf-concat bad [] =
      id
    cl-bad-conf-concat bad (gs ∷ gss) {g} =
      g ∈ (⟪ cl-bad-conf bad gs ⟫ ++ concat ⟪ cl-bad-conf* bad gss ⟫*)
        ↔⟨ sym $ ++↔ ⟩
      (g ∈ ⟪ cl-bad-conf bad gs ⟫ ⊎ g ∈ concat ⟪ cl-bad-conf* bad gss ⟫*)
        ∼⟨ cl-bad-conf-sound bad gs ⊎-cong cl-bad-conf-concat bad gss ⟩
      (g ∈ ⟪ gs ⟫ ⊎ g ∈ concat ⟪ gss ⟫*)
        ↔⟨ ++↔ ⟩
      g ∈ (⟪ gs ⟫ ++ concat ⟪ gss ⟫*)
      ∎ where open ∼-Reasoning

    -- cl-bad-conf-cartesian

    cl-bad-conf-cartesian :
      {C : Set} (bad : C → Bool) (gss : List (LazyGraph C)) →
      cartesian ⟪ cl-bad-conf* bad gss ⟫* ⊆ cartesian ⟪ gss ⟫*

    cl-bad-conf-cartesian {C} bad gss {gs} =
      cartesian-mono ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫* (helper tt)
      where
      open ∼-Reasoning

      ∈*∘map : ∀ gss →
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) gss) (map ⟪_⟫ gss)
      ∈*∘map [] = []
      ∈*∘map (gs ∷ gss) = cl-bad-conf-sound bad gs ∷ ∈*∘map gss

      helper : ⊤ → Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫*
      helper =
        ⊤
          ∼⟨ const (∈*∘map gss) ⟩
        Pointwise.Rel _⊆_ (map (⟪_⟫ ∘ cl-bad-conf bad) gss) (map ⟪_⟫ gss)
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ u (map ⟪_⟫ gss))
                   (map-compose gss) ⟩
        Pointwise.Rel _⊆_ (map ⟪_⟫ (map (cl-bad-conf bad) gss)) (map ⟪_⟫ gss)
          ∼⟨ subst₂ (λ u v → Pointwise.Rel _⊆_ u v)
                    (P.sym $ ⟪⟫*-is-map (map (cl-bad-conf bad) gss))
                    (P.sym $ ⟪⟫*-is-map gss) ⟩
        Pointwise.Rel _⊆_ ⟪ map (cl-bad-conf bad) gss ⟫* ⟪ gss ⟫*
          ∼⟨ subst (λ u → Pointwise.Rel _⊆_ ⟪ u ⟫* ⟪ gss ⟫*)
                   (P.sym $ cl-bad-conf*-is-map bad gss) ⟩
        Pointwise.Rel _⊆_ ⟪ cl-bad-conf* bad gss ⟫* ⟪ gss ⟫*
        ∎

--
-- The graph returned by `cl-bad-conf` may be cleaned by `cl-empty`.
--

-- cl-empty&bad

cl-empty&bad : {C : Set} (bad : C → Bool) (gs : LazyGraph C) →
  LazyGraph C

cl-empty&bad bad = cl-empty ∘ cl-bad-conf bad

--
-- Extracting a graph of minimal size (if any).
--

mutual

  -- graph-size

  graph-size  : ∀ {C : Set} (g : Graph C) → ℕ

  graph-size (back c) = 1
  graph-size (split c gs) = suc (graph-size* gs)
  graph-size (rebuild c g) = suc (graph-size g)

  -- graph-size*

  graph-size* : ∀ {C : Set} (g : List (Graph C)) → ℕ

  graph-size* [] = 0
  graph-size* (g ∷ gs) = graph-size g + graph-size* gs


-- Now we define a cleaner that produces a lazy graph
-- representing the smallest graph (or the empty set of graphs).

-- We use a trick: ∞ is represented by 0 in (0 , Ø).

-- select-min₂

select-min₂ : ∀ {C : Set} (kgs₁ kgs₂ : ℕ × LazyGraph C) →
  ℕ × LazyGraph C

select-min₂ (_ , Ø) (k₂ , gs₂) = k₂ , gs₂
select-min₂ (k₁ , gs₁) (_ , Ø) = k₁ , gs₁
select-min₂ (k₁ , gs₁) (k₂ , gs₂) with k₁ ≤? k₂
... | yes _ = k₁ , gs₁
... | no  _ = k₂ , gs₂

-- select-min

select-min : ∀ {C : Set} (kgss : List (ℕ × LazyGraph C)) →
  ℕ × LazyGraph C

select-min [] = 0 , Ø
select-min (kgs ∷ kgss) = foldl select-min₂ kgs kgss

mutual

  -- cl-min-size

  cl-min-size : ∀ {C : Set} (gs : LazyGraph C) → ℕ × LazyGraph C

  cl-min-size (⁇ a⊥) =
    ⊥-elim a⊥
  cl-min-size Ø =
    0 , Ø -- should be ∞ , Ø
  cl-min-size (alt gs₁ gs₂) =
    select-min₂ (cl-min-size gs₁) (cl-min-size gs₂)
  cl-min-size (back c) =
    1 , back c
  cl-min-size (split c gss) with cl-min-size-∧ gss
  ... | 0 , _ = 0 , Ø
  ... | k , gs = k , split c gs
  cl-min-size (rebuild c gss) with select-min (cl-min-size* gss)
  ... | _ , Ø = 0 , Ø
  ... | k , gs = suc k , rebuild c [ gs ]

  -- cl-min-size*

  cl-min-size* : ∀ {C : Set} (gss : List(LazyGraph C)) →
    List (ℕ × LazyGraph C)

  cl-min-size* [] = []
  cl-min-size* (gs ∷ gss) = cl-min-size gs ∷ cl-min-size* gss

  -- cl-min-size-∧

  cl-min-size-∧ : ∀ {C : Set} (gss : List (LazyGraph C)) →
    ℕ × List (LazyGraph C)

  cl-min-size-∧ [] = 1 , []
  cl-min-size-∧ (gs ∷ gss) with cl-min-size gs | cl-min-size-∧ gss
  ... | 0 , gs′ | _ , gss′ = 0 , gs′ ∷ gss′
  ... | _ , gs′ | 0 , gss′ = 0 , gs′ ∷ gss′
  ... | i , gs′ | j , gss′ = i + j , gs′ ∷ gss′

--
-- `cl-min-size` is sound:
--
--  Let cl-min-size gs ≡ (k , gs′). Then
--     ⟪ gs′ ⟫ ⊆ ⟪ gs ⟫
--     k ≡ graph-size (hd ⟪ gs′ ⟫)
--
-- TODO: prove this formally