module SllDef where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Data.Maybe

open import Relation.Nullary
open import Relation.Binary as Rel2
open import Relation.Binary.PropositionalEquality

data Exp (FN : Set) : Set where
  V : ℕ → Exp FN
  F : FN → List (Exp FN) → Exp FN
  G : FN → Exp FN → List (Exp FN) → Exp FN
  Nil : Exp FN
  Cons : Exp FN → Exp FN → Exp FN

data Exp' (FN : Set) : Set where
  V : ℕ → Exp' FN
  F : FN → List (Exp FN) → Exp' FN
  Nil : Exp' FN
  Cons : Exp FN → Exp FN → Exp' FN

injExp' : ∀ {FN} → Exp' FN → Exp FN
injExp' (V x) = V x
injExp' (F f es) = F f es
injExp' Nil = Nil
injExp' (Cons e1 e2) = Cons e1 e2

Context : Set → Set
Context FN = List (FN × List (Exp FN))

exposeRedex : ∀ {FN} → Exp FN → Context FN × Exp' FN
exposeRedex e = helper [] e
  where
    helper : ∀ {FN} → Context FN → Exp FN → Context FN × Exp' FN
    helper ctx (V n) = ctx , (V n)
    helper ctx (F f es) = ctx , (F f es)
    helper ctx (G f e es) = helper ((f , es) ∷ ctx) e 
    helper ctx Nil = ctx , Nil
    helper ctx (Cons e1 e2) = ctx , Cons e1 e2

fillContext : ∀ {FN} → Context FN → Exp FN → Exp FN
fillContext ctx e = foldl (λ e p → G (proj₁ p) e (proj₂ p)) e ctx

{-
fillContext-exposeRedex : ∀ {FN} (e : Exp FN) → 
                          let p = exposeRedex e 
                          in fillContext (proj₁ p) (injExp' (proj₂ p)) ≡ e
fillContext-exposeRedex (V n) = refl
fillContext-exposeRedex (F f es) = refl
fillContext-exposeRedex (G f e es) = {!!}
  where
    helper = fillContext-exposeRedex e
fillContext-exposeRedex Nil = refl
fillContext-exposeRedex (Cons e1 e2) = refl
-}

record Prog (FN : Set) : Set where
  field
    fdefs : List (FN × Exp FN)
    gdefs : List (FN × (Exp FN × Exp FN))

EqDec = λ (X : Set) → (x y : X) → Dec (x ≡ y)

lookup : ∀ {A B : Set} (Aeq : EqDec A) → A → List (A × B) -> Maybe B
lookup {A} {B} Aeq a ps with gfilter f ps
  where 
    f : A × B → Maybe B
    f (a' , b) with Aeq a a'
    f (a' , b) | yes p = just b
    f (a' , b) | no ¬p = nothing
lookup Aeq a ps | [] = nothing
lookup Aeq a ps | b ∷ bs = just b

bvSubst : ∀ {FN} → List (Exp FN) → Exp FN → Exp FN
bvSubst es e = {!!}

redStep : ∀ {FN} (FNeq : EqDec FN) → Prog FN → Context FN × Exp' FN 
          → Maybe (Context FN × Exp' FN)
redStep FNeq prg (ctx , V n) = nothing
redStep FNeq prg (ctx , F f es) with lookup FNeq f (Prog.fdefs prg)
... | just def = just (proj₁ p ++ ctx , proj₂ p)
  where p = exposeRedex (bvSubst es def)
... | nothing = nothing
redStep FNeq prg ([] , Nil) = nothing
redStep FNeq prg ((g , es) ∷ ctx , Nil) with lookup FNeq g (Prog.gdefs prg)
... | just (eNil , eCons) = just (proj₁ p ++ ctx , proj₂ p)
  where p = exposeRedex (bvSubst es eNil)
... | nothing = nothing
redStep FNeq prg ([] , Cons e1 e2) = nothing {- ?? -}
redStep FNeq prg ((g , es) ∷ ctx , Cons e1 e2) with lookup FNeq g (Prog.gdefs prg)
... | just (eNil , eCons) = just ((proj₁ p ++ ctx) , (proj₂ p))
  where p = exposeRedex (bvSubst es eCons)
... | nothing = nothing
