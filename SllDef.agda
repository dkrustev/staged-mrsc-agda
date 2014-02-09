module SllDef where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product hiding (map)
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

mutual 
  mapV : ∀ {FN} → (ℕ → Exp FN) → Exp FN → Exp FN
  mapV fv (V n) = fv n
  mapV fv (F f es) = F f (mapsV fv es)
  mapV fv (G g e es) = G g (mapV fv e) (mapsV fv es)
  mapV fv Nil = Nil
  mapV fv (Cons e1 e2) = Cons (mapV fv e1) (mapV fv e2)

  {- the following inlined List.map serves just to satisfy the termination checker -}
  mapsV : ∀ {FN} → (ℕ → Exp FN) → List (Exp FN) → List (Exp FN)
  mapsV fv [] = []
  mapsV fv (e ∷ es) = mapV fv e ∷ mapsV fv es

bvSubst : ∀ {FN} → List (Exp FN) → Exp FN → Exp FN
bvSubst es e = mapV (λ n → nthWithDefault Nil n es) e
  where
    nthWithDefault : ∀ {A : Set} → A → ℕ → List A → A
    nthWithDefault def n [] = def
    nthWithDefault def zero (x ∷ xs) = x
    nthWithDefault def (suc n) (x ∷ xs) = nthWithDefault def n xs
    
{- redex calculation -}

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

{- mixed-step reduction -}

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

data Val : Set where
  VNil : Val
  VCons : Val → Val → Val

projVal : ∀ {FN} → Exp FN → Maybe Val
projVal (V n) = nothing
projVal (F f es) = nothing
projVal (G g e es) = nothing
projVal Nil = just VNil
projVal (Cons e1 e2) with projVal e1 
projVal (Cons e1 e2) | just v1 with projVal e2 
projVal (Cons e1 e2) | just v1 | just v2 = just (VCons v1 v2)
projVal (Cons e1 e2) | just v1 | nothing = nothing
projVal (Cons e1 e2) | _ = nothing

data RedExp {FN} (FNeq : EqDec FN) (prg : Prog FN) :
            (Context FN × Exp' FN) → (Context FN × Exp' FN) → Set where
  RedStep : ∀ ce1 ce2 ce3 → redStep FNeq prg ce1 ≡ just ce2 → 
            RedExp FNeq prg ce2 ce3 → RedExp FNeq prg ce1 ce3
  RedCons : ∀ e11 e12 c21 e21 c22 e22 
            → RedExp FNeq prg (exposeRedex e11) (c21 , e21)
            → RedExp FNeq prg (exposeRedex e12) (c22 , e22) 
            → RedExp FNeq prg ([] , Cons e11 e12) 
                ([] , Cons (fillContext c21 (injExp' e21)) (fillContext c22 (injExp' e22)))

EvalExp : ∀ {FN} (FNeq : EqDec FN) (prg : Prog FN) → Exp FN → Val → Set
EvalExp FNeq prg e v = ∃ (λ ce → 
  RedExp FNeq prg (exposeRedex e) ce ×
    projVal (fillContext (proj₁ ce) (injExp' (proj₂ ce))) ≡ just v)

redExp : ∀ {FN} (FNeq : EqDec FN) (prg : Prog FN) → ℕ →
         (Context FN × Exp' FN) → Maybe (Context FN × Exp' FN)
redExp FNeq prg zero _ = nothing
redExp FNeq prg (suc n) ce with redStep FNeq prg ce
redExp FNeq prg (suc n) ce | just ce1 = redExp FNeq prg n ce1
redExp FNeq prg (suc n) ce | nothing = helper FNeq prg n ce
  where 
    helper : ∀ {FN} (FNeq : EqDec FN) (prg : Prog FN) → ℕ → 
             (Context FN × Exp' FN) → Maybe (Context FN × Exp' FN)
    helper FNeq prg n ([] , Cons e1 e2) with redExp FNeq prg n (exposeRedex e1)
    helper FNeq prg n ([] , Cons e1 e2) | just (c1 , e1') with 
                                          redExp FNeq prg n (exposeRedex e2)
    helper FNeq prg n ([] , Cons e1 e2) | just (c1 , e1') | just (c2 , e2') = 
      just ([] , Cons (fillContext c1 (injExp' e1')) (fillContext c2 (injExp' e2')))
    helper FNeq prg n ([] , Cons e1 e2) | just (c1 , e1') | nothing = nothing
    helper FNeq prg n ([] , Cons e1 e2) | nothing = nothing
    helper FNeq prg n ce = just ce

redExp-monotone : ∀ {FN} (FNeq : EqDec FN) (prg : Prog FN) (n : ℕ)
   (ce1 ce2 : Context FN × Exp' FN) → redExp FNeq prg n ce1 ≡ just ce2
   → ∀ (m : ℕ) → n ≤ m → redExp FNeq prg n ce1 ≡ just ce2
redExp-monotone FNeq prg zero ce1 ce2 () m n≤m
redExp-monotone FNeq prg (suc n) ce1 ce2 Heq zero ()
redExp-monotone FNeq prg (suc n) ce1 ce2 Heq (suc m) (s≤s n≤m) with redStep FNeq prg ce1
redExp-monotone FNeq prg (suc n) ce1 ce2 Heq (suc m) (s≤s n≤m) | just p = Heq
redExp-monotone FNeq prg (suc n) ([] , V x) ce2 Heq (suc m) (s≤s n≤m) | nothing = Heq
redExp-monotone FNeq prg (suc n) ([] , F x x₁) ce2 Heq (suc m) (s≤s n≤m) | nothing = Heq
redExp-monotone FNeq prg (suc n) ([] , Nil) ce2 Heq (suc m) (s≤s n≤m) | nothing = Heq
redExp-monotone FNeq prg (suc n) ([] , Cons x x₁) ce2 Heq (suc m) (s≤s n≤m) | nothing = Heq
redExp-monotone FNeq prg (suc n) ce1 ce2 Heq (suc m) (s≤s n≤m) | nothing = Heq

RedExp→redExp : ∀ {FN} (FNeq : EqDec FN) (prg : Prog FN) (ce1 ce2 : Context FN × Exp' FN) 
                → RedExp FNeq prg ce1 ce2 → ∃ (λ n → redExp FNeq prg n ce1 ≡ just ce2)
RedExp→redExp FNeq prg ce1 ce2 (RedStep .ce1 ce3 .ce2 Heq HRE) rewrite Heq = 
  suc n , helper2 Heq
  where
    helper = RedExp→redExp _ _ _ _ HRE
    n = proj₁ helper
    Heq1 = proj₂ helper
    helper2 : redStep FNeq prg ce1 ≡ just ce3 → redExp FNeq prg (suc n) ce1 ≡ just ce2
    helper2 Heq rewrite Heq = Heq1
RedExp→redExp FNeq prg .([] , Cons e11 e12) 
  .([] , Cons (fillContext c21 (injExp' e21)) (fillContext c22 (injExp' e22))) 
  (RedCons e11 e12 c21 e21 c22 e22 HRE1 HRE2) = suc n , {!!}
  where
    IH1 = RedExp→redExp _ _ _ _ HRE1
    IH2 = RedExp→redExp _ _ _ _ HRE2
    n = (proj₁ IH1) ⊔ (proj₁ IH2)
    


