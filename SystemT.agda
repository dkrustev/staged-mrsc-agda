{- Author: Dimitur Krustev -}
{- loosely based on: 
     http://perso.ens-lyon.fr/guillaume.allais/?en/main/blog/read/glueing-terms-model -}

module SystemT where

open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Memb {A : Set} (x : A) : List A → Set where
  MembZ : ∀ xs → Memb x (x ∷ xs)
  MembS : ∀ {xs} y → Memb x xs → Memb x (y ∷ xs)

Incl : {A : Set} (xs ys : List A) → Set
Incl xs ys = ∀ x → Memb x xs → Memb x ys

InclStep : ∀ {A : Set} {xs ys} (x : A) → Incl xs ys → Incl xs (x ∷ ys)
InclStep {A} {xs} {ys} x inc = λ y m → MembS x (inc y m)

InclPop : ∀ {A : Set} {xs ys} {x : A} → Incl xs ys → Incl (x ∷ xs) (x ∷ ys)
InclPop {A} {xs} {ys} {x} inc .x (MembZ .xs) = MembZ ys
InclPop {A} {xs} {ys} {x} inc y (MembS .x memb) = MembS x (inc y memb)

InclRefl : ∀ {A : Set} (xs : List A) → Incl xs xs
InclRefl xs = λ x m → m

InclTrans : {A : Set} {xs ys zs : List A} → Incl xs ys → Incl ys zs → Incl xs zs
InclTrans {A} {xs} {ys} {zs} inc1 inc2 = λ x m → inc2 x (inc1 x m)

weakenMemb : ∀ {A : Set} {xs ys : List A} {x : A} → Incl xs ys → Memb x xs → Memb x ys
weakenMemb {A} {xs} {ys} {x} inc memb = inc x memb

{- ***** -}

data Ty : Set where
  TNat : Ty
  TArr : Ty → Ty → Ty

data Exp (G : List Ty) : Ty → Set where
  EV : ∀ {t} → Memb t G → Exp G t
  EApp : ∀ {t1 t2} → Exp G (TArr t1 t2) → Exp G t1 → Exp G t2
  ELam : ∀ {t1 t2} → Exp (t1 ∷ G) t2 → Exp G (TArr t1 t2)
  EZero : Exp G TNat
  ESucc : Exp G TNat → Exp G TNat
  ENatRec : ∀ {t} → Exp G t → Exp G (TArr TNat (TArr t t)) → Exp G TNat → Exp G t

mutual
  data Nf (G : List Ty) : Ty → Set where
    NfNe : Ne G TNat → Nf G TNat
    NfLam : ∀ {t1 t2} → Nf (t1 ∷ G) t2 → Nf G (TArr t1 t2)
    NfZero : Nf G TNat
    NfSucc : Nf G TNat → Nf G TNat
  
  data Ne (G : List Ty) : Ty → Set where
    NeV : ∀ {t} → Memb t G → Ne G t
    NeApp : ∀ {t1 t2} → Ne G (TArr t1 t2) → Nf G t1 → Ne G t2
    NeNatRec : ∀ {t} → Nf G t → Nf G (TArr TNat (TArr t t)) → Ne G TNat → Ne G t

mutual 
  weakenNf : ∀ {G D t} → Incl G D → Nf G t → Nf D t
  weakenNf inc (NfNe ne) = NfNe (weakenNe inc ne)
  weakenNf inc (NfLam nf) = NfLam (weakenNf (InclPop inc) nf)
  weakenNf inc NfZero = NfZero
  weakenNf inc (NfSucc nf) = NfSucc (weakenNf inc nf)

  weakenNe : ∀ {G D t} → Incl G D → Ne G t → Ne D t
  weakenNe inc (NeV x) = NeV (weakenMemb inc x)
  weakenNe inc (NeApp ne nf) = NeApp (weakenNe inc ne) (weakenNf inc nf)
  weakenNe inc (NeNatRec nfz nfs ne) = 
    NeNatRec (weakenNf inc nfz) (weakenNf inc nfs) (weakenNe inc ne)

eta : ∀ {G} {t} → Ne G t → Nf G t
eta {G} {TNat} ne = NfNe ne
eta {G} {TArr t1 t2} ne = NfLam (eta (NeApp (weakenNe inc ne) var))
  where
    inc : (x : Ty) → Memb x G → Memb x (t1 ∷ G)
    inc x memb = InclStep t1 (λ x₁ z → z) x (InclRefl G x memb)
    var : Nf (t1 ∷ G) t1
    var = eta (NeV (MembZ G))

{- ***** -}

mutual
  Model : (G : List Ty) (t : Ty) → Set
  Model G t = Ne G t ⊎ Nf G t × ActingModel G t

  ActingModel : (G : List Ty) (t : Ty) → Set
  ActingModel G TNat = ⊤
  ActingModel G (TArr t1 t2) = ∀ D → Incl G D → Model D t1 → Model D t2

weakenActVal : ∀ {G t} D → Incl G D → ActingModel G t → ActingModel D t
weakenActVal {G} {TNat} D inc v = v
weakenActVal {G} {TArr t1 t2} D inc v = λ E inc1 v1 → v E (InclTrans inc inc1) v1

weakenVal : ∀ {G D t} → Incl G D → Model G t → Model D t
weakenVal inc (inj₁ ne) = inj₁ (weakenNe inc ne)
weakenVal inc (inj₂ (nf , v)) = inj₂ (weakenNf inc nf , weakenActVal _ inc v)

reify : ∀ {G t} → Model G t → Nf G t
reify (inj₁ ne) = eta ne
reify (inj₂ (nf , v)) = nf

reflect : ∀ {G t} → Ne G t → Model G t
reflect ne = inj₁ ne

{- ***** -}

Env : List Ty → List Ty → Set
Env D [] = ⊤
Env D (t ∷ G) = Env D G × Model D t

weakenEnv : ∀ G {D E} → Incl D E → Env D G → Env E G
weakenEnv [] {D} {E} inc env = tt
weakenEnv (t ∷ G) {D} {E} inc env = (weakenEnv G inc (proj₁ env)) , weakenVal inc (proj₂ env)

diagEnv : ∀ G → Env G G
diagEnv [] = tt
diagEnv (t ∷ G) = 
  (weakenEnv G (InclStep _ (InclRefl _)) (diagEnv G)) , reflect (NeV (MembZ _))

lookup : ∀ {G t} → Memb t G → ∀ {D} → Env D G → Model D t
lookup (MembZ _) = λ env → proj₂ env
lookup (MembS _ m) = λ env → lookup m (proj₁ env)

app : ∀ {G t1 t2} → Model G (TArr t1 t2) → Model G t1 → Model G t2
app (inj₁ ne) x = inj₁ (NeApp ne (reify x))
app (inj₂ (nf , f)) x = f _ (InclRefl _) x

natrec : ∀ {G t} → Model G t → Model G (TArr TNat (TArr t t)) → Model G TNat → Model G t
natrec z s (inj₁ ne) = inj₁ (NeNatRec (reify z) (reify s) ne)
natrec z s (inj₂ (nf , _)) = helper z s nf
  where
    helper : ∀ {G t} → Model G t → Model G (TArr TNat (TArr t t)) → Nf G TNat → Model G t
    helper z s (NfNe ne) = inj₁ (NeNatRec (reify z) (reify s) ne)
    helper z s NfZero = z
    helper z s (NfSucc n) = app (app s n') (helper z s n)
      where
        n' : Model _ TNat
        n' = inj₂ (n , tt)

eval : ∀ {G t} → Exp G t → ∀ {D} → Env D G → Model D t
eval (EV x) = λ env → lookup x env
eval (EApp e1 e2) = λ env → app (eval e1 env) (eval e2 env)
eval (ELam e) = λ env → inj₂ ((NfLam (Bquoted env)) , (B env))
  where
    B = λ env E (inc : Incl _ E) x → eval e (weakenEnv _ inc env , x)
    Bquoted = λ env → reify (B env _ (InclStep _ (InclRefl _)) (reflect (NeV (MembZ _))))
eval EZero = λ env → inj₂ (NfZero , tt)
eval (ESucc e) = λ env → inj₂ ((NfSucc (reify (eval e env))) , tt)
eval (ENatRec ez es en) = λ env → natrec (eval ez env) (eval es env) (eval en env)

norm : ∀ {G t} → Exp G t → Nf G t
norm e = reify (eval e (diagEnv _))

{- ***** -}

st-add = λ G n m → ENatRec m (ELam {G} (ELam (ESucc (EV (MembZ _))))) n

st-1 = λ G → ESucc (EZero {G})

st-1-plus-1 = norm (st-add _ (st-1 _) (st-1 []))

st-1-plus-1-ok : st-1-plus-1 ≡ NfSucc (NfSucc NfZero)
st-1-plus-1-ok = refl
