module VecWf where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec
--open import Relation.Binary.Core
open import Induction.WellFounded

{- An alternative definition of `Vec`, more convenient for proving well-foundedness -}
RecVec : ∀ (A : Set) (n : ℕ) → Set
RecVec A zero = ⊤
RecVec A (suc n) = Σ A (λ _ → RecVec A n)

RecVec< : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) → RecVec A n → RecVec A n → Set
RecVec< {A} {zero} _<_ v₁ v₂ = ⊥
RecVec< {A} {suc n} _<_ v₁ v₂ = Lexicographic._<_ _<_ (λ _ → RecVec< _<_) v₁ v₂

RecVec<-wf : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) →
  Well-founded _<_ → Well-founded (RecVec< {A} {n} _<_)
RecVec<-wf {A} {zero} _<_ wf< tt = acc (λ top bot → ⊥-elim bot)
RecVec<-wf {A} {suc n} _<_ wf< (x , v) = 
  Lexicographic.well-founded _<_ (λ _ → RecVec< _<_) wf< (RecVec<-wf _<_ wf<) (x , v)

Vec⇒RecVec : ∀ {A n} → Vec A n → RecVec A n
Vec⇒RecVec [] = tt
Vec⇒RecVec (x ∷ v) = x , (Vec⇒RecVec v)

Vec< : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) → Vec A n → Vec A n → Set
Vec< _<_ v₁ v₂ = RecVec< _<_ (Vec⇒RecVec v₁) (Vec⇒RecVec v₂)

Vec<-wf : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) →
  Well-founded _<_ → Well-founded (Vec< {A} {n} _<_)
Vec<-wf {A} {n} _<_ wf< v = Inverse-image.well-founded Vec⇒RecVec (RecVec<-wf _<_ wf<) v
