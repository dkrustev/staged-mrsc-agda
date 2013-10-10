module VecWf where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary
  using (Rel) renaming (Decidable to Decidable₂)
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded

{- An alternative definition of `Vec`, more convenient for proving well-foundedness -}
RecVec : ∀ (A : Set) (n : ℕ) → Set
RecVec A zero = ⊤
RecVec A (suc n) = Σ A (λ _ → RecVec A n)

{- Lift a well-founded relation on elements to a well-founded relation on vectors -}
RecVec< : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) → RecVec A n → RecVec A n → Set
RecVec< {A} {zero} _<_ v₁ v₂ = ⊥
RecVec< {A} {suc n} _<_ v₁ v₂ = Lexicographic._<_ _<_ (λ _ → RecVec< _<_) v₁ v₂

RecVec<-dec : ∀ {A} → Decidable₂ (_≡_ {A = A}) → ∀ (_<_ : A → A → Set) → Decidable₂ _<_
  → ∀ {n} → Decidable₂ (RecVec< {A} {n} _<_)
RecVec<-dec _A≟_ _<_ _<dec_ {zero} tt tt = no (λ x → x)
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (h₂ , t₂) with h₁ <dec h₂
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (h₂ , t₂) | yes h₁<h₂ = 
  yes (Lexicographic.left h₁<h₂)
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (h₂ , t₂) | no ¬h₁<h₂ with h₁ A≟ h₂
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (.h₁ , t₂) | no ¬h₁<h₂ | yes refl
  with RecVec<-dec _A≟_ _<_ _<dec_ t₁ t₂
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (.h₁ , t₂) | no ¬h₁<h₂ | yes refl | yes t₁<t₂ =
  yes (Lexicographic.right t₁<t₂)
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (.h₁ , t₂) | no ¬h₁<h₂ | yes refl | no ¬t₁<t₂ =
  no helper
  where
    helper : Lexicographic._<_ _<_ (λ _ → RecVec< _<_) (h₁ , t₁) (h₁ , t₂) → ⊥
    helper (Lexicographic.left x₁<x₂) = ¬h₁<h₂ x₁<x₂
    helper (Lexicographic.right y₁<y₂) = ¬t₁<t₂ y₁<y₂
RecVec<-dec _A≟_ _<_ _<dec_ {suc n} (h₁ , t₁) (h₂ , t₂) | no ¬h₁<h₂ | no ¬h₁≡h₂ = 
  no (helper h₁ t₁ h₂ t₂ ¬h₁<h₂ ¬h₁≡h₂)
  where
    helper2 : ∀ h₁ t₁ h₂ t₂ → ¬ h₁ < h₂ →  
      Lexicographic._<_ _<_ (λ _ → RecVec< _<_) (h₁ , t₁) (h₂ , t₂) → h₁ ≡ h₂
    helper2 h₃ t₃ h₄ t₄ ¬h₁<h₂ (Lexicographic.left x₁<x₂) = ⊥-elim (¬h₁<h₂ x₁<x₂)
    helper2 .h₃ t₃ h₃ t₄ ¬h₁<h₂ (Lexicographic.right y₁<y₂) = refl
    helper : ∀ h₁ t₁ h₂ t₂ → ¬ h₁ < h₂ → ¬ h₁ ≡ h₂ → 
      Lexicographic._<_ _<_ (λ _ → RecVec< _<_) (h₁ , t₁) (h₂ , t₂) → ⊥ 
    helper h₁ t₁ h₂ t₂ ¬h₁<h₂ ¬h₁≡h₂ p = ¬h₁≡h₂ (helper2 h₁ t₁ h₂ t₂ ¬h₁<h₂ p)

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

Vec<-dec : ∀ {A} → Decidable₂ (_≡_ {A = A}) → ∀ (_<_ : A → A → Set) → Decidable₂ _<_
  → ∀ {n} → Decidable₂ (Vec< {A} {n} _<_)
Vec<-dec _A≟_ _<_ _<dec_ v₁ v₂ = 
  RecVec<-dec _A≟_ _<_ _<dec_ (Vec⇒RecVec v₁) (Vec⇒RecVec v₂)

Vec<-wf : ∀ {A : Set} {n : ℕ} (_<_ : A → A → Set) →
  Well-founded _<_ → Well-founded (Vec< {A} {n} _<_)
Vec<-wf {A} {n} _<_ wf< v = Inverse-image.well-founded Vec⇒RecVec (RecVec<-wf _<_ wf<) v
