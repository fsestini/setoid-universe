{-# OPTIONS --without-K --prop #-}

module Setoid.SeTT where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF
open import Setoid.Props

-- contexts

_~C : ∀{i}(Γ : Con i){j}{Ω : Con j}(σ₀ σ₁ : Tms Ω Γ) → Prop (i ⊔ j)
_~C = SetoidMor~

RC : ∀{i}(Γ : Con i){j}{Ω : Con j}(σ : Tms Ω Γ) → (Γ ~C) σ σ
∣ RC Γ σ ∣ γ = refC Γ (∣ σ ∣s γ)


SC : ∀{i}(Γ : Con i){j}{Ω : Con j}{σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁) → (Γ ~C) σ₁ σ₀
∣ SC Γ σ₀₁ ∣ γ = symC Γ (∣ σ₀₁ ∣ γ)

TC : ∀{i}(Γ : Con i){j}{Ω : Con j}{σ₀ σ₁ σ₂ : Tms Ω Γ} → (Γ ~C) σ₀ σ₁ → (Γ ~C) σ₁ σ₂ → (Γ ~C) σ₀ σ₂
∣ TC Γ σ₀₁ σ₁₂ ∣ γ = transC Γ (∣ σ₀₁ ∣ γ) (∣ σ₁₂ ∣ γ)

_[_]C : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{Θ : Con k}{σ₀ σ₁ : Tms Γ Δ} → (Δ ~C) σ₀ σ₁ → (δ : Tms Θ Γ) → (Δ ~C) (σ₀ ∘ δ) (σ₁ ∘ δ)
∣ σ₀₁ [ δ ]C ∣ γ = ∣ σ₀₁ ∣ (∣ δ ∣s γ)
infixl 7 _[_]C

-- substitutions

_~s' : ∀{i}{Γ : Con i}{j}{Δ : Con j}(δ : Tms Γ Δ){k}{Ω : Con k}{σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁) →
  (Δ ~C) (δ ∘ σ₀) (δ ∘ σ₁)
∣ (σ ~s') σ₀₁ ∣ γ = ~s σ (∣ σ₀₁ ∣ γ)

-- types

_~T : ∀{i}{Γ : Con i}{k}(A : Ty Γ k){j}{Ω : Con j}{σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁) → Tm Ω (A [ σ₀ ]T) → Tm Ω (A [ σ₁ ]T) → Tm Ω (P k)
∣ (A ~T) σ₀₁ t₀ t₁ ∣t γ = A T ∣ σ₀₁ ∣ γ ⊢ ∣ t₀ ∣t γ ~ ∣ t₁ ∣t γ
~t ((A ~T) σ₀₁ t₀ t₁) γ~ = mk↑pl
  ((λ t₀₁ → transT3 A (symT A (~t t₀ γ~)) (un↑ps t₀₁) (~t t₁ γ~)) ,p
  (λ t₀₁ → transT3 A (~t t₀ γ~) (un↑ps t₀₁) (symT A (~t t₁ γ~))))

RT : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}(A : Ty Γ k){σ : Tms Ω Γ}(t : Tm Ω (A [ σ ]T)) → Tm Ω (ElP ((A ~T) {σ₀ = σ}{σ} (RC Γ σ) t t))
∣ RT A t ∣t γ = mk↑ps (refT A (∣ t ∣t γ))
~t (RT A t) _ = mk↑pl ttp

ST : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}(A : Ty Γ k){σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
     {t₀ : Tm Ω (A [ σ₀ ]T)}{t₁ : Tm Ω (A [ σ₁ ]T)}
     (t₀₁ : Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₁} σ₀₁ t₀ t₁))) →
     Tm Ω (ElP ((A ~T) {σ₀ = σ₁}{σ₀} (SC Γ {σ₀ = σ₀}{σ₁} σ₀₁) t₁ t₀))
∣ ST A t₀₁ ∣t γ = mk↑ps (symT A (un↑ps (∣ t₀₁ ∣t γ)))
~t (ST A t₀₁) _ = mk↑pl ttp

TT : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}(A : Ty Γ k){σ₀ σ₁ σ₂ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{σ₁₂ : (Γ ~C) σ₁ σ₂}
     {t₀ : Tm Ω (A [ σ₀ ]T)}{t₁ : Tm Ω (A [ σ₁ ]T)}{t₂ : Tm Ω (A [ σ₂ ]T)}
     (t₀₁ : Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₁} σ₀₁ t₀ t₁)))(t₁₂ : Tm Ω (ElP ((A ~T) {σ₀ = σ₁}{σ₂} σ₁₂ t₁ t₂))) →
     Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₂} (TC Γ {σ₀ = σ₀}{σ₁}{σ₂} σ₀₁ σ₁₂) t₀ t₂))
∣ TT A t₀₁ t₁₂ ∣t γ = mk↑ps (transT A (un↑ps (∣ t₀₁ ∣t γ)) (un↑ps (∣ t₁₂ ∣t γ)))
~t (TT A t₀₁ t₁₂) _ = mk↑pl ttp

coeT' : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}(A : Ty Γ k){σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁)
  (t₀ : Tm Ω (A [ σ₀ ]T)) → Tm Ω (A [ σ₁ ]T)
∣ coeT' A σ₀₁ t₀ ∣t γ = coeT A (∣ σ₀₁ ∣ γ) (∣ t₀ ∣t γ)
~t (coeT' A σ₀₁ t₀) {γ}{γ'} γ~ = transT3 A (symT A (cohT A (∣ σ₀₁ ∣ γ) (∣ t₀ ∣t γ))) (~t t₀ γ~) (cohT A (∣ σ₀₁ ∣ γ') (∣ t₀ ∣t γ'))

cohT' : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}(A : Ty Γ k){σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁)
  (t₀ : Tm Ω (A [ σ₀ ]T)) →
  Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ (coeT' A {σ₀}{σ₁} σ₀₁ t₀)))
∣ cohT' A σ₀₁ t₀ ∣t γ = mk↑ps (cohT A (∣ σ₀₁ ∣ γ) (∣ t₀ ∣t γ))
~t (cohT' A σ₀₁ t₀) _ = mk↑pl ttp

-- terms

_~t' : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}(t : Tm Γ A){k}{Ω : Con k}{σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁) →
  Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₁} σ₀₁ (t [ σ₀ ]t) (t [ σ₁ ]t)))
∣ (t ~t') σ₀₁ ∣t γ = mk↑ps (~t t (∣ σ₀₁ ∣ γ))
~t ((t ~t') σ₀₁) _ = mk↑pl ttp

-- empty context

ε~ : ∀{i}{Ω : Con i} → (• ~C) (ε {Γ = Ω}) ε
∣ ε~ ∣ _ = ttp

-- comprehension

_,'_ : ∀{i}{Γ : Con i}{k}{A : Ty Γ k}{j}{Ω : Con j}{σ₀ σ₁ : Tms Ω Γ}(σ₀₁ : (Γ ~C) σ₀ σ₁)
  {t₀ : Tm Ω (A [ σ₀ ]T)}{t₁ : Tm Ω (A [ σ₁ ]T)}(t₀₁ : Tm Ω (ElP ((A ~T) {σ₀ = σ₀}{σ₁} σ₀₁ t₀ t₁))) →
  ((Γ ▷ A) ~C) (_,_ σ₀ {A = A} t₀) (_,_ σ₁ {A = A} t₁)
∣ σ₀₁ ,' t₀₁ ∣ γ = ∣ σ₀₁ ∣ γ ,p un↑ps (∣ t₀₁ ∣t γ)
infixl 5 _,'_
 
π₁' : ∀{i}{Γ : Con i}{k}{A : Ty Γ k}{j}{Ω : Con j}{σ₀ σ₁ : Tms Ω (Γ ▷ A)}(σ₀₁ : ((Γ ▷ A) ~C) σ₀ σ₁) → 
  (Γ ~C) (π₁ {A = A} σ₀) (π₁ {A = A} σ₁)
∣ π₁' σ₀₁ ∣ γ = proj₁p (∣ σ₀₁ ∣ γ)

π₂' : ∀{i}{Γ : Con i}{k}{A : Ty Γ k}{j}{Ω : Con j}{σ₀ σ₁ : Tms Ω (Γ ▷ A)}(σ₀₁ : ((Γ ▷ A) ~C) σ₀ σ₁) →
  Tm Ω (ElP ((A ~T) {σ₀ = π₁ {A = A} σ₀}{π₁ {A = A} σ₁} (π₁' {A = A}{σ₀ = σ₀}{σ₁} σ₀₁) (π₂ {A = A} σ₀) (π₂ {A = A} σ₁)))
∣ π₂' σ₀₁ ∣t γ = mk↑ps (proj₂p (∣ σ₀₁ ∣ γ))
~t (π₂' σ₀₁) _ = mk↑pl ttp

open import Setoid.SetsII

U~BoolBool : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁} →
  Tm Ω (ElP ((U ~T) σ₀₁ BoolS BoolS))
un↑ps (∣ U~BoolBool {Γ = Γ}{σ₀₁ = σ₀₁} ∣t γ) =  ~t (BoolS {Γ = Γ}) (∣ σ₀₁ ∣ γ) 
~t U~BoolBool _ = mk↑pl ttp
