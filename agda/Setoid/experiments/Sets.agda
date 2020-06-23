{-# OPTIONS --prop --rewriting #-}
module Setoid.experiments.Sets where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ x
infix 4 _≡_
{-# BUILTIN REWRITE _≡_ #-}
postulate
  transp  : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
  transpβ : ∀{i j}{A : Set i}(P : A → Set j){x : A}{u : P x} → transp P refl u ≡ u
{-# REWRITE transpβ #-}

U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
∣ U ∣T γ = Set
U T _ ⊢ T₀ ~ T₁ = T₀ ≡ T₁
refT U _ = refl
symT U refl = refl
transT U refl refl = refl
coeT U _ A = A
cohT U _ _ = refl

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
∣ El a ∣T γ = ∣ a ∣t γ
El a T γ~ ⊢ α₀ ~ α₁ = transp (λ x → x) (~t a γ~) α₀ ≡ α₁
refT (El a) α = refl
symT (El a) refl = {!!}
transT (El a) refl refl = {!!}
coeT (El a) γ~ = transp (λ A → A) (~t a γ~)
cohT (El a) _ _ = refl

σ : ∀{i}{Γ : Con i}(a : Tm Γ U)(b : Tm (Γ ▷ El a) U) → Tm Γ U
∣ σ a b ∣t γ = Σ (∣ a ∣t γ) λ α → ∣ b ∣t (γ ,Σ α)
~t (σ a b) γ~ = {!~t b (γ~ ,p ?)!}

π : ∀{i}{Γ : Con i}(A : Ty Γ lzero)(b : Tm (Γ ▷ A) U) → Tm Γ U
∣ π {Γ = Γ} A b ∣t γ = Σsp ((x : ∣ A ∣T γ) → ∣ b ∣t (γ ,Σ x)) λ f → (x x' : ∣ A ∣T γ)(x~ : A T refC Γ γ ⊢ x ~ x') → El b T (refC Γ γ ,p x~) ⊢ f x ~ f x'
~t (π A b) γ~ = {!!} -- we can't prove this because we don't have ∣ A ∣T γ ≡ ∣ A ∣T γ'. it would work if A was also in U

-- this universe is simply an inclusion from the metatheory to SeTT
