{-# OPTIONS --without-K --prop #-}

module Setoid.Empty where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

Empty : ∀{i}{Γ : Con i} → Ty Γ lzero
∣ Empty ∣T γ = ⊥
Empty T _ ⊢ _ ~ _ = ⊤p
refT Empty = _
symT Empty = _
transT Empty = _
coeT Empty γ~ α = α
cohT Empty = _

exfalso : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ Empty → Tm Γ A
∣ exfalso t ∣t γ = ⊥elim (∣ t ∣t γ)
~t (exfalso t) {γ} _ = ⊥elimp (∣ t ∣t γ)
