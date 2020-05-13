{-# OPTIONS --without-K --prop #-}

module Setoid.Unit where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

Unit : ∀{i}{Γ : Con i} → Ty Γ lzero
∣ Unit ∣T γ = ⊤
Unit T γ~ ⊢ _ ~ _ = ⊤p
refT Unit = _
symT Unit = _
transT Unit = _
coeT Unit = _
cohT Unit = _

* : ∀{i}{Γ : Con i} → Tm Γ Unit
* = _
