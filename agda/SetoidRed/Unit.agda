{-# OPTIONS --without-K --prop #-}

module SetoidRed.Unit where

open import Agda.Primitive
open import SetoidRed.lib
open import SetoidRed.CwF

Unit : ∀{i}{Γ : Con i} → Ty Γ lzero
∣ Unit ∣T γ = ⊤
Unit T γ~ ⊢ _ ~ _ = ⊤p
refT Unit _ = ttp
symT Unit _ = ttp
transT Unit _ _ = ttp
coeT Unit = _
cohT Unit _ _ = ttp

* : ∀{i}{Γ : Con i} → Tm Γ Unit
∣ * ∣t _ = tt
~t * _ = ttp
