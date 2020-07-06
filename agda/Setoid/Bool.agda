{-# OPTIONS --without-K --prop #-}

module Setoid.Bool where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

Bool    : ∀{i}{Γ : Con i} → Ty Γ lzero
Bool = mkTy
  (λ _ → 𝟚)
  (λ _ t₀ t₁ → t₀ ≟𝟚 t₁)
  (λ t → ref𝟚 t)
  (λ {_}{_}{_}{t₀}{t₁} t₀₁ → sym𝟚 {t₀} {t₁} t₀₁)
  (λ {_}{_}{_}{_}{_}{t₀}{t₁}{t₂} t₀₁ t₁₂ → trans𝟚 {t₀}{t₁}{t₂} t₀₁ t₁₂)
  (λ _ t → t)
  (λ _ t → ref𝟚 t)

true    : ∀{i}{Γ : Con i} → Tm Γ Bool
∣ true ∣t _ = tt
~t true _ = ttp

false   : ∀{i}{Γ : Con i} → Tm Γ Bool
∣ false ∣t _ = ff
~t false _ = ttp

ite :
  ∀{i}{Γ : Con i}{j}(C : Ty (Γ ▷ Bool) j)
      → Tm Γ (C [ (_,_ id {A = Bool} true) ]T)
      → Tm Γ (C [ (_,_ id {A = Bool} false) ]T)
      → (t : Tm Γ Bool)
      → Tm Γ (C [ (_,_ id {A = Bool} t) ]T)
ite {i}{Γ}{j} = λ C u v t → record {
  ∣_∣t = λ γ → if_then_else_ {C = λ b → ∣ C ∣T γ ,Σ b} (∣ t ∣t γ) (∣ u ∣t γ) (∣ v ∣t γ) ;
  ~t = λ {γ}{γ'} γ~ → 
    pif_then_else_
      {j}
      {C = λ b → (b~ : Bool {i}{Γ} T γ~ ⊢ b ~ ∣ t ∣t γ') → C T (γ~ ,p b~) ⊢ (if_then_else_ {C = λ b → ∣ C ∣T γ ,Σ b} b (∣ u ∣t γ) (∣ v ∣t γ)) ~ (if_then_else_ {C = λ b → ∣ C ∣T γ' ,Σ b} (∣ t ∣t γ') (∣ u ∣t γ') (∣ v ∣t γ'))}
      (∣ t ∣t γ)
      (pif_then_else_ {C = λ b → (b~ : Bool {i}{Γ} T γ~ ⊢ tt ~ b) → C T (γ~ ,p b~) ⊢ (∣ u ∣t γ) ~ (if_then_else_ {C = λ b → ∣ C ∣T γ' ,Σ b} b (∣ u ∣t γ') (∣ v ∣t γ'))} (∣ t ∣t γ') (λ _ → ~t u γ~) (λ ()))
      (pif_then_else_ {C = λ b → (b~ : Bool {i}{Γ} T γ~ ⊢ ff ~ b) → C T (γ~ ,p b~) ⊢ (∣ v ∣t γ) ~ (if_then_else_ {C = λ b → ∣ C ∣T γ' ,Σ b} b (∣ u ∣t γ') (∣ v ∣t γ'))} (∣ t ∣t γ') (λ ()) (λ _ → ~t v γ~))
      (~t t γ~)
       }
