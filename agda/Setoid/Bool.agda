{-# OPTIONS --without-K --prop #-}

module Setoid.Bool where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

Bool    : ∀{i}{Γ : Con i} → Ty Γ lzero
Bool = mkTy
  (λ _ → 𝟚)
  (λ _ t₀ t₁ → if t₀ then (if t₁ then ⊤p else ⊥p) else (if t₁ then ⊥p else ⊤p))
  (λ t → pif_then_else_ {C = λ t → if t then (if t then ⊤p else ⊥p) else (if t then ⊥p else ⊤p)} t ttp ttp)
  (λ {_}{_}{_}{t₀}{t₁} t₀₁ →
    pif_then_else_
      {C = λ t₀ → if t₀ then if t₁ then ⊤p else ⊥p else (if t₁ then ⊥p else ⊤p) → if t₁ then if t₀ then ⊤p else ⊥p else (if t₀ then ⊥p else ⊤p)}
      t₀
      (λ x → x)
      (λ x → x)
      t₀₁)
  (λ {_}{_}{_}{_}{_}{t₀}{t₁}{t₂} t₀₁ t₁₂ →
    pif_then_else_
      {C = λ t₀ → if t₀ then if t₁ then ⊤p else ⊥p else (if t₁ then ⊥p else ⊤p) → if t₁ then if t₂ then ⊤p else ⊥p else (if t₂ then ⊥p else ⊤p) → if t₀ then if t₂ then ⊤p else ⊥p else (if t₂ then ⊥p else ⊤p)}
      t₀
      (λ x y → 
        pif_then_else_
          {C = λ t₁ → if t₁ then ⊤p else ⊥p → if t₁ then if t₂ then ⊤p else ⊥p else (if t₂ then ⊥p else ⊤p) → if t₂ then ⊤p else ⊥p}
          t₁ (λ _ x → x) (λ ()) x y)
      (λ x y →
        pif_then_else_
          {C = λ t₁ → if t₁ then ⊥p else ⊤p → if t₁ then if t₂ then ⊤p else ⊥p else (if t₂ then ⊥p else ⊤p) → if t₂ then ⊥p else ⊤p}
          t₁ (λ ()) (λ _ x → x) x y)
      t₀₁
      t₁₂)
  (λ _ t → t)
  (λ _ t → pif_then_else_ {C = λ t → if t then (if t then ⊤p else ⊥p) else (if t then ⊥p else ⊤p)} t ttp ttp)

true    : ∀{i}{Γ : Con i} → Tm Γ Bool
true = record { ∣_∣t = λ _ → tt }

false   : ∀{i}{Γ : Con i} → Tm Γ Bool
false = record { ∣_∣t = λ _ → ff }

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
