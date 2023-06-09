{-# OPTIONS --without-K --prop #-}

module Setoid.Sigma where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

Σ' : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k) → Ty Γ (j ⊔ k)
Σ' {i}{Γ}{j} A {k} B = mkTy
  (λ γ → Σ (∣ A ∣T γ) (λ α → ∣ B ∣T (γ ,Σ α)))
  (λ { γ~ (u₀ ,Σ v₀) (u₁ ,Σ v₁) → Σp (A T γ~ ⊢ u₀ ~ u₁) λ u₀₁ → B T γ~ ,p u₀₁ ⊢ v₀ ~ v₁ })
  (λ { (u ,Σ v) → refT A u ,p refT B v })
  (λ { {_}{_}{_}{u₀ ,Σ v₀}{u₁ ,Σ v₁}(u₀₁ ,p v₀₁) → (symT A u₀₁) ,p symT B v₀₁ })
  (λ { {_}{_}{_}{_}{_}{u₀ ,Σ v₀}{u₁ ,Σ v₁}{u₂ ,Σ v₂}(u₀₁ ,p v₀₁)(u₁₂ ,p v₁₂) → (transT A u₀₁ u₁₂) ,p transT B v₀₁ v₁₂ })
  (λ { γ~ (u₀ ,Σ v₀) → coeT A γ~ u₀ ,Σ coeT B (γ~ ,p (cohT A γ~ u₀)) v₀ })
  (λ { γ~ (u₀ ,Σ v₀) → cohT A γ~ u₀ ,p cohT B (γ~ ,p (cohT A γ~ u₀)) v₀ })

_,Σ'_ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}(u : Tm Γ A)(v : Tm Γ (B [ _,_ id {A = A} u ]T)) → Tm Γ (Σ' A B)
u ,Σ' v = record {
  ∣_∣t = λ γ → ∣ u ∣t γ ,Σ ∣ v ∣t γ ;
  ~t   = λ γ~ → ~t u γ~ ,p ~t v γ~ }

pr₁ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k} → Tm Γ (Σ' A B) → Tm Γ A
pr₁ t = record {
  ∣_∣t = λ γ → proj₁ (∣ t ∣t γ) ;
  ~t   = λ γ~ → proj₁p (~t t γ~) }

pr₂ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}(t : Tm Γ (Σ' A B)) → Tm Γ (B [ _,_ id {A = A} (pr₁ {A = A}{B} t) ]T)
pr₂ t = record {
  ∣_∣t = λ γ → proj₂ (∣ t ∣t γ) ;
  ~t   = λ γ~ → proj₂p (~t t γ~) }
