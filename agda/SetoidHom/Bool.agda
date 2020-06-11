{-# OPTIONS --without-K --prop #-}

module SetoidHom.Bool where

open import lib
open import Agda.Primitive

open import SetoidHom.lib
open import SetoidHom.CwF


Bool : ∀{i}{Γ : Con i} → Ty Γ lzero
Bool = record {
  EL = λ _ → record {
    ∣_∣C = 𝟚 ;
    _⊢_~_ = λ t₀ t₁ → if t₀ then (if t₁ then ⊤p else ⊥p) else (if t₁ then ⊥p else ⊤p) ;
    refC = λ t → pif_then_else_ {C = λ t → if t then (if t then ⊤p else ⊥p) else (if t then ⊥p else ⊤p)} t ttp ttp ;
    symC = λ {t₀}{t₁} t₀₁ →
      pif_then_else_
        {C = λ t₀ → if t₀ then if t₁ then ⊤p else ⊥p else (if t₁ then ⊥p else ⊤p) → if t₁ then if t₀ then ⊤p else ⊥p else (if t₀ then ⊥p else ⊤p)}
        t₀
        (λ x → x)
        (λ x → x)
        t₀₁ ;
    transC = λ {t₀}{t₁}{t₂} t₀₁ t₁₂ →
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
        t₁₂ } ;
  subst = λ γ~ → id ;
  subst-ref = λ t → pif_then_else_ {C = λ t → if t then (if t then ⊤p else ⊥p) else (if t then ⊥p else ⊤p)} t ttp ttp ;
  subst-trans = λ _ _ t → pif_then_else_ {C = λ t → if t then (if t then ⊤p else ⊥p) else (if t then ⊥p else ⊤p)} t ttp ttp }

true    : ∀{i}{Γ : Con i} → Tm Γ Bool
true = record { ∣_∣t = λ _ → tt ; ~t = λ _ → ttp }
false   : ∀{i}{Γ : Con i} → Tm Γ Bool
false = record { ∣_∣t = λ _ → ff ; ~t = λ _ → ttp }

ite :
  ∀{i}{Γ : Con i}{j}(C : Ty (Γ ▷ Bool) j)
      → Tm Γ (C [ (_,_ id {A = Bool} true) ]T)
      → Tm Γ (C [ (_,_ id {A = Bool} false) ]T)
      → (t : Tm Γ Bool)
      → Tm Γ (C [ (_,_ id {A = Bool} t) ]T)
ite {i}{Γ}{j} = λ C u v t → record {
  ∣_∣t = λ γ → if_then_else_ {C = λ b → ∣ EL C (γ ,Σ b) ∣C} (∣ t ∣t γ) (∣ u ∣t γ) (∣ v ∣t γ) ;
  ~t = λ {γ}{γ'} γ~ → pif_then_else_
      {j}
      {C = λ b → (b~ : EL {i}{Γ} Bool γ' ⊢ b ~ ∣ t ∣t γ') → EL C (γ' ,Σ ∣ t ∣t γ') ⊢ ∣ subst C (γ~ ,p b~) ∣s (if_then_else_ {C = λ b → ∣ EL C (γ ,Σ b) ∣C} b (∣ u ∣t γ) (∣ v ∣t γ)) ~ (if_then_else_ {C = λ b → ∣ EL C (γ' ,Σ b) ∣C} (∣ t ∣t γ') (∣ u ∣t γ') (∣ v ∣t γ'))}
      (∣ t ∣t γ)
      (pif_then_else_ {C = λ b → (b~ : EL {i}{Γ} Bool γ' ⊢ tt ~ b) → EL C (γ' ,Σ b) ⊢ ∣ subst C (γ~ ,p b~) ∣s (∣ u ∣t γ) ~ (if_then_else_ {C = λ b → ∣ EL C (γ' ,Σ b) ∣C} b (∣ u ∣t γ') (∣ v ∣t γ'))} (∣ t ∣t γ') (λ _ → ~t u γ~) (λ ()))
      (pif_then_else_ {C = λ b → (b~ : EL {i}{Γ} Bool γ' ⊢ ff ~ b) → EL C (γ' ,Σ b) ⊢ ∣ subst C (γ~ ,p b~) ∣s (∣ v ∣t γ) ~ (if_then_else_ {C = λ b → ∣ EL C (γ' ,Σ b) ∣C} b (∣ u ∣t γ') (∣ v ∣t γ'))} (∣ t ∣t γ') (λ ()) (λ _ → ~t v γ~))
      (~t t γ~) }
