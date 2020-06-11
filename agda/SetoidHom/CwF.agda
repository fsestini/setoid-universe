{-# OPTIONS --without-K --prop #-}

module SetoidHom.CwF where

open import Agda.Primitive
open import SetoidHom.lib

infixl 5 _▷_
infixl 7 _[_]T
infixl 5 _,_
infixr 6 _∘_
infixl 8 _[_]t

Con = Setoid
Tms = SetoidMor
Ty  = SetoidFam
Tm  = SetoidSec

transC3 : ∀{i}(Γ : Con i){γ γ' γ'' γ''' : ∣ Γ ∣C} → Γ ⊢ γ ~ γ' → Γ ⊢ γ' ~ γ'' → Γ ⊢ γ'' ~ γ''' → Γ ⊢ γ ~ γ'''
transC3 Γ γ~ γ~' γ~'' = transC Γ γ~ (transC Γ γ~' γ~'')

• : Con lzero
∣ • ∣C = ⊤
• ⊢ _ ~ _ = ⊤p
refC • _ = ttp
symC • _ = ttp
transC • _ _ = ttp

_▷_ : ∀{i}(Γ : Con i){j} → Ty Γ j → Con (i ⊔ j)
_▷_ Γ A = record
  { ∣_∣C   = Σ ∣ Γ ∣C λ γ → ∣ EL A γ ∣C
  ; _⊢_~_  = λ { (γ ,Σ α)(γ' ,Σ α') → Σp (Γ ⊢ γ ~ γ') λ γ~ → EL A γ' ⊢ ∣ subst A γ~ ∣s α ~ α' }
  ; refC   = λ { (γ ,Σ α) → refC Γ γ ,p subst-ref A α }
  ; symC   = λ { {γ ,Σ α}{γ' ,Σ α'}(γ~ ,p α~) → symC Γ γ~ ,p transC (EL A γ) (transC (EL A γ)
                                                               (~s (subst A (symC Γ γ~)) (symC (EL A γ') α~))
                                                               (symC (EL A γ) ((subst-trans A γ~ (symC Γ γ~)) α)))
                                                               (subst-ref A α) }
  ; transC = λ { {γ ,Σ α}{γ' ,Σ α'}{γ'' ,Σ α''}(γ~ ,p α~)(γ~' ,p α~') →
      transC Γ γ~ γ~' ,p transC (EL A γ'') (subst-trans A γ~ γ~' α) (transC (EL A γ'') (~s (subst A γ~') α~) α~') }
  }

_[_]T : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k} → Ty Δ k → Tms Γ Δ → Ty Γ k
A [ σ ]T = record {
  EL = λ γ → EL A (∣ σ ∣s γ) ;
  subst = λ γ~ → subst A (~s σ γ~) ;
  subst-ref = subst-ref A ;
  subst-trans = λ γ~ γ~' → subst-trans A (~s σ γ~) (~s σ γ~') }

id : ∀{i}{Γ : Con i} → Tms Γ Γ
id = record
  { ∣_∣s = λ γ → γ
  ; ~s   = λ p → p
  }

_∘_ : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Δ : Con k} → Tms Θ Δ → Tms Γ Θ → Tms Γ Δ
σ ∘ ν = record
  { ∣_∣s = λ γ → ∣ σ ∣s (∣ ν ∣s γ)
  ; ~s   = λ p → ~s σ (~s ν p)
  }

ε : ∀{i}{Γ : Con i} → Tms Γ •
ε = record
  { ∣_∣s = λ _ → tt ;
    ~s = λ _ → ttp
  }

_,_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Tms Γ Δ){b}{A : Ty Δ b} → Tm Γ (A [ σ ]T) → Tms Γ (Δ ▷ A)
σ , t = record { ∣_∣s = λ γ → ∣ σ ∣s γ ,Σ ∣ t ∣t γ ; ~s = λ p → ~s σ p ,p ~t t p }

π₁ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k} → Tms Γ (Δ ▷ A) →  Tms Γ Δ
π₁ σ = record { ∣_∣s = λ γ → proj₁ (∣ σ ∣s γ) ; ~s = λ p → proj₁p (~s σ p) }

_[_]t : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ]t = record { ∣_∣t = λ γ → ∣ t ∣t (∣ σ ∣s γ) ; ~t = λ p → ~t t (~s σ p) }

π₂ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}(σ : Tms Γ (Δ ▷ A)) → Tm Γ (A [ π₁ {A = A} σ ]T)
π₂ σ = record { ∣_∣t = λ γ → proj₂ (∣ σ ∣s γ) ; ~t = λ p → proj₂p (~s σ p) }
