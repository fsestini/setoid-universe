{-# OPTIONS --without-K --prop #-}

module SetoidRed.Props where

open import Agda.Primitive
open import SetoidRed.lib
open import SetoidRed.CwF

-- a universe of propositions

P : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
P {i}{Γ} j = record
  { ∣_∣T_ = λ γ → Prop j
  ; _T_⊢_~_ = λ _ a b → ↑pl ((↑ps a → b) ×p (↑ps b → a))
  ; refT = λ _ → mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))
  ; symT = λ { (mk↑pl f) → mk↑pl (proj₂p f ,p proj₁p f) }
  ; transT = λ { (mk↑pl f) (mk↑pl f') → mk↑pl ((λ x → proj₁p f' (mk↑ps (proj₁p f x))) ,p (λ y → proj₂p f (mk↑ps (proj₂p f' y)))) }
  ; coeT = λ _ a → a
  ; cohT = λ _ _ → mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))
  }

ElP : ∀{i}{Γ : Con i}{j} → Tm Γ (P j) → Ty Γ j
∣ ElP {Γ} a ∣T γ = ↑ps (∣ a ∣t γ)
ElP {Γ} a T γ~ ⊢ _ ~ _ = ↑pl ⊤p
refT (ElP {Γ} a) _ = mk↑pl ttp
symT (ElP {Γ} a) _ = mk↑pl ttp
transT (ElP {Γ} a) _ _ = mk↑pl ttp
coeT (ElP {Γ} a) γ~ (mk↑ps α) = mk↑ps (proj₁p (un↑pl (~t a γ~)) (mk↑ps α))
cohT (ElP {Γ} a) _ _ = mk↑pl ttp

-- propositional truncation

Trunc : ∀{i}{Γ : Con i}{j} → Ty Γ j → Tm Γ (P j)
∣ Trunc A ∣t γ = Tr (∣ A ∣T γ)
~t (Trunc A) γ~ = mk↑pl ((λ { (mk↑ps (tr α)) → tr (coeT A γ~ α) }) ,p λ { (mk↑ps (tr α)) → tr (coeT* A γ~ α) })

trunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ A → Tm Γ (ElP (Trunc A))
∣ trunc t ∣t γ = mk↑ps (tr (∣ t ∣t γ))
~t (trunc t) _ = mk↑pl ttp

untrunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ ElP (Trunc A)) (P k)} →
  Tm (Γ ▷ A) (ElP b [ _,_ (π₁ {A = A} id){A = ElP (Trunc A)} (trunc (π₂ {A = A} id)) ]T) →
  (u : Tm Γ (ElP (Trunc A))) → Tm Γ (ElP b [ _,_ id {A = ElP (Trunc A)} u ]T)
∣ untrunc t u ∣t γ = mk↑ps (untr (λ α → un↑ps (∣ t ∣t (γ ,Σ α))) (un↑ps (∣ u ∣t γ)))
~t (untrunc t u) _ = mk↑pl ttp

-- lifting universe levels

LiftP : ∀{i}{Γ : Con i}{j}{k} → Tm Γ (P j) → Tm Γ (P (j ⊔ k))
∣ LiftP {j = j}{k = k} a ∣t γ = ↑pl {j}{k} (∣ a ∣t γ)
~t (LiftP a) γ~ = mk↑pl (
  (λ α → mk↑pl (proj₁p (un↑pl (~t a γ~)) (mk↑ps (un↑pl (un↑ps α))))) ,p
  (λ α → mk↑pl (proj₂p (un↑pl (~t a γ~)) (mk↑ps (un↑pl (un↑ps α))))))

liftP : ∀{i}{Γ : Con i}{j}{k}{a : Tm Γ (P j)} → Tm Γ (ElP a) → Tm Γ (ElP (LiftP {k = k} a))
∣ liftP t ∣t γ = mk↑ps (mk↑pl (un↑ps (∣ t ∣t γ)))
~t (liftP t) γ~ = mk↑pl ttp

-- empty type

EmptyP : ∀{i}{Γ : Con i} → Tm Γ (P lzero)
∣ EmptyP ∣t _ = ⊥p
~t EmptyP _ = mk↑pl (un↑ps ,p un↑ps)

exfalsoP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ (ElP EmptyP) → Tm Γ A
∣ exfalsoP t ∣t γ = ⊥pelim (un↑ps (∣ t ∣t γ))
~t (exfalsoP t) {γ} _ = ⊥pelimp (un↑ps (∣ t ∣t γ))
