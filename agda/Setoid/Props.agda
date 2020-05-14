{-# OPTIONS --without-K --prop #-}

module Setoid.Props where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

-- a universe of propositions

P : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
P {i}{Γ} j = record
  { ∣_∣T_ = λ γ → Prop j
  ; _T_⊢_~_ = λ _ a b → LiftP ((Liftp a → b) ×p (Liftp b → a))
  ; refT = λ _ → liftP ((λ x → unliftp x) ,p (λ x → unliftp x))
  ; symT = λ { (liftP (f ,p g)) → liftP (g ,p f) }
  ; transT = λ { (liftP (f ,p g)) (liftP (f' ,p g')) → liftP ((λ x → f' (liftp (f x))) ,p (λ y → g (liftp (g' y)))) }
  ; coeT = λ _ a → a
  ; cohT = λ _ _ → liftP ((λ x → unliftp x) ,p (λ x → unliftp x))
  }

ElP : ∀{i}{Γ : Con i}{j} → Tm Γ (P j) → Ty Γ j
∣ ElP {Γ} a ∣T γ = Liftp (∣ a ∣t γ)
ElP {Γ} a T γ~ ⊢ _ ~ _ = LiftP ⊤p
refT (ElP {Γ} a) _ = liftP ttp
symT (ElP {Γ} a) _ = liftP ttp
transT (ElP {Γ} a) _ _ = liftP ttp
coeT (ElP {Γ} a) γ~ (liftp α) = liftp (proj₁p (unliftP (~t a γ~)) (liftp α))
cohT (ElP {Γ} a) _ _ = liftP ttp

-- propositional truncation

Trunc : ∀{i}{Γ : Con i}{j} → Ty Γ j → Tm Γ (P j)
∣ Trunc A ∣t γ = Tr (∣ A ∣T γ)
~t (Trunc A) γ~ = liftP ((λ { (liftp (tr α)) → tr (coeT A γ~ α) }) ,p λ { (liftp (tr α)) → tr (coeT* A γ~ α) })

trunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ A → Tm Γ (ElP (Trunc A))
∣ trunc t ∣t γ = liftp (tr (∣ t ∣t γ))
~t (trunc t) _ = liftP ttp

untrunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ ElP (Trunc A)) (P k)} →
  Tm (Γ ▷ A) (ElP b [ _,_ (π₁ {A = A} id){A = ElP (Trunc A)} (trunc (π₂ {A = A} id)) ]T) →
  (u : Tm Γ (ElP (Trunc A))) → Tm Γ (ElP b [ _,_ id {A = ElP (Trunc A)} u ]T)
∣ untrunc t u ∣t γ = liftp (untr (λ α → unliftp (∣ t ∣t (γ ,Σ α))) (unliftp (∣ u ∣t γ)))
~t (untrunc t u) _ = liftP ttp

-- empty type

⊥P : ∀{i}{Γ : Con i} → Tm Γ (P lzero)
∣ ⊥P ∣t _ = ⊥p
~t ⊥P _ = liftP (unliftp ,p unliftp)

exfalsoP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ (ElP ⊥P) → Tm Γ A
∣ exfalsoP t ∣t γ = ⊥pelim (unliftp (∣ t ∣t γ))
~t (exfalsoP t) {γ} _ = ⊥pelimp (unliftp (∣ t ∣t γ))

