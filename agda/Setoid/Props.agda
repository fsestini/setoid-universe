{-# OPTIONS --without-K --prop #-}

module Setoid.Props where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

-- a universe of propositions

P : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
P {i}{Γ} j = record
  { ∣_∣T_ = λ γ → Prop j
  ; _T_⊢_~_ = λ _ a b → ↑pl ((↑ps a → b) ×p (↑ps b → a))
  ; refT = λ _ → mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))
  ; symT = λ { (mk↑pl (f ,p g)) → mk↑pl (g ,p f) }
  ; transT = λ { (mk↑pl (f ,p g)) (mk↑pl (f' ,p g')) → mk↑pl ((λ x → f' (mk↑ps (f x))) ,p (λ y → g (mk↑ps (g' y)))) }
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

unliftP : ∀{i}{Γ : Con i}{j}{k}{a : Tm Γ (P j)} → Tm Γ (ElP (LiftP {k = k} a)) → Tm Γ (ElP a)
un↑ps (∣ unliftP t ∣t γ) = un↑pl (un↑ps (∣ t ∣t γ))
un↑pl (~t (unliftP t) _) = ttp

-- empty type

EmptyP : ∀{i}{Γ : Con i} → Tm Γ (P lzero)
∣ EmptyP ∣t _ = ⊥p
~t EmptyP _ = mk↑pl (un↑ps ,p un↑ps)

exfalsoP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ (ElP EmptyP) → Tm Γ A
∣ exfalsoP t ∣t γ = ⊥pelim (un↑ps (∣ t ∣t γ))
~t (exfalsoP t) {γ} _ = ⊥pelimp (un↑ps (∣ t ∣t γ))

-- unit type

UnitP : ∀{i}{Γ : Con i} → Tm Γ (P lzero)
∣ UnitP ∣t _ = ⊤p
~t UnitP _ = mk↑pl ((λ _ → ttp) ,p λ _ → ttp)

ttP : ∀{i}{Γ : Con i} → Tm Γ (ElP UnitP)
∣ ttP ∣t _ = mk↑ps ttp
~t ttP _ = mk↑pl ttp

-- function space

ΠP : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(b : Tm (Γ ▷ A) (P k)) → Tm Γ (P (j ⊔ k))
∣ ΠP A b ∣t γ = (x : ∣ A ∣T γ) → ∣ b ∣t (γ ,Σ x)
~t (ΠP {_}{Γ} A b) γ~ = mk↑pl (
  (λ f x' → proj₁p (un↑pl (~t b (γ~ ,p cohT* A γ~ x'))) (mk↑ps (un↑ps f (coeT* A γ~ x')))) ,p
  (λ f x → proj₂p (un↑pl (~t b (γ~ ,p cohT A γ~ x))) (mk↑ps (un↑ps f (coeT A γ~ x)))))

lamP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ A) (P k)} → Tm (Γ ▷ A) (ElP b) → Tm Γ (ElP (ΠP A b))
un↑ps (∣ lamP {A = A} {b = b} t ∣t γ) x = un↑ps (∣ t ∣t (γ ,Σ x))
~t (lamP {A = A} {b = b} t) _ = mk↑pl (tr tt)

appP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ A) (P k)} → Tm Γ (ElP (ΠP A b)) → Tm (Γ ▷ A) (ElP b)
∣ appP {Γ = Γ} {A = A} {b = b} t ∣t (γ ,Σ x) = mk↑ps (un↑ps (∣ t ∣t γ) x)
~t (appP {Γ = Γ} {A = A} {b = b} t) _ = mk↑pl (tr tt)

-- Sigma types

ΣP : ∀{i}{Γ : Con i}{j}(a : Tm Γ (P j)){k}(b : Tm (Γ ▷ ElP a) (P k)) → Tm Γ (P (j ⊔ k))
∣ ΣP a b ∣t γ = Σp (∣ a ∣t γ) λ x → ∣ b ∣t (γ ,Σ mk↑ps x)
~t (ΣP a b) γ~ = mk↑pl (
  (λ { (mk↑ps (α ,p β)) → (
    proj₁p (un↑pl (~t a γ~)) (mk↑ps α)) ,p
    proj₁p (un↑pl (~t b (γ~ ,p mk↑pl ttp))) (mk↑ps β) }) ,p
  λ { (mk↑ps (α ,p β)) → (
    proj₂p (un↑pl (~t a γ~)) (mk↑ps α) ,p
    proj₂p (un↑pl (~t b (γ~ ,p mk↑pl ttp))) (mk↑ps β)) })

_,P_ : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{k}{b : Tm (Γ ▷ ElP a) (P k)}(t : Tm Γ (ElP a))(u : Tm Γ (ElP b [ _,_ id {A = ElP a} t ]T)) →
  Tm Γ (ElP (ΣP a b))
un↑ps (∣ _,P_ {a = a} {b = b} u v ∣t γ) = un↑ps (∣ u ∣t γ) ,p un↑ps (∣ v ∣t γ)
~t (_,P_ {a = a} {b = b} u v) _ = mk↑pl ttp
infixl 5 _,P_

proj₁P : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{k}{b : Tm (Γ ▷ ElP a) (P k)} → Tm Γ (ElP (ΣP a b)) → Tm Γ (ElP a)
un↑ps (∣ proj₁P {a = a} {b = b} t ∣t γ) = proj₁p (un↑ps (∣ t ∣t γ))
un↑pl (~t (proj₁P {a = a} {b = b} t) _) = ttp

proj₂P : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{k}{b : Tm (Γ ▷ ElP a) (P k)}(w : Tm Γ (ElP (ΣP a b))) →
  Tm Γ (ElP b [ _,_ id {A = ElP a} (proj₁P {a = a}{b = b} w) ]T)
un↑ps (∣ proj₂P {a = a} {b = b} t ∣t γ) = proj₂p (un↑ps (∣ t ∣t γ))
un↑pl (~t (proj₂P {a = a} {b = b} t) _) = ttp
