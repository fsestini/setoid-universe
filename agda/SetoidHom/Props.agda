{-# OPTIONS --without-K --prop #-}

module SetoidHom.Props where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF

-- a universe of propositions

P : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
∣ EL (P {i} {Γ} j) γ ∣C = Prop j
_⊢_~_ (EL (P {i} {Γ} j) γ) a b = ↑pl ((↑ps a → b) ×p (↑ps b → a))
refC (EL (P {i} {Γ} j) γ) a = mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))
symC (EL (P {i} {Γ} j) γ) = λ { (mk↑pl (f ,p g)) → mk↑pl (g ,p f) }
transC (EL (P {i} {Γ} j) γ) = λ { (mk↑pl (f ,p g)) (mk↑pl (f' ,p g')) → mk↑pl ((λ x → f' (mk↑ps (f x))) ,p (λ y → g (mk↑ps (g' y)))) }
subst (P {i} {Γ} j) γ₀₁ = ID _
subst-ref (P {i} {Γ} j) a = mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))
subst-trans (P {i} {Γ} j) γ₀₁ γ₁₂ a = mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))

ElP : ∀{i}{Γ : Con i}{j} → Tm Γ (P j) → Ty Γ j
∣ EL (ElP a) γ ∣C = ↑ps (∣ a ∣t γ)
_⊢_~_ (EL (ElP a) γ) _ _ = ⊤p'
refC (EL (ElP a) γ) _ = ttp'
symC (EL (ElP a) γ) _ = ttp'
transC (EL (ElP a) γ) _ _ = ttp'
∣ subst (ElP a) γ₀₁ ∣s α = mk↑ps (proj₁p (un↑pl (~t a γ₀₁)) α)
~s (subst (ElP a) γ₀₁) _ = ttp'
subst-ref (ElP a) _ = ttp'
subst-trans (ElP a) _ _ _ = ttp'

-- propositional truncation

Trunc : ∀{i}{Γ : Con i}{j} → Ty Γ j → Tm Γ (P j)
∣ Trunc A ∣t γ = Tr (∣ A ∣T γ)
~t (Trunc {Γ = Γ} A) γ~ = mk↑pl ((λ { (mk↑ps (tr α)) → tr (∣ subst A γ~ ∣s α) }) ,p (λ { (mk↑ps (tr α)) → tr (∣ subst A (symC Γ γ~) ∣s α) }))

trunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ A → Tm Γ (ElP (Trunc A))
∣ trunc t ∣t γ = mk↑ps (tr (∣ t ∣t γ))
~t (trunc t) _ = ttp'

untrunc : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ ElP (Trunc A)) (P k)} →
  Tm (Γ ▷ A) (ElP b [ _,_ (π₁ {A = A} id){A = ElP (Trunc A)} (trunc (π₂ {A = A} id)) ]T) →
  (u : Tm Γ (ElP (Trunc A))) → Tm Γ (ElP b [ _,_ id {A = ElP (Trunc A)} u ]T)
∣ untrunc t u ∣t γ = mk↑ps (untr (λ α → un↑ps (∣ t ∣t (γ ,Σ α))) (un↑ps (∣ u ∣t γ)))
~t (untrunc t u) _ = ttp'

-- -- lifting universe levels

-- LiftP : ∀{i}{Γ : Con i}{j}{k} → Tm Γ (P j) → Tm Γ (P (j ⊔ k))
-- ∣ LiftP {j = j}{k = k} a ∣t γ = ↑pl {j}{k} (∣ a ∣t γ)
-- ~t (LiftP a) γ~ = mk↑pl (
--   (λ α → mk↑pl (proj₁p (un↑pl (~t a γ~)) (mk↑ps (un↑pl (un↑ps α))))) ,p
--   (λ α → mk↑pl (proj₂p (un↑pl (~t a γ~)) (mk↑ps (un↑pl (un↑ps α))))))

-- liftP : ∀{i}{Γ : Con i}{j}{k}{a : Tm Γ (P j)} → Tm Γ (ElP a) → Tm Γ (ElP (LiftP {k = k} a))
-- ∣ liftP t ∣t γ = mk↑ps (mk↑pl (un↑ps (∣ t ∣t γ)))
-- ~t (liftP t) γ~ = ttp'

-- empty type

EmptyP : ∀{i}{Γ : Con i} → Tm Γ (P lzero)
∣ EmptyP ∣t _ = ⊥p
~t EmptyP _ = mk↑pl (un↑ps ,p un↑ps)

exfalsoP : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ (ElP EmptyP) → Tm Γ A
∣ exfalsoP t ∣t γ = ⊥pelim (un↑ps (∣ t ∣t γ))
~t (exfalsoP t) {γ} _ = ⊥pelimp (un↑ps (∣ t ∣t γ))


-- sigma type

ΣP : ∀{i j k}{Γ : Con i}(a : Tm Γ (P j))(b : Tm (Γ ▷ ElP a) (P k)) → Tm Γ (P (j ⊔ k))
∣ ΣP {Γ} a b ∣t γ = Σp (∣ a ∣t γ) λ α → ∣ b ∣t (γ ,Σ mk↑ps α)
~t (ΣP {Γ} a b) {γ}{γ'} γ~ = mk↑pl ((λ { (mk↑ps (α ,p β)) → (proj₁p (un↑pl (~t a γ~)) (mk↑ps α)) ,p proj₁p (un↑pl (~t b (γ~ ,p ttp'))) (mk↑ps β) } )
                                    ,p λ { (mk↑ps (α ,p β)) → (proj₂p (un↑pl (~t a γ~)) (mk↑ps α)) ,p proj₂p (un↑pl (~t b (γ~ ,p ttp'))) (mk↑ps β) })

_,P_ : ∀{i j k}{Γ : Con i}{a : Tm Γ (P j)}{b : Tm (Γ ▷ ElP a) (P k)}(t : Tm Γ (ElP a))(u : Tm Γ (ElP b [ _,_ id {A = ElP a} t ]T)) → Tm Γ (ElP (ΣP a b))
∣ t ,P u ∣t γ = mk↑ps (un↑ps (∣ t ∣t γ) ,p un↑ps (∣ u ∣t γ))
~t (t ,P u) γ₀₁ = ttp'

-- proj₁P : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P} → Tm Γ (ElP (ΣP a b)) → Tm Γ (ElP a)
-- proj₁P w = record { ∣_∣t = λ γ → liftp (proj₁p (unliftp (∣ w ∣t γ))) }

-- proj₂P : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P}(w : Tm Γ (ElP (ΣP a b))) →
--   Tm Γ (ElP b [ < proj₁P {a = a}{b} w > ]T)
-- proj₂P w = record { ∣_∣t = λ γ → liftp (proj₂p (unliftp (∣ w ∣t γ))) }

-- ΣPβ₁ : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P}{t : Tm Γ (ElP a)}{u : Tm Γ (ElP b [ < t > ]T)} →
--   proj₁P {a = a}{b} (_,P_ {a = a}{b} t u) ≡ t
-- ΣPβ₁ = refl

-- ΣPβ₂ : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P}{t : Tm Γ (ElP a)}{u : Tm Γ (ElP b [ < t > ]T)}
--   → proj₂P {a = a}{b} (_,P_ {a = a}{b} t u) ≡ u
-- ΣPβ₂ = refl

-- ΣP[] : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P}{Θ : Con}{σ : Tms Θ Γ} →
--   ΣP a b [ σ ]t ≡ ΣP (a [ σ ]t) (b [ σ ^ ElP a ]t)
-- ΣP[] = refl

-- ,P[] : {Γ : Con}{a : Tm Γ P}{b : Tm (Γ , ElP a) P}{t : Tm Γ (ElP a)}{u : Tm Γ (ElP b [ < t > ]T)}{Θ : Con}{σ : Tms Θ Γ} →
--   (_,P_ {a = a}{b} t u) [ σ ]t ≡ _,P_ {a = a [ σ ]t}{b = b [ σ ^ ElP a ]t} (t [ σ ]t) (u [ σ ]t)
-- ,P[] = refl
