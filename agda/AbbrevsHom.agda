{-# OPTIONS --without-K --prop #-}

module AbbrevsHom where

open import Agda.Primitive
open import lib using (_≡_; refl)

open import SetoidHom.CwF

wk : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tms (Γ ▷ A) Γ
wk {A = A} = π₁ {A = A} id

vz : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm (Γ ▷ A) (A [ wk {A = A} ]T)
vz {A = A} = π₂ {A = A} id

vs : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty Γ k} → Tm Γ A → Tm (Γ ▷ B) (A [ wk {A = B} ]T) 
vs {B = B} x = x [ wk {A = B} ]t

<_> : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm Γ A → Tms Γ (Γ ▷ A)
<_> {i}{Γ}{j}{A} t = _,_ id {A = A} t
infix 4 <_>

_^_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Tms Γ Δ){k}(A : Ty Δ k) → Tms (Γ ▷ A [ σ ]T) (Δ ▷ A)
_^_ {Γ}{Δ} σ {b} A = _,_ (σ ∘ wk {A = A [ σ ]T}) {A = A} (vz {A = A [ σ ]T})
infixl 5 _^_

_,⟨_⟩_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Tms Γ Δ){k}(A : Ty Δ k)
         → Tm Γ (A [ σ ]T) → Tms Γ (Δ ▷ A)
_,⟨_⟩_ σ A = _,_ σ {A = A}
infixl 5  _,⟨_⟩_

open import SetoidHom.Pi

infixr 1 _⇒_ _⇛_ --   \r=   and \r==
_⇛_ = Π
_⇒_ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty Γ k) → Ty Γ (j ⊔ k)
A ⇒ B = A ⇛ (B [ wk {A = A} ]T)

oldapp : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k)(t : Tm Γ (Π A B))(u : Tm Γ A) → Tm Γ (B [ < u > ]T)
oldapp A B t u = (app {A = A}{B = B} t) [ < u > ]t
