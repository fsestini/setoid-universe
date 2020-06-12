{-# OPTIONS --without-K --prop #-}

module EquationsHom where

open import Agda.Primitive
open import lib using (_≡_; refl)
open import AbbrevsHom

open import SetoidHom.CwF

[id]T : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → A [ id ]T ≡ A
[][]T : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Δ : Con k}{l}{A : Ty Δ l}{σ : Tms Θ Δ}{δ : Tms Γ Θ} → (A [ σ ]T [ δ ]T) ≡ (A [ σ ∘ δ ]T)
idl   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{δ : Tms Γ Δ} → (id ∘ δ) ≡ δ
idr   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{δ : Tms Γ Δ} → (δ ∘ id) ≡ δ
ass   : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Ψ : Con k}{l}{Δ : Con l}{σ : Tms Ψ Δ}{δ : Tms Θ Ψ}{ν : Tms Γ Θ} →
  ((σ ∘ δ) ∘ ν) ≡ (σ ∘ (δ ∘ ν))
,∘    : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Δ : Con k}{σ : Tms Θ Δ}{δ : Tms Γ Θ}{l}{A : Ty Δ l}{t : Tm Θ (A [ σ ]T)} →
  (_,_ σ {A = A} t) ∘ δ ≡ _,_ (σ ∘ δ) {A = A} (t [ δ ]t)
π₁β   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{δ : Tms Γ Δ}{k}{A : Ty Δ k}{a : Tm Γ (A [ δ ]T)} → (π₁ {A = A}(_,_ δ {A = A} a)) ≡ δ
πη    : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}{δ : Tms Γ (Δ ▷ A)} → (_,_ (π₁ {A = A} δ) {A = A} (π₂ {A = A} δ)) ≡ δ
εη    : ∀{i}{Γ : Con i}{σ : Tms Γ •} → σ ≡ ε
π₂β   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{δ : Tms Γ Δ}{k}{A : Ty Δ k}{a : Tm Γ (A [ δ ]T)} → (π₂ {A = A}(_,_ δ {A = A} a)) ≡ a

[id]T = refl
[][]T = refl
idl   = refl
idr   = refl
ass   = refl
,∘    = refl
π₁β   = refl
πη    = refl
εη    = refl
π₂β   = refl

open import SetoidHom.Pi

Π[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{l}{B : Ty (Δ ▷ A) l} →
  Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
Π[] = refl

lam[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{l}{B : Ty (Δ ▷ A) l}{t : Tm (Δ ▷ A) B} →
      (_[_]t {i}{Γ}{j}{Δ}{_}{Π A B}(lam {_}{Δ}{_}{A}{_}{B} t) σ) ≡ (lam {_}{Γ}{_}{A [ σ ]T}{_}{B [ σ ^ A ]T}(t [ σ ^ A ]t))
lam[] = refl

Πβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{t : Tm (Γ ▷ A) B} →
  app {i}{Γ}{j}{A}{k}{B} (lam {i}{Γ}{j}{A}{k}{B} t) ≡ t
Πβ = refl

Πη : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{t : Tm Γ (Π A B)} →
  lam {i}{Γ}{j}{A}{k}{B} (app {i}{Γ}{j}{A}{k}{B} t) ≡ t
Πη = refl

open import SetoidHom.Bool

Bool[]  : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → Bool [ σ ]T ≡ Bool
Bool[] = refl
true[]  : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → true [ σ ]t ≡ true
true[] = refl
false[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → false [ σ ]t ≡ false
false[] = refl

ite-true :
  ∀{i}{Γ : Con i}{j}{C : Ty (Γ ▷ Bool) j}
      → {u : Tm Γ (C [ (_,_ id {A = Bool} true) ]T)}
      → {v : Tm Γ (C [ (_,_ id {A = Bool} false) ]T)}
      → ite C u v true ≡ u
ite-true = refl

ite-false :
  ∀{i}{Γ : Con i}{j}{C : Ty (Γ ▷ Bool) j}
      → {u : Tm Γ (C [ (_,_ id {A = Bool} true) ]T)}
      → {v : Tm Γ (C [ (_,_ id {A = Bool} false) ]T)}
      → ite C u v false ≡ v
ite-false = refl

ite[]   : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}
          → {C  : Ty (Δ ▷ Bool) j}
          → {u : Tm Δ (C [ (_,_ id {A = Bool} true) ]T)}
          → {v : Tm Δ (C [ (_,_ id {A = Bool} false) ]T)}
          → {t  : Tm Δ Bool}
          → ite C u v t [ σ ]t ≡ ite (C [ σ ^ Bool ]T) (u [ σ ]t) (v [ σ ]t) (t [ σ ]t)
ite[] = refl


open import SetoidHom.Id


Id[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{l}{A : Ty Δ l}{u v : Tm Δ A}
       → (Id A u v) [ σ ]T ≡ Id (A [ σ ]T) (u [ σ ]t) (v [ σ ]t)
Id[] = refl

idp[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{l}{A : Ty Δ l}{a : Tm Δ A}
        → idp A a [ σ ]t ≡ idp (A [ σ ]T) (a [ σ ]t)
idp[] = refl
