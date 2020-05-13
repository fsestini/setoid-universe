{-# OPTIONS --without-K --prop #-}

module Equations where

open import Agda.Primitive
open import lib using (_≡_; refl)
open import Abbrevs

open import Setoid.CwF

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

open import Setoid.Pi

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

open import Setoid.Sigma

Σ[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{l}{B : Ty (Δ ▷ A) l} →
  Σ' A B [ σ ]T ≡ Σ' (A [ σ ]T) (B [ σ ^ A ]T)
Σ[] = refl

,Σ[] : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}{u : Tm Γ A}{v : Tm Γ (B [ _,_ id {A = A} u ]T)}{l}{Ω : Con l}{ν : Tms Ω Γ} →
  (_,Σ'_ {A = A}{B = B} u v) [ ν ]t ≡ _,Σ'_ {A = A [ ν ]T}{B = B [ ν ^ A ]T} (u [ ν ]t) (v [ ν ]t)
,Σ[] = refl

Σβ₁ : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}{u : Tm Γ A}{v : Tm Γ (B [ _,_ id {A = A} u ]T)} →
  pr₁ {A = A}{B = B}(_,Σ'_ {A = A}{B = B} u v) ≡ u
Σβ₁ = refl

Σβ₂ : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}{u : Tm Γ A}{v : Tm Γ (B [ _,_ id {A = A} u ]T)} →
  pr₂ {A = A}{B = B}(_,Σ'_ {A = A}{B = B} u v) ≡ v
Σβ₂ = refl

Ση : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}{t : Tm Γ (Σ' A B)} →
  (_,Σ'_ {A = A}{B = B} (pr₁ {A = A}{B = B} t) (pr₂ {A = A}{B = B} t)) ≡ t
Ση = refl

open import Setoid.Empty

Empty[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → Empty [ σ ]T ≡ Empty
Empty[] = refl
exfalso[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{t : Tm Δ Empty} → exfalso {A = A} t [ σ ]t ≡ exfalso (t [ σ ]t)
exfalso[] = refl

open import Setoid.Unit

Unit[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → Unit [ σ ]T ≡ Unit
Unit[] = refl
*[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → * [ σ ]t ≡ *
*[] = refl

open import Setoid.Bool

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

open import Setoid.Props

P[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k} → P k [ σ ]T ≡ P k
P[] = refl

ElP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{t : Tm Δ (P k)} → ElP t [ σ ]T ≡ ElP (t [ σ ]t)
ElP[] = refl

irr : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{u v : Tm Γ (ElP a)} → u ≡ v
irr = refl

⊤P[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → ⊤P [ σ ]t ≡ ⊤P
⊤P[] = refl
ttP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → ttP [ σ ]t ≡ ttP
ttP[] = refl

ΠP[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ A) (P k)}{l}{Θ : Con l}{σ : Tms Θ Γ} → ΠP A b [ σ ]t ≡ ΠP (A [ σ ]T) (b [ σ ^ A ]t)
ΠP[] = refl

ΣP[] : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{k}{b : Tm (Γ ▷ ElP a) (P k)}{l}{Θ : Con l}{σ : Tms Θ Γ} →
  ΣP a b [ σ ]t ≡ ΣP (a [ σ ]t) (b [ σ ^ ElP a ]t)
ΣP[] = refl

⊥P[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → ⊥P [ σ ]t ≡ ⊥P
⊥P[] = refl
exfalsoP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{t : Tm Δ (ElP ⊥P)} → exfalsoP {A = A} t [ σ ]t ≡ exfalsoP (t [ σ ]t)
exfalsoP[] = refl

open import Setoid.Sets

U[] : ∀{i j}{Γ : Con i}{Δ : Con j}{σ : Tms Γ Δ} → (U [ σ ]T) ≡ U
U[] = refl

El[] : ∀{i j}{Γ : Con i}{Δ : Con j}{σ : Tms Γ Δ}{Â : Tm Δ U}
     → (El Â [ σ ]T) ≡ (El {i} (Â [ σ ]t))
El[] = refl

ElBool : ∀{i}{Γ : Con i} → El {i}{Γ} BoolS ≡ Bool
ElBool = refl

ElΠ : ∀{i Γ}{Â : Tm Γ U}{B̂ : Tm (Γ ▷ El {i} Â) U} → El (ΠS Â B̂) ≡ Π (El Â) (El B̂)
ElΠ = refl
