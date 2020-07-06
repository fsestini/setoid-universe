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

UnitP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → UnitP [ σ ]t ≡ UnitP
UnitP[] = refl
ttP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → ttP [ σ ]t ≡ ttP
ttP[] = refl

ΠP[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{b : Tm (Γ ▷ A) (P k)}{l}{Θ : Con l}{σ : Tms Θ Γ} → ΠP A b [ σ ]t ≡ ΠP (A [ σ ]T) (b [ σ ^ A ]t)
ΠP[] = refl

ΣP[] : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{k}{b : Tm (Γ ▷ ElP a) (P k)}{l}{Θ : Con l}{σ : Tms Θ Γ} →
  ΣP a b [ σ ]t ≡ ΣP (a [ σ ]t) (b [ σ ^ ElP a ]t)
ΣP[] = refl

EmptyP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ} → EmptyP [ σ ]t ≡ EmptyP
EmptyP[] = refl
exfalsoP[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{k}{A : Ty Δ k}{t : Tm Δ (ElP EmptyP)} → exfalsoP {A = A} t [ σ ]t ≡ exfalsoP (t [ σ ]t)
exfalsoP[] = refl

module IRSets where
  open import Setoid.IRSets

  U[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ} → (U [ σ ]T) ≡ U
  U[] = refl

  El[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ}{a : Tm Δ U}
       → (El a [ σ ]T) ≡ (El (a [ σ ]t))
  El[] = refl

  bool[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ} → (bool [ σ ]t) ≡ bool
  bool[] = refl

  Elbool : ∀{i}{Γ} → El bool ≡ Bool {i}{Γ}
  Elbool = refl

  π[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ}{a : Tm Δ U}{b : Tm (Δ ▷ El a) U}
      → ((π a b) [ σ ]t) ≡ π (a [ σ ]t) (b [ _,_ (σ ∘ π₁ {A = (El a) [ σ ]T} id) {A = El a} (π₂ {A = (El a) [ σ ]T} id)  ]t) -- (b [ σ ^ El a ]t)
  π[] = refl

  Elπ : ∀{i Γ}(a : Tm Γ U)(b : Tm (Γ ▷ El {i} a) U) → El (π a b) ≡ Π (El a) (El b)
  Elπ a b = refl

  ι[] : ∀{i j}{Γ Θ}{σ : Tms {i}{j} Γ Θ}(t : Tm Θ (P lzero)) → ((ι t) [ σ ]t) ≡ (ι (t [ σ ]t))
  ι[] t = refl

  Elι : ∀{i}{Γ : Con i}(a : Tm Γ (P lzero)) → El (ι a) ≡  ElP a
  Elι a = refl

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

open import Setoid.SeTT

[]T~ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}{δ : Tms Γ Δ}{l}{Ω : Con l}
  {σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
  {t₀ : Tm Ω (A [ δ ]T [ σ₀ ]T)}{t₁ : Tm Ω (A [ δ ]T [ σ₁ ]T)} →
  ((A [ δ ]T) ~T) {σ₀ = σ₀}{σ₁} σ₀₁ t₀ t₁ ≡
  (A ~T) {σ₀ = δ ∘ σ₀}{δ ∘ σ₁} ((δ ~s') {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁) t₀ t₁
[]T~ = refl

Π~ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{Ω : Con l}
  {σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
  {t₀ : Tm Ω (Π A B [ σ₀ ]T)}{t₁ : Tm Ω (Π A B [ σ₁ ]T)} →
  let A[σ₀]    = A [ σ₀ ]T
      A[σ₁]    = A [ σ₁ ∘ wk {A = A[σ₀]} ]T
      v0       = vz {A = A[σ₁]}
      v1       = vs {B = A[σ₁]} (vz {A = A[σ₀]})
      wk2      = wk {A = A[σ₀]} ∘ wk {A = A[σ₁]}
      σ₀₁[wk2] = _[_]C {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ wk2
      A~       = ElP ((A ~T) {σ₀ = σ₀ ∘ wk2}{σ₁ = σ₁ ∘ wk2} σ₀₁[wk2] v1 v0)
      wk3      = wk2 ∘ wk {A = A~}
      σ₀₁[wk3] = _[_]C {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ wk3
  in
    ((Π A B) ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡
    ΠP A[σ₀] (ΠP (A[σ₁]) (ΠP A~ ((B ~T)
      {σ₀ = _,_ (σ₀ ∘ wk3){A = A}(vs {B = A~} v1)}
      {σ₁ = _,_ (σ₁ ∘ wk3){A = A}(vs {B = A~} v0)}
      (_,'_ {Γ = Γ}{A = A}{σ₀ = σ₀ ∘ wk3}{σ₁ = σ₁ ∘ wk3} σ₀₁[wk3] {t₀ = vs {B = A~} v1}{t₁ = vs {B = A~} v0}(vz {A = A~}))
      (app {A = A[σ₀]}{B = B [ σ₀ ^ A ]T} t₀ [ wk {A = A[σ₁]} ∘ wk {A = A~} ]t)
      (app {A = A [ σ₁ ]T}{B = B [ σ₁ ^ A ]T} t₁ [ (wk {A = A[σ₀]} ^ (A [ σ₁ ]T)) ∘ wk {A = A~} ]t))))
Π~ = refl

Σ~ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
  {t₀ : Tm Ω (Σ' A B [ σ₀ ]T)}{t₁ : Tm Ω (Σ' A B [ σ₁ ]T)} →
  ((Σ' A B) ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡
  let
    pr₁t₀ = pr₁ {A = A [ σ₀ ]T}{B = B [ σ₀ ^ A ]T} t₀
    pr₁t₁ = pr₁ {A = A [ σ₁ ]T}{B = B [ σ₁ ^ A ]T} t₁
    A~    = (A ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ pr₁t₀ pr₁t₁
    wk'   = wk {A = ElP A~}
    pr₂t₀ = pr₂ {A = A [ σ₀ ]T}{B = B [ σ₀ ^ A ]T} t₀
    pr₂t₁ = pr₂ {A = A [ σ₁ ]T}{B = B [ σ₁ ^ A ]T} t₁
  in
    ΣP ((A ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ pr₁t₀ pr₁t₁)
       ((B ~T) {σ₀ = _,_ (σ₀ ∘ wk'){A = A}(pr₁t₀ [ wk' ]t)}
               {σ₁ = _,_ (σ₁ ∘ wk'){A = A}(pr₁t₁ [ wk' ]t)}
               (_,'_ {Γ = Γ}{A = A}{σ₀ = σ₀ ∘ wk'}{σ₁ = σ₁ ∘ wk'}(σ₀₁ [ wk' ]C){t₀ = pr₁t₀ [ wk' ]t}{t₁ = pr₁t₁ [ wk' ]t} (vz {A = ElP A~}))
               (pr₂t₀ [ wk' ]t)
               (pr₂t₁ [ wk' ]t))
Σ~ = refl

Empty~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Empty} → 
  (Empty ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ UnitP
Empty~ = refl

Unit~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Unit} → 
  (Unit ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ UnitP
Unit~ = refl

Bool~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Bool} → 
  (Bool ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ ite (P lzero) (ite (P lzero) UnitP EmptyP t₁) (ite (P lzero) EmptyP UnitP t₁) t₀
Bool~ = refl

P~ : ∀{i}{Γ : Con i}{j}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{a₀ a₁ : Tm Ω (P j)} → 
  ((P j) ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ a₀ a₁ ≡
  LiftP ((ElP a₀ ⇒P a₁) ×P (ElP a₁ ⇒P a₀))
P~ = refl

ElP~ : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{l}{Ω : Con l}{ρ₀ ρ₁ : Tms Ω Γ}{ρ₀₁ : (Γ ~C) ρ₀ ρ₁}
  {t₀ : Tm Ω (ElP a [ ρ₀ ]T)}{t₁ : Tm Ω (ElP a [ ρ₁ ]T)} →
  ((ElP a) ~T) {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ t₀ t₁ ≡ LiftP UnitP
ElP~ = refl

-- U~

-- El~

coeT[] : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}{A : Ty Γ k}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
  {t₀ : Tm Ω (A [ σ₀ ]T)}{l}{Ψ : Con l}{δ : Tms Ψ Ω} →
  coeT' A {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ [ δ ]t ≡
  coeT' A {σ₀ = σ₀ ∘ δ}{σ₁ = σ₁ ∘ δ}(_[_]C {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ δ) (t₀ [ δ ]t)
coeT[] = refl

coeΠ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{Ω : Con l}{ρ₀ ρ₁ : Tms Ω Γ}{ρ₀₁ : (Γ ~C) ρ₀ ρ₁}{t₀ : Tm Ω (Π A B [ ρ₀ ]T)} →
  let
    wk' = wk {A = A [ ρ₁ ]T}
    vz' = vz {A = A [ ρ₁ ]T}
    t₁  = coeT' A {σ₀ = ρ₁ ∘ wk'}{σ₁ = ρ₀ ∘ wk'}(SC Γ {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ [ wk' ]C) vz'
  in
    coeT' (Π A B) {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ t₀ ≡
    lam {A = A [ ρ₁ ]T}{B = B [ ρ₁ ^ A ]T}
        (coeT' B {σ₀ = _,_ (ρ₀ ∘ wk'){A = A}(coeT' A {σ₀ = ρ₁ ∘ wk'}{σ₁ = ρ₀ ∘ wk'}(SC Γ {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ [ wk' ]C) vz')}
                 {σ₁ = _,_ (ρ₁ ∘ wk'){A = A}(vz')}
                 (_,'_ {Γ = Γ}{A = A}{σ₀ = (ρ₀ ∘ wk')}{σ₁ = (ρ₁ ∘ wk')}(ρ₀₁ [ wk' ]C)
                       {t₀ = t₁}
                       {t₁ = vz'}
                       (ST A
                           {σ₀ = ρ₁ ∘ wk'}
                           {σ₁ = ρ₀ ∘ wk'}
                           {σ₀₁ = SC Γ {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ [ wk' ]C}
                           {t₀ = vz'}
                           {t₁ = t₁}
                           (cohT' A {σ₀ = ρ₁ ∘ wk'}{σ₁ = ρ₀ ∘ wk'}(SC Γ {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ [ wk' ]C) vz')))
                 (app {A = A [ ρ₀ ]T}{B = B [ ρ₀ ^ A ]T} t₀ [ _,_ wk' {A = A [ ρ₀ ]T} ((coeT' A {σ₀ = ρ₁ ∘ wk'}{σ₁ = ρ₀ ∘ wk'}(SC Γ {σ₀ = ρ₀ ∘ wk'}{σ₁ = ρ₁ ∘ wk'} (ρ₀₁ [ wk' ]C)) vz')) ]t))
coeΠ = refl

coeΣ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{Ω : Con l}{ρ₀ ρ₁ : Tms Ω Γ}{ρ₀₁ : (Γ ~C) ρ₀ ρ₁}
  {t₀ : Tm Ω (Σ' A B [ ρ₀ ]T)} →
  let
    pr₁t₀ = pr₁ {A = A [ ρ₀ ]T}{B = B [ ρ₀ ^ A ]T} t₀
    pr₂t₀ = pr₂ {A = A [ ρ₀ ]T}{B = B [ ρ₀ ^ A ]T} t₀
  in
    coeT' (Σ' A B) {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ t₀ ≡
    (_,Σ'_ {A = A [ ρ₁ ]T}{B = B [ ρ₁ ^ A ]T}
           (coeT' A {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ pr₁t₀)
           (coeT' B
                  {σ₀ = _,_ ρ₀ {A = A} pr₁t₀}
                  {σ₁ = _,_ ρ₁ {A = A} (coeT' A {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ pr₁t₀)}
                  (_,'_ {Γ = Γ}{A = A}{σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ {t₀ = pr₁t₀}{t₁ = coeT' A {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ pr₁t₀} (cohT' A {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ pr₁t₀))
                  pr₂t₀))
coeΣ = refl

coeEmpty : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Empty [ σ₀ ]T)} →
  coeT' Empty {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeEmpty = refl

coeUnit : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Unit [ σ₀ ]T)} →
  coeT' Unit {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeUnit = refl

coeBool : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Bool [ σ₀ ]T)} →
  coeT' Bool {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeBool = refl

coeP : ∀{i}{Γ : Con i}{j}{l}{Ω : Con l}{ρ₀ ρ₁ : Tms Ω Γ}{ρ₀₁ : (Γ ~C) ρ₀ ρ₁}
  {t₀ : Tm Ω (P j [ ρ₀ ]T)} →
  coeT' (P j) {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ t₀ ≡ t₀
coeP = refl

coeElP : ∀{i}{Γ : Con i}{j}{a : Tm Γ (P j)}{l}{Ω : Con l}{ρ₀ ρ₁ : Tms Ω Γ}{ρ₀₁ : (Γ ~C) ρ₀ ρ₁}
  {t₀ : Tm Ω ((ElP a) [ ρ₀ ]T)} →
  coeT' (ElP a) {σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁ t₀ ≡
  appP
    {A = ElP (a [ ρ₀ ]t)}
    {b = a [ ρ₁ ]t [ wk {A = ElP (a [ ρ₀ ]t)} ]t}
    (proj₁P
      {a = ElP (a [ ρ₀ ]t) ⇒P a [ ρ₁ ]t}
      {b = (ElP (a [ ρ₁ ]t) ⇒P a [ ρ₀ ]t) [ wk {A = ElP (ElP (a [ ρ₀ ]t) ⇒P a [ ρ₁ ]t)} ]t}
      (unliftP {a = ((ElP (a [ ρ₀ ]t) ⇒P (a [ ρ₁ ]t)) ×P (ElP (a [ ρ₁ ]t) ⇒P (a [ ρ₀ ]t)))} ((a ~t'){σ₀ = ρ₀}{σ₁ = ρ₁} ρ₀₁)))
  [ _,_ id {A = ElP (a [ ρ₀ ]t)} t₀ ]t
coeElP = refl

-- coeU

-- coeEl

open import Setoid.Id

Idβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{a : Tm Γ A}{k}{Id' : Ty (Γ ▷ A) k}{idp' : Tm Γ (Id' [ _,_ id {A = A} a ]T)} →
  recId A a Id' idp' [ _,_ (_,_ id {A = A} a) {A = Id A a} (idp A a) ]t ≡ idp'
Idβ = refl

module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(a a' : Tm Γ A) where

  -- tofrom : toId A a a' [ wk {A = Id A a [ id ,⟨ A ⟩ a' ]T} ,⟨ ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a') ⟩ fromId A a a' ]t ≡ vz {A = Id A a [ id ,⟨ A ⟩ a' ]T}
  -- tofrom = {!refl!}

  fromto :
    fromId A a a' [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ,⟨ Id A a [ id ,⟨ A ⟩ a' ]T ⟩ toId A a a' ]t ≡
    vz {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')}
  fromto = refl
