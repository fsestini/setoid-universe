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

{-
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
Π~ = {!refl!}
-}

-- Σ~

Empty~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Empty} → 
  (Empty ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ UnitP
Empty~ = refl

Unit~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Unit} → 
  (Unit ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ UnitP
Unit~ = refl

Bool~ : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ t₁ : Tm Ω Bool} → 
  (Bool ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ t₁ ≡ ite (P lzero) (ite (P lzero) UnitP EmptyP t₁) (ite (P lzero) EmptyP UnitP t₁) t₀
Bool~ = refl
{-
P~ : ∀{i}{Γ : Con i}{j}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{a₀ a₁ : Tm Ω (P j)} → 
  ((P j) ~T) {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ a₀ a₁ ≡
  LiftP ((ElP a₀ ⇒P a₁) ×P (ElP a₁ ⇒P a₀))
P~ = {!refl!}
-}
-- ElP~

-- U~

-- El~

coeT[] : ∀{i}{Γ : Con i}{j}{Ω : Con j}{k}{A : Ty Γ k}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}
  {t₀ : Tm Ω (A [ σ₀ ]T)}{l}{Ψ : Con l}{δ : Tms Ψ Ω} →
  coeT' A {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ [ δ ]t ≡
  coeT' A {σ₀ = σ₀ ∘ δ}{σ₁ = σ₁ ∘ δ}(_[_]C {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ δ) (t₀ [ δ ]t)
coeT[] = refl

-- coeΠ

-- coeΣ~

coeEmpty : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Empty [ σ₀ ]T)} →
  coeT' Empty {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeEmpty = refl

coeUnit : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Unit [ σ₀ ]T)} →
  coeT' Unit {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeUnit = refl

coeBool : ∀{i}{Γ : Con i}{l}{Ω : Con l}{σ₀ σ₁ : Tms Ω Γ}{σ₀₁ : (Γ ~C) σ₀ σ₁}{t₀ : Tm Ω (Bool [ σ₀ ]T)} →
  coeT' Bool {σ₀ = σ₀}{σ₁ = σ₁} σ₀₁ t₀ ≡ t₀
coeBool = refl

-- coeP

-- coeElP

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
