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


open import SetoidHom.Sigma
open import SetoidHom.Props
open import SetoidHom.Id


Id[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{l}{A : Ty Δ l}{u v : Tm Δ A}
       → (Id A u v) [ σ ]t ≡ Id (A [ σ ]T) (u [ σ ]t) (v [ σ ]t)
Id[] = refl

idp[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Tms Γ Δ}{l}{A : Ty Δ l}{a : Tm Δ A}
        → idp A a [ σ ]t ≡ idp (A [ σ ]T) (a [ σ ]t)
idp[] = refl

IdΣ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}(u v : Tm Γ (Σ' A B))
    → let pr₁u = pr₁' A B u
          pr₁v = pr₁' A B v
          pr₂u = pr₂' A B u
          pr₂v = pr₂' A B v
          Id₁ = Id A pr₁u pr₁v
          wkId₁ : Tms (Γ ▷ ElP Id₁) Γ
          wkId₁ = wk' (ElP Id₁)
          transp = recId (A [ wkId₁ ]T) (pr₁u [ wkId₁ ]t) (B [ wk1 (ElP Id₁) A ]T) {pr₁v [ wkId₁ ]t} (vz' (ElP Id₁)) (pr₂u [ wkId₁ ]t)
          Id₂ : Tm (Γ ▷ ElP Id₁) (P k)
          Id₂ = Id (B [ <> A pr₁v ∘ wkId₁ ]T) transp (pr₂v [ wkId₁ ]t) in
      Id (Σ' A B) u v ≡ ΣP Id₁ Id₂
IdΣ u v = refl


coe : ∀{i}{Γ : Con i}{j}{a a' : Tm Γ (P j)} → a' ≡ a → Tm Γ (ElP a) → Tm Γ (ElP a')
coe refl x = x

unpack : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k) → Tms (Γ ▷ Σ' A B) (Γ ▷ A ▷ B)
unpack A B = ,' (,' (wk' (Σ' A B)) A (pr₁' (A [ wk' (Σ' A B) ]T) (B [ wk1 (Σ' A B) A ]T) (vz' (Σ' A B))))
                                   B (pr₂' (A [ wk' (Σ' A B) ]T) (B [ wk1 (Σ' A B) A ]T) (vz' (Σ' A B)))

recIdΣ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{C : Ty (Γ ▷ A ▷ B) l}(u v : Tm Γ A)
          (e : Tm Γ (ElP (Id A u v)))(p : Tm Γ ((Σ' B C) [ <> A u ]T) )
          → let Id' = Σ' B C
                Bv = B [ <> A v ]T
                Cv = C [ (<> A v) ^ B ]T
                Bu = B [ <> A u ]T
                Cu = C [ (<> A u) ^ B ]T
                pr₁p = pr₁' Bu Cu p
                pr₂p = pr₂' Bu Cu p
                trans₁ = recId A u B {v} e pr₁p
                upr₁p = mkΣ' A B u pr₁p
                vtrans₁ = mkΣ' A B v trans₁
                wkIduv = wk' (ElP (Id A u v))
                eidp = _,P_ {a = Id A u v}
                            {b = Id (Bv [ wkIduv ]T)
                                    (recId (A [ wkIduv ]T) (u [ wkIduv ]t) (B [ wk1 (ElP (Id A u v)) A ]T) {v [ wkIduv ]t} (vz' (ElP (Id A u v))) (pr₁p [ wkIduv ]t))
                                    (trans₁ [ wkIduv ]t)}
                                    e (idp Bv trans₁)
                trans₂ = recId (Σ' A B) upr₁p (C [ unpack A B ]T) {vtrans₁} (coe (IdΣ {A = A}{B = B} upr₁p vtrans₁) eidp) pr₂p
            in recId A u Id' {v} e p ≡ (mkΣ' Bv Cv trans₁ trans₂)
recIdΣ u v e p = refl



IdΠ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}(f g : Tm Γ (Π A B))
    → let A' = A [ wk' A ]T
          A'' = A' [ wk' A' ]T
          x₀ = vs' A' (vz' A)
          x₁ = vz' A'
          Idx₀x₁ = Id A'' x₀ x₁
          wk2 = wk' A ∘ wk' A'
          wk3 = wk2 ∘ wk' (ElP Idx₀x₁)
          Bx₁ = B [ ,' wk2 A x₁ ∘ (wk' (ElP Idx₀x₁)) ]T
          fx₀ = oldapp (A [ wk3 ]T) (B [ wk3 ^ A ]T) (f [ wk3 ]t) (x₀ [ wk' (ElP Idx₀x₁) ]t)
          gx₁ = oldapp (A [ wk3 ]T) (B [ wk3 ^ A ]T) (g [ wk3 ]t) (x₁ [ wk' (ElP Idx₀x₁) ]t)
          transpfx₀ = recId (A [ wk3 ]T) (x₀ [ wk' (ElP Idx₀x₁) ]t) ( B [ ,' (wk3 ∘ wk' (A [ wk3 ]T)) A (vz' (A [ wk3 ]T)) ]T) {x₁ [ wk' (ElP Idx₀x₁) ]t} (vz' (ElP Idx₀x₁)) fx₀
      in Id (Π A B) f g ≡ πsp A (πsp A' (πpp Idx₀x₁ (Id Bx₁ transpfx₀ gx₁)))
IdΠ u v = refl
