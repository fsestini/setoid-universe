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
    → let pr₁u = pr₁ {A = A}{B = B} u
          pr₁v = pr₁ {A = A}{B = B} v
          pr₂u = pr₂ {A = A}{B = B} u
          pr₂v = pr₂ {A = A}{B = B} v
          Id₁ = Id A pr₁u pr₁v
          wkId₁ : Tms (Γ ▷ ElP Id₁) Γ
          wkId₁ = wk {A = ElP Id₁}
          transp = recId (A [ wkId₁ ]T) (pr₁u [ wkId₁ ]t) (B [ wk1 (ElP Id₁) A ]T) {pr₁v [ wkId₁ ]t} (vz {A = ElP Id₁}) (pr₂u [ wkId₁ ]t)
          Id₂ : Tm (Γ ▷ ElP Id₁) (P k)
          Id₂ = Id {Γ = Γ ▷ ElP Id₁} (B [ <_> {A = A} pr₁v ∘ wkId₁ ]T) transp (pr₂v [ wkId₁ ]t) in
      Id (Σ' A B) u v ≡ ΣP Id₁ Id₂
IdΣ u v = refl


coe : ∀{i}{Γ : Con i}{j}{a a' : Tm Γ (P j)} → a' ≡ a → Tm Γ (ElP a) → Tm Γ (ElP a')
coe refl x = x

recIdΣ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k}{l}{C : Ty (Γ ▷ A ▷ B) l}(u v : Tm Γ A)
          (e : Tm Γ (ElP (Id A u v)))(p : Tm Γ ((Σ' B C) [ _,_ id {A = A} u ]T) )
          → let Id' = Σ' B C
                Bv = B [ _,_ id {A = A} v ]T
                Cv = C [ (_,_ id {A = A} v) ^ B ]T
                Bu = B [ _,_ id {A = A} u ]T
                Cu = C [ (_,_ id {A = A} u) ^ B ]T
                pr₁p = pr₁ {A = Bu}{B = Cu} p
                pr₂p = pr₂ {A = Bu}{B = Cu} p
                unpack : Tms (Γ ▷ Σ' A B) (Γ ▷ A ▷ B)
                unpack = _,_ (_,_ (wk {A = Σ' A B}) {A = A} (pr₁ {A = A [ wk {A = Σ' A B} ]T} {B [ wk1 (Σ' A B) A ]T} (vz {A = Σ' A B})))
                                                    {A = B} (pr₂ {A = A [ wk {A = Σ' A B} ]T} {B [ wk1 (Σ' A B) A ]T} (vz {A = Σ' A B}))
                trans₁ = recId A u B {v} e pr₁p
                upr₁p = _,Σ'_ {A = A}{B} u pr₁p
                vtrans₁ = _,Σ'_ {A = A}{B} v trans₁
                trans₂ = recId (Σ' A B) upr₁p (C [ unpack ]T) {vtrans₁} (coe (IdΣ {A = A} {B = B} upr₁p vtrans₁) (_,P_
                                                                                                                    {a =
                                                                                                                     Id {i} {Γ} {j} A
                                                                                                                     (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                      (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                       (pr₁ {i} {k} {l} {Γ}
                                                                                                                        {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                         (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                        {_[_]T {i ⊔ k}
                                                                                                                         {_▷_ {i} Γ {k}
                                                                                                                          (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                           (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                         {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                         (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                          (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                        p)))
                                                                                                                     (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                      (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                       (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                        (pr₁ {i} {k} {l} {Γ}
                                                                                                                         {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                          (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                         {_[_]T {i ⊔ k}
                                                                                                                          {_▷_ {i} Γ {k}
                                                                                                                           (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                          {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                          (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                           (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                         p))))}
                                                                                                                    {Id {i ⊔ j}
                                                                                                                     {_▷_ {i} Γ {j}
                                                                                                                      (ElP {i} {Γ} {j}
                                                                                                                       (Id {i} {Γ} {j} A
                                                                                                                        (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                         (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                          (pr₁ {i} {k} {l} {Γ}
                                                                                                                           {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                           {_[_]T {i ⊔ k}
                                                                                                                            {_▷_ {i} Γ {k}
                                                                                                                             (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                            {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                            (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                           p)))
                                                                                                                        (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                         (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                          (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p))))))}
                                                                                                                     {k}
                                                                                                                     (_[_]T {i ⊔ j}
                                                                                                                      {_▷_ {i} Γ {j}
                                                                                                                       (ElP {i} {Γ} {j}
                                                                                                                        (Id {i} {Γ} {j} A
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                           (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p))))))}
                                                                                                                      {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                      (_∘_ {i ⊔ j}
                                                                                                                       {_▷_ {i} Γ {j}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))}
                                                                                                                       {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                       (<_> {i} {Γ} {j} {A}
                                                                                                                        (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                         (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                          (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))))
                                                                                                                       (wk {i} {Γ} {j}
                                                                                                                        {ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))))})))
                                                                                                                     (recId {i ⊔ j}
                                                                                                                      {_▷_ {i} Γ {j}
                                                                                                                       (ElP {i} {Γ} {j}
                                                                                                                        (Id {i} {Γ} {j} A
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                           (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p))))))}
                                                                                                                      {j}
                                                                                                                      (_[_]T {i ⊔ j}
                                                                                                                       {_▷_ {i} Γ {j}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))}
                                                                                                                       {i} {Γ} {j} A
                                                                                                                       (wk {i} {Γ} {j}
                                                                                                                        {ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))))}))
                                                                                                                      (_[_]t {i ⊔ j}
                                                                                                                       {_▷_ {i} Γ {j}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))}
                                                                                                                       {i} {Γ} {j} {A}
                                                                                                                       (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                        (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                         (pr₁ {i} {k} {l} {Γ}
                                                                                                                          {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                           (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                          {_[_]T {i ⊔ k}
                                                                                                                           {_▷_ {i} Γ {k}
                                                                                                                            (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                           {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                           (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                          p)))
                                                                                                                       (wk {i} {Γ} {j}
                                                                                                                        {ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))))}))
                                                                                                                      {k}
                                                                                                                      (_[_]T {i ⊔ j}
                                                                                                                       {_▷_ {i ⊔ j}
                                                                                                                        (_▷_ {i} Γ {j}
                                                                                                                         (ElP {i} {Γ} {j}
                                                                                                                          (Id {i} {Γ} {j} A
                                                                                                                           (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                            (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))
                                                                                                                           (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                            (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                             (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                              (pr₁ {i} {k} {l} {Γ}
                                                                                                                               {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                               {_[_]T {i ⊔ k}
                                                                                                                                {_▷_ {i} Γ {k}
                                                                                                                                 (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                  (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                                {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                                (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                               p)))))))
                                                                                                                        {j}
                                                                                                                        (_[_]T {i ⊔ j}
                                                                                                                         {_▷_ {i} Γ {j}
                                                                                                                          (ElP {i} {Γ} {j}
                                                                                                                           (Id {i} {Γ} {j} A
                                                                                                                            (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                             (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                              (pr₁ {i} {k} {l} {Γ}
                                                                                                                               {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                               {_[_]T {i ⊔ k}
                                                                                                                                {_▷_ {i} Γ {k}
                                                                                                                                 (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                  (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                                {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                                (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                               p)))
                                                                                                                            (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                             (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                              (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                               (pr₁ {i} {k} {l} {Γ}
                                                                                                                                {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                                {_[_]T {i ⊔ k}
                                                                                                                                 {_▷_ {i} Γ {k}
                                                                                                                                  (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                   (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                                 {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                                 (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                  (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                                p))))))}
                                                                                                                         {i} {Γ} {j} A
                                                                                                                         (wk {i} {Γ} {j}
                                                                                                                          {ElP {i} {Γ} {j}
                                                                                                                           (Id {i} {Γ} {j} A
                                                                                                                            (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                             (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                              (pr₁ {i} {k} {l} {Γ}
                                                                                                                               {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                               {_[_]T {i ⊔ k}
                                                                                                                                {_▷_ {i} Γ {k}
                                                                                                                                 (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                  (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                                {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                                (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                               p)))
                                                                                                                            (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                             (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                              (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                               (pr₁ {i} {k} {l} {Γ}
                                                                                                                                {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                                {_[_]T {i ⊔ k}
                                                                                                                                 {_▷_ {i} Γ {k}
                                                                                                                                  (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                   (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                                 {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                                 (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                  (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                                p)))))}))}
                                                                                                                       {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                       (wk1 {i} {j} {j} {Γ}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))
                                                                                                                        A))
                                                                                                                      {_[_]t {i ⊔ j}
                                                                                                                       {_▷_ {i} Γ {j}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))}
                                                                                                                       {i} {Γ} {j} {A}
                                                                                                                       (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                        (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                         (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                          (pr₁ {i} {k} {l} {Γ}
                                                                                                                           {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                           {_[_]T {i ⊔ k}
                                                                                                                            {_▷_ {i} Γ {k}
                                                                                                                             (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                            {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                            (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                           p))))
                                                                                                                       (wk {i} {Γ} {j}
                                                                                                                        {ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))))})}
                                                                                                                      (vz {i} {Γ} {j}
                                                                                                                       {ElP {i} {Γ} {j}
                                                                                                                        (Id {i} {Γ} {j} A
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                           (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))))})
                                                                                                                      (_[_]t {i ⊔ j}
                                                                                                                       {_▷_ {i} Γ {j}
                                                                                                                        (ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p))))))}
                                                                                                                       {i} {Γ} {k}
                                                                                                                       {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                        (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A}
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p))))}
                                                                                                                       (pr₂ {i} {j} {k} {Γ} {A} {B}
                                                                                                                        (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                         (pr₁ {i} {k} {l} {Γ}
                                                                                                                          {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                           (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                          {_[_]T {i ⊔ k}
                                                                                                                           {_▷_ {i} Γ {k}
                                                                                                                            (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                           {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                           (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                          p)))
                                                                                                                       (wk {i} {Γ} {j}
                                                                                                                        {ElP {i} {Γ} {j}
                                                                                                                         (Id {i} {Γ} {j} A
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))
                                                                                                                          (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                           (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                            (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                             (pr₁ {i} {k} {l} {Γ}
                                                                                                                              {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                              {_[_]T {i ⊔ k}
                                                                                                                               {_▷_ {i} Γ {k}
                                                                                                                                (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                 (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                               {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                               (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                              p)))))})))
                                                                                                                     (_[_]t {i ⊔ j}
                                                                                                                      {_▷_ {i} Γ {j}
                                                                                                                       (ElP {i} {Γ} {j}
                                                                                                                        (Id {i} {Γ} {j} A
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                           (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p))))))}
                                                                                                                      {i} {Γ} {k}
                                                                                                                      {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                       (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A}
                                                                                                                        (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                         (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                          (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))))}
                                                                                                                      (pr₂ {i} {j} {k} {Γ} {A} {B}
                                                                                                                       (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                        (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                         (pr₁ {i} {k} {l} {Γ}
                                                                                                                          {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                           (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                          {_[_]T {i ⊔ k}
                                                                                                                           {_▷_ {i} Γ {k}
                                                                                                                            (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                           {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                           (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                            (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                          p))))
                                                                                                                      (wk {i} {Γ} {j}
                                                                                                                       {ElP {i} {Γ} {j}
                                                                                                                        (Id {i} {Γ} {j} A
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} u
                                                                                                                           (pr₁ {i} {k} {l} {Γ}
                                                                                                                            {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                             (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                            {_[_]T {i ⊔ k}
                                                                                                                             {_▷_ {i} Γ {k}
                                                                                                                              (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                             {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                             (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                            p)))
                                                                                                                         (pr₁ {i} {j} {k} {Γ} {A} {B}
                                                                                                                          (_,Σ'_ {i} {j} {k} {Γ} {A} {B} v
                                                                                                                           (recId {i} {Γ} {j} A u {k} B {v} e
                                                                                                                            (pr₁ {i} {k} {l} {Γ}
                                                                                                                             {_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                              (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u)}
                                                                                                                             {_[_]T {i ⊔ k}
                                                                                                                              {_▷_ {i} Γ {k}
                                                                                                                               (_[_]T {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A} {k} B
                                                                                                                                (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u))}
                                                                                                                              {i ⊔ j ⊔ k} {_▷_ {i ⊔ j} (_▷_ {i} Γ {j} A) {k} B} {l} C
                                                                                                                              (_^_ {i} {Γ} {i ⊔ j} {_▷_ {i} Γ {j} A}
                                                                                                                               (_,_ {i} {Γ} {i} {Γ} (id {i} {Γ}) {j} {A} u) {k} B)}
                                                                                                                             p)))))}))}
                                                                                                                    e (idp (B [ <_> v ]T) trans₁))) pr₂p
            in recId A u Id' {v} e p ≡ (_,Σ'_ {A = Bv}{Cv} trans₁ trans₂)
recIdΣ u v e p = refl
