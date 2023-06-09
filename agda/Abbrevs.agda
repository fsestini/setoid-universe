{-# OPTIONS --without-K --prop #-}

module Abbrevs where

open import Agda.Primitive
open import lib using (_≡_; refl)

open import Setoid.CwF

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

open import Setoid.Pi

infixr 1 _⇒_ _⇛_ --   \r=   and \r==
_⇛_ = Π
_⇒_ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty Γ k) → Ty Γ (j ⊔ k)
A ⇒ B = A ⇛ (B [ wk {A = A} ]T)

oldapp : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k)(t : Tm Γ (Π A B))(u : Tm Γ A) → Tm Γ (B [ < u > ]T)
oldapp A B t u = (app {A = A}{B = B} t) [ < u > ]t

open import Setoid.Sigma

_×'_ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty Γ k) → Ty Γ (j ⊔ k)
A ×' B = Σ' A (B [ wk {A = A} ]T)
infixl 5 _×'_

open import Setoid.Props

open import Setoid.Pi

_⇒P_ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(b : Tm Γ (P k)) → Tm Γ (P (j ⊔ k))
A ⇒P b = ΠP A (b [ wk {A = A} ]t)
infixl 5 _⇒P_

open import Setoid.Sigma

_×P_ : ∀{i}{Γ : Con i}{j}(a : Tm Γ (P j)){k}(b : Tm Γ (P k)) → Tm Γ (P (j ⊔ k))
a ×P b = ΣP a (b [ wk {A = ElP a} ]t)
infixl 5 _×P_

open import Setoid.SeTT

open import Setoid.Id

module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(a a' : Tm Γ A) where

  toId : Tm (Γ ▷ ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')) (Id A a [ id ,⟨ A ⟩ a' ]T [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]T)
  toId = coeT'
    (Id A a [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ^ A ]T)
    {σ₀ = _,_ id {A = A [ wk  {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]T} (a  [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]t)}
    {σ₁ = _,_ id {A = A [ wk  {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]T} (a' [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]t)}
    ( _,'_
      {A = A [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]T}
      {σ₀ = id}
      {id}
      (RC (Γ ▷ ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')) id)
      {t₀ = a  [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]t}
      {t₁ = a' [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]t}
      (vz {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')}) )
    (idp A a [ wk {A = ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a')} ]t)

  fromId : Tm (Γ ▷ Id A a [ id ,⟨ A ⟩ a' ]T) (ElP ((_~T A {σ₀ = id}{id}) (RC Γ id) a a') [ wk {A = Id A a [ id ,⟨ A ⟩ a' ]T} ]T)
  fromId = recId A a (ElP ((_~T A {σ₀ = wk {A = A}}{wk {A = A}}) (RC Γ (wk {A = A})) (a [ wk {A = A} ]t) (vz {A = A}))) (RT A {σ = id} a)
    [ wk {A = Id A a [ id ,⟨ A ⟩ a' ]T} ,⟨ A ⟩ a' [ wk {A = Id A a [ id ,⟨ A ⟩ a' ]T} ]t ,⟨ Id A a ⟩ vz {A = Id A a [ id {Γ = Γ} ,⟨ A ⟩ a' ]T} ]t

