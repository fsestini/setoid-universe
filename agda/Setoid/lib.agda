{-# OPTIONS --without-K --prop #-}

module Setoid.lib where

-- it is not allowed to open this module outside of Setoid

open import Agda.Primitive

-- CwF

record Setoid i : Set (lsuc i) where
  field
    ∣_∣C : Set i
    _C_~_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _C_~_ γ γ
    symC : ∀{γ γ'} → _C_~_ γ γ' → _C_~_ γ' γ
    transC : ∀{γ γ' γ''} → _C_~_ γ γ' → _C_~_ γ' γ'' → _C_~_ γ γ''
  infix 4 ∣_∣C
  infix 5 _C_~_
open Setoid public

record SetoidMor {i j}(Γ : Setoid i)(Δ : Setoid j) : Set (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ~s   : {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → Δ C (∣_∣s γ) ~ (∣_∣s γ')
  infix 4 ∣_∣s
open SetoidMor public

record SetoidFam {i}(Γ : Setoid i) j : Set (i ⊔ lsuc j) where
  constructor mkTy
  field
    ∣_∣T_   : ∣ Γ ∣C → Set j
    _T_⊢_~_ : ∀{γ γ'}(p : Γ C γ ~ γ') → ∣_∣T_ γ → ∣_∣T_ γ' → Prop j
    refT    : ∀{γ} α → _T_⊢_~_ (refC Γ γ) α α
    symT    : ∀{γ γ'}{p : Γ C γ ~ γ'}{α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}
            → _T_⊢_~_ p α α' → _T_⊢_~_ (symC Γ p) α' α
    transT  : ∀{γ γ' γ''}{p : Γ C γ ~ γ'}{q : Γ C γ' ~ γ''}
              {α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}{α'' : ∣_∣T_ γ''}
            → _T_⊢_~_ p α α' → _T_⊢_~_ q α' α'' → _T_⊢_~_ (transC Γ p q) α α''
    coeT    : {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → ∣_∣T_ γ → ∣_∣T_ γ'
    cohT    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ')(α : ∣_∣T_ γ) → _T_⊢_~_ p α (coeT p α)
  infix 4 ∣_∣T_
  infix 5 _T_⊢_~_
open SetoidFam public

record SetoidSec {i}(Γ : Setoid i){j}(A : SetoidFam Γ j) : Set (i ⊔ j) where
  field
    ∣_∣t : (γ : ∣ Γ ∣C) → ∣ A ∣T γ
    ~t   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ') → A T p ⊢ (∣_∣t γ) ~ (∣_∣t γ')
  infix 4 ∣_∣t
open SetoidSec public

record ⊤  : Set  where constructor tt

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,Σ_
  field
    proj₁ : A
    proj₂ : B proj₁
infixl 5 _,Σ_
_×_ : ∀{ℓ ℓ'} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A λ _ → B
infixl 4 _×_

open Σ public
record Σp {ℓ ℓ'} (A : Prop ℓ) (B : A → Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  constructor _,p_
  field
    proj₁p : A
    proj₂p : B proj₁p
infixl 5 _,p_
open Σp public
_×p_ : ∀{ℓ ℓ'} → Prop ℓ → Prop ℓ' → Prop (ℓ ⊔ ℓ')
A ×p B = Σp A λ _ → B
infixl 4 _×p_

-- Pi

record Σsp {ℓ ℓ'} (A : Set ℓ) (B : A → Prop ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,sp_
  field
    proj₁sp : A
    proj₂sp : B proj₁sp
infixl 5 _,sp_
open Σsp public

record Liftp {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor liftp
  field
    unliftp : A
open Liftp public

-- Empty

data ⊥ : Set where

⊥elim : ∀{ℓ}{A : Set ℓ} → ⊥ → A
⊥elim ()

⊥elimp : ∀{ℓ}{A : Prop ℓ} → ⊥ → A
⊥elimp ()

-- Bool

data ⊥p : Prop where

data 𝟚 : Set where
  tt ff : 𝟚

if_then_else_ : ∀{ℓ}{C : 𝟚 → Set ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
if tt then c else d = c
if ff then c else d = d

pif_then_else_ : ∀{ℓ}{C : 𝟚 → Prop ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
pif tt then c else d = c
pif ff then c else d = d

-- Props

record LiftP {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor liftP
  field
    unliftP : A
open LiftP public

data Tr {i}(A : Set i) : Prop i where
  tr : A → Tr A

untr : ∀{i j}{A : Set i}{B : Tr A → Prop j} → ((x : A) → B (tr x)) → (x : Tr A) → B x
untr f (tr x) = f x

⊤p : Prop
⊤p = Tr ⊤

ttp : ⊤p
ttp = tr tt

⊥pelim : ∀{ℓ}{A : Set ℓ} → ⊥p → A
⊥pelim ()
⊥pelimp : ∀{ℓ}{A : Prop ℓ} → ⊥p → A
⊥pelimp ()
