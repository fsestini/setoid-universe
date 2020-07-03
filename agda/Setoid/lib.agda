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

record ↑ps {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor mk↑ps
  field
    un↑ps : A
open ↑ps public

-- Empty

data ⊥ : Set where

⊥elim : ∀{ℓ}{A : Set ℓ} → ⊥ → A
⊥elim ()

⊥elimp : ∀{ℓ}{A : Prop ℓ} → ⊥ → A
⊥elimp ()

-- Props

record ↑pl {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor mk↑pl
  field
    un↑pl : A
open ↑pl public

data Tr {i}(A : Set i) : Prop i where
  tr : A → Tr A

untr : ∀{i j}{A : Set i}{B : Tr A → Prop j} → ((x : A) → B (tr x)) → (x : Tr A) → B x
untr f (tr x) = f x

data ⊥p : Prop where

⊤p : Prop
⊤p = Tr ⊤

ttp : ⊤p
ttp = tr tt

⊥pelim : ∀{ℓ}{A : Set ℓ} → ⊥p → A
⊥pelim ()
⊥pelimp : ∀{ℓ}{A : Prop ℓ} → ⊥p → A
⊥pelimp ()
-- Bool

data 𝟚 : Set where
  tt ff : 𝟚

if_then_else_ : ∀{ℓ}{C : 𝟚 → Set ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
if tt then c else d = c
if ff then c else d = d

pif_then_else_ : ∀{ℓ}{C : 𝟚 → Prop ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
pif tt then c else d = c
pif ff then c else d = d

_≟𝟚_ : 𝟚 → 𝟚 → Prop
x₀ ≟𝟚 x₁ = if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)

ref𝟚 : ∀ b → b ≟𝟚 b
ref𝟚 tt = ttp
ref𝟚 ff = ttp

sym𝟚 : ∀ {b₀ b₁} → b₀ ≟𝟚 b₁ → b₁ ≟𝟚 b₀
sym𝟚 {tt} {tt} _ = ttp
sym𝟚 {ff} {ff} _ = ttp

trans𝟚 : ∀ {b₀ b₁ b₂} → b₀ ≟𝟚 b₁ → b₁ ≟𝟚 b₂ → b₀ ≟𝟚 b₂
trans𝟚 {tt} {tt} {tt} _ _ = ttp
trans𝟚 {ff} {ff} {ff} _ _ = ttp


-- SeTT

record SetoidMor~ {i}(Γ : Setoid i){j}{Ω : Setoid j}(σ₀ σ₁ : SetoidMor Ω Γ) : Prop (i ⊔ j) where
  field
    ∣_∣ :  (γ : ∣ Ω ∣C) →  Γ C ∣ σ₀ ∣s γ ~ ∣ σ₁ ∣s γ
open SetoidMor~ public

-- Id

module _ {i}{Γ : Setoid i}{j}(A : SetoidFam Γ j)(a : SetoidSec Γ A) where

  open import lib

  data ∣Id∣ : {γ : ∣ Γ ∣C} → ∣ A ∣T γ → Set (i ⊔ j) where
    ∣idp∣  : {γ : ∣ Γ ∣C} → ∣Id∣ (∣ a ∣t γ)
    coeId : ∀{γ₀ γ₁}{γ₀₁ : Γ C γ₀ ~ γ₁}{α₀ α₁}(α₀₁ : A T γ₀₁ ⊢ α₀ ~ α₁)(p₀ : ∣Id∣ α₀) → ∣Id∣ α₁

  data Id~ : {γ₀ γ₁ : ∣ Γ ∣C}{γ₀₁ : Γ C γ₀ ~ γ₁}{α₀ : ∣ A ∣T γ₀}{α₁ : ∣ A ∣T γ₁} → A T γ₀₁ ⊢ α₀ ~ α₁ → ∣Id∣ α₀ → ∣Id∣ α₁ → Prop (i ⊔ j) where
    idp~ : ∀{γ₀ γ₁}{γ₀₁ : Γ C γ₀ ~ γ₁} → Id~ (~t a γ₀₁) ∣idp∣ ∣idp∣
    refId : ∀{γ}{α : ∣ A ∣T γ} p → Id~ (refT A α) p p
    symId : ∀{γ₀ γ₁}{γ₀₁ : Γ C γ₀ ~ γ₁}{α₀ α₁}{α₀₁ : A T γ₀₁ ⊢ α₀ ~ α₁}{p₀ p₁} → Id~ α₀₁ p₀ p₁ → Id~ (symT A α₀₁) p₁ p₀
    transId : ∀{γ₀ γ₁ γ₂}{γ₀₁ : Γ C γ₀ ~ γ₁}{γ₁₂ : Γ C γ₁ ~ γ₂}{α₀ α₁ α₂}{α₀₁ : A T γ₀₁ ⊢ α₀ ~ α₁}{α₁₂ : A T γ₁₂ ⊢ α₁ ~ α₂}{p₀ p₁ p₂} →
      Id~ α₀₁ p₀ p₁ → Id~ α₁₂ p₁ p₂ → Id~ (transT A α₀₁ α₁₂) p₀ p₂
    cohId : ∀{γ₀ γ₁}{γ₀₁ : Γ C γ₀ ~ γ₁}{α₀ α₁}(α₀₁ : A T γ₀₁ ⊢ α₀ ~ α₁)(p₀ : ∣Id∣ α₀) → Id~ α₀₁ p₀ (coeId α₀₁ p₀)

_↔_ : ∀{i j}(A : Prop i)(B : Prop j) → Prop (i ⊔ j)
A ↔ B = (A → B) ×p (B → A)
