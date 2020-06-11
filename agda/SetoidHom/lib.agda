{-# OPTIONS --without-K --prop #-}

module SetoidHom.lib where

-- it is not allowed to open this module outside of Setoid

open import Agda.Primitive

-- CwF

record Setoid i : Set (lsuc i) where
  field
    ∣_∣C : Set i
    _⊢_~_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _⊢_~_ γ γ
    symC : ∀{γ γ'} → _⊢_~_ γ γ' → _⊢_~_ γ' γ
    transC : ∀{γ γ' γ''} → _⊢_~_ γ γ' → _⊢_~_ γ' γ'' → _⊢_~_ γ γ''
  infix 4 ∣_∣C
  infix 5 _⊢_~_
open Setoid public

record SetoidMor {i j}(Γ : Setoid i)(Δ : Setoid j) : Set (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ~s   : {γ γ' : ∣ Γ ∣C} → Γ ⊢ γ ~ γ' → Δ ⊢ (∣_∣s γ) ~ (∣_∣s γ')
  infix 4 ∣_∣s
open SetoidMor public

record SetoidFam {i}(Γ : Setoid i) j : Set (i ⊔ lsuc j) where
  constructor mkTy
  field
    EL          : ∣ Γ ∣C → Setoid j
    subst       : {γ γ' : ∣ Γ ∣C}(γ~ : Γ ⊢ γ ~ γ') → SetoidMor (EL γ) (EL γ')
    subst-ref   : {γ : ∣ Γ ∣C}(x : ∣ EL γ ∣C) → EL γ ⊢ ∣ subst (refC Γ γ) ∣s x ~ x
    subst-trans : {γ γ' γ'' : ∣ Γ ∣C}(γ~ : Γ ⊢ γ ~ γ')(γ~' : Γ ⊢ γ' ~ γ'')(x : ∣ EL γ ∣C) →
      EL γ'' ⊢ ∣ subst (transC Γ γ~ γ~') ∣s x ~ ∣ subst γ~' ∣s (∣ subst γ~ ∣s x)

open SetoidFam public

record SetoidSec {i}(Γ : Setoid i){j}(A : SetoidFam Γ j) : Set (i ⊔ j) where
  field
    ∣_∣t : (γ : ∣ Γ ∣C) → ∣ EL A γ ∣C
    ~t   : {γ γ' : ∣ Γ ∣C}(γ~ : Γ ⊢ γ ~ γ') → EL A γ' ⊢ ∣ subst A γ~ ∣s (∣_∣t γ) ~ ∣_∣t γ'
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

record ↑pl {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor mk↑pl
  field
    un↑pl : A
open ↑pl public

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

-- SeTT

record SetoidMor~ {i}(Γ : Setoid i){j}{Ω : Setoid j}(σ₀ σ₁ : SetoidMor Ω Γ) : Prop (i ⊔ j) where
  field
    ∣_∣ :  (γ : ∣ Ω ∣C) →  Γ ⊢ ∣ σ₀ ∣s γ ~ ∣ σ₁ ∣s γ
open SetoidMor~ public

-- Sets

data in-U : Set → Set₁
data in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁

data in-U where
  bool : in-U 𝟚
  π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
      
      {B : A → Set}(b : (a : A) → in-U (B a))
      {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
      (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
      
      in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁)))

data in-U~ where
  bool~ : in-U~ bool bool λ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
  π~ : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
       {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
       {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)

       {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
         {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
         {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
       {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
         {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
         {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
       {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
       (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)) → 
        
       in-U~ (π a₀ a₀~ b₀ {B₀~} b₀~)
             (π a₁ a₁~ b₁ {B₁~} b₁~)
             (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : A₀₁ x₀ x₁) → B₀₁ x₀₁ (f₀ x₀) (f₁ x₁)})
