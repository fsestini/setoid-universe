{-# OPTIONS --without-K --prop #-}

module Setoid.Sets1.lib where

open import Setoid.lib

-- Sets1

data in-Uₚ : Set → Set₁
data in-U~ₚ : {A₀ A₁ : Set}(A₀₁ : A₀ → A₁ → Prop) → Set₁

data in-Uₚ where
  boolₚ : in-Uₚ 𝟚
  πₚ :
    {A : Set}(aₚ : in-Uₚ A){A~ : A → A → Prop}(a~ₚ : in-U~ₚ A~)
    {B : A → Set}(bₚ : (x : A) → in-Uₚ (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ₚ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₚ (B~ x₀₁)) → 
    in-Uₚ (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁)))

data in-U~ₚ where
  bool~ₚ : in-U~ₚ λ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
  π~ₚ :
    {A₀ : Set}(a₀ : in-Uₚ A₀){A₀~ : A₀ → A₀ → Prop}(a₀~ : in-U~ₚ A₀~)
    {A₁ : Set}(a₁ : in-Uₚ A₁){A₁~ : A₁ → A₁ → Prop}(a₁~ : in-U~ₚ A₁~)
    {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ₚ A₀₁)

    {B₀ : A₀ → Set}(b₀ : (x : A₀) → in-Uₚ (B₀ x))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      (b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ₚ (B₀~ x₀₁))
    {B₁ : A₁ → Set}(b₁ : (x : A₁) → in-Uₚ (B₁ x))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      (b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ₚ (B₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₚ (B₀₁ x₀₁)) → 
     
    in-U~ₚ
      {Σsp ((x : A₀) → B₀ x) (λ f → (x₀ x₁ : A₀)(x₀₁ : A₀~ x₀ x₁) → B₀~ x₀₁ (f x₀) (f x₁))}
      {Σsp ((x : A₁) → B₁ x) (λ f → (x₀ x₁ : A₁)(x₀₁ : A₁~ x₀ x₁) → B₁~ x₀₁ (f x₀) (f x₁))}
      (λ f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : A₀₁ x₀ x₁) → B₀₁ x₀₁ (proj₁sp f₀ x₀) (proj₁sp f₁ x₁))

data in-Uₜ : {A : Set} → in-Uₚ A → Prop₁
data in-U~ₜ : {A₀ A₁ : Set}(a₀ : in-Uₚ A₀)(a₁ : in-Uₚ A₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ₚ A₀₁ → Prop₁

data in-Uₜ where
  boolₜ : in-Uₜ boolₚ
  πₜ :
    {A : Set}{aₚ : in-Uₚ A}(a : in-Uₜ aₚ){A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}(a~ : in-U~ₜ aₚ aₚ a~ₚ)
    {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}(b : (x : A) → in-Uₜ (bₚ x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ₚ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₚ (B~ x₀₁)} →
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)) →
    in-Uₜ (πₚ aₚ a~ₚ bₚ b~ₚ)

data in-U~ₜ where
  bool~ₜ : in-U~ₜ boolₚ boolₚ bool~ₚ
  π~ₜ :
    {A₀ : Set}{a₀ₚ : in-Uₚ A₀}(a₀ : in-Uₜ a₀ₚ){A₀~ : A₀ → A₀ → Prop}{a₀~ₚ : in-U~ₚ A₀~}(a₀~ : in-U~ₜ a₀ₚ a₀ₚ a₀~ₚ)
    {A₁ : Set}{a₁ₚ : in-Uₚ A₁}(a₁ : in-Uₜ a₁ₚ){A₁~ : A₁ → A₁ → Prop}{a₁~ₚ : in-U~ₚ A₁~}(a₁~ : in-U~ₜ a₁ₚ a₁ₚ a₁~ₚ)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ₚ : in-U~ₚ A₀₁}(a₀₁ : in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ)
    {B₀ : A₀ → Set}{b₀ₚ : (x : A₀) → in-Uₚ (B₀ x)}(b₀ : (x : A₀) → in-Uₜ (b₀ₚ x))
    {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
    {b₀~ₚ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ₚ (B₀~ x₀₁)}
    (b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁))
    {B₁ : A₁ → Set}{b₁ₚ : (x : A₁) → in-Uₚ (B₁ x)}(b₁ : (x : A₁) → in-Uₜ (b₁ₚ x))
    {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
    {b₁~ₚ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ₚ (B₁~ x₀₁)}
    (b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ₜ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ₚ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₚ  (B₀₁ x₀₁)}
    (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)) →
    in-U~ₜ (πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ) (πₚ a₁ₚ a₁~ₚ b₁ₚ b₁~ₚ)
      (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ)
{-
proj₁-in-Uₜ-π :
  {A : Set}{aₚ : in-Uₚ A}{A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}
  {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}
  {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
  {b~ₚ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₚ (B~ x₀₁)}
  {C : Set}{cₚ : in-Uₚ C}(cₜ : in-Uₜ cₚ)
  (e : C ≡ (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁))))
  (e' : transport in-Uₚ e cₚ ≡ πₚ aₚ a~ₚ bₚ b~ₚ) →
  in-Uₜ aₚ
proj₁-in-Uₜ-π boolₜ e e' = {!c!}
proj₁-in-Uₜ-π (πₜ a a~ b b~) e e' = {!!}
-}
{-
ind-in-Uₜ :
  ∀{i}{C : Prop i}
  {A : Set}{aₚ : in-Uₚ A}{A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}
  {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}
  {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}{b~ₚ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₚ (B~ x₀₁)} →
  ((a : in-Uₜ aₚ)(a~ : in-U~ₜ aₚ aₚ a~ₚ)(b : (x : A) → in-Uₜ (bₚ x))(b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)) → C) →
  in-Uₜ (πₚ aₚ a~ₚ bₚ b~ₚ) → C
ind-in-Uₜ f w = {!w!} -- f a a~ b b~  -- (πₜ a a~ b b~)
-}




in-U : Set → Set₁
in-U A = Σsp (in-Uₚ A) in-Uₜ

in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁
in-U~ {A₀}{A₁} a₀ a₁ A₀₁ = Σsp (in-U~ₚ A₀₁) (in-U~ₜ (proj₁sp a₀) (proj₁sp a₁))

bool : in-U 𝟚
bool = boolₚ ,sp boolₜ

π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
    in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁)))
π {A} a {A~} a~ {B} b {B~} b~ = _,sp_
  (πₚ (proj₁sp a) (proj₁sp a~) (λ x → proj₁sp (b x)) (λ x₀₁ → proj₁sp (b~ x₀₁)))
  (πₜ (proj₂sp a) (proj₂sp a~) (λ x → proj₂sp (b x)) (λ x₀₁ → proj₂sp (b~ x₀₁)))

bool~ : in-U~ bool bool λ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
bool~ = bool~ₚ ,sp bool~ₜ

π~ :
  {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
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
        (λ f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : A₀₁ x₀ x₁) → B₀₁ x₀₁ (proj₁sp f₀ x₀) (proj₁sp f₁ x₁))
π~ {A₀}{a₀}{A₀~}{a₀~}{A₁}{a₁}{A₁~}{a₁~}{A₀₁}(a₀₁){B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{B₀₁} b₀₁ =
  π~ₚ (proj₁sp a₀) (proj₁sp a₀~) (proj₁sp a₁) (proj₁sp a₁~) (proj₁sp a₀₁) (λ x → proj₁sp (b₀ x)) (λ x₀₁ → proj₁sp (b₀~ x₀₁)) (λ x → proj₁sp (b₁ x)) (λ x₀₁ → proj₁sp (b₁~ x₀₁)) (λ x₀₁ → proj₁sp (b₀₁ x₀₁)) ,sp
  π~ₜ (proj₂sp a₀) (proj₂sp a₀~) (proj₂sp a₁) (proj₂sp a₁~) (proj₂sp a₀₁) (λ x → proj₂sp (b₀ x)) (λ x₀₁ → proj₂sp (b₀~ x₀₁)) (λ x → proj₂sp (b₁ x)) (λ x₀₁ → proj₂sp (b₁~ x₀₁)) (λ x₀₁ → proj₂sp (b₀₁ x₀₁))

-- simple eliminator targetting propositions

module simple
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Prop i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Prop j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ {a₀ = a}{a₁ = a} a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ {a₀ = b x₀}{a₁ = b x₁}(b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ {a₀ = bool}{a₁ = bool} bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₀} a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ {a₀ = a₁}{a₁ = a₁} a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₀ x₁} (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ {a₀ = b₁ x₀}{a₁ = b₁ x₁} (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₁ x₁} (b₀₁ x₀₁)) → 
    in-U~ᴰ {a₀ = π a₀ a₀~ b₀ b₀~}{a₁ = π a₁ a₁~ b₁ b₁~} (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁))
  where

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U (aₚ ,Σ mk↑ps boolₜ) = boolᴰ
  ind-in-U (aₚ ,Σ mk↑ps (πₜ a a~ b b~)) =
    πᴰ (ind-in-U (_ ,Σ mk↑ps a)) (ind-in-U~ (_ ,Σ mk↑ps a~)) (λ x → ind-in-U (_ ,Σ mk↑ps (b x))) (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b~ x₀₁)))
  ind-in-U~ (aₚ ,Σ mk↑ps bool~ₜ) = bool~ᴰ
  ind-in-U~ (aₚ ,Σ mk↑ps (π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) = π~ᴰ
    (ind-in-U  (_ ,Σ mk↑ps a₀))
    (ind-in-U~ (_ ,Σ mk↑ps a₀~))
    (ind-in-U  (_ ,Σ mk↑ps a₁))
    (ind-in-U~ (_ ,Σ mk↑ps a₁~))
    (ind-in-U~ (_ ,Σ mk↑ps a₀₁))
    (λ x → ind-in-U    (_ ,Σ mk↑ps (b₀ x)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₀~ x₀₁)))
    (λ x → ind-in-U    (_ ,Σ mk↑ps (b₁ x)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₁~ x₀₁)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₀₁ x₀₁)))

-- simple eliminator targetting sets

module _
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Set j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ {a₀ = a}{a₁ = a} a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ {a₀ = b x₀}{a₁ = b x₁}(b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ {a₀ = bool}{a₁ = bool} bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₀} a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ {a₀ = a₁}{a₁ = a₁} a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₀ x₁} (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ {a₀ = b₁ x₀}{a₁ = b₁ x₁} (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₁ x₁} (b₀₁ x₀₁)) → 
    in-U~ᴰ {a₀ = π a₀ a₀~ b₀ b₀~}{a₁ = π a₁ a₁~ b₁ b₁~} (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁))
  where
{-
  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U (aₚ ,Σ mk↑ps boolₜ) = boolᴰ
  ind-in-U (aₚ ,Σ mk↑ps (πₜ a a~ b b~)) =
    πᴰ (ind-in-U (_ ,Σ mk↑ps a)) (ind-in-U~ (_ ,Σ mk↑ps a~)) (λ x → ind-in-U (_ ,Σ mk↑ps (b x))) (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b~ x₀₁)))
  ind-in-U~ (aₚ ,Σ mk↑ps bool~ₜ) = bool~ᴰ
  ind-in-U~ (aₚ ,Σ mk↑ps (π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) = π~ᴰ
    (ind-in-U  (_ ,Σ mk↑ps a₀))
    (ind-in-U~ (_ ,Σ mk↑ps a₀~))
    (ind-in-U  (_ ,Σ mk↑ps a₁))
    (ind-in-U~ (_ ,Σ mk↑ps a₁~))
    (ind-in-U~ (_ ,Σ mk↑ps a₀₁))
    (λ x → ind-in-U    (_ ,Σ mk↑ps (b₀ x)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₀~ x₀₁)))
    (λ x → ind-in-U    (_ ,Σ mk↑ps (b₁ x)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₁~ x₀₁)))
    (λ x₀₁ → ind-in-U~ (_ ,Σ mk↑ps (b₀₁ x₀₁)))

-}
