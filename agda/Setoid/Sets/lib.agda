{-# OPTIONS --without-K --prop #-}

module Setoid.Sets.lib where

-- constructing in-U and in-U~ using preterms and a typing relation

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
    in-Uₚ (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))

data in-U~ₚ where
  bool~ₚ : in-U~ₚ λ x₀ x₁ → x₀ ≟𝟚 x₁
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
      {Σsp ((x : A₀) → B₀ x) (λ f → (x₀ x₁ : A₀)(x₀₁ : ↑ps (A₀~ x₀ x₁)) → B₀~ (un↑ps x₀₁) (f x₀) (f x₁))}
      {Σsp ((x : A₁) → B₁ x) (λ f → (x₀ x₁ : A₁)(x₀₁ : ↑ps (A₁~ x₀ x₁)) → B₁~ (un↑ps x₀₁) (f x₀) (f x₁))}
      (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (A₀₁ x₀ x₁)) → B₀₁ (un↑ps x₀₁) (f₀ x₀) (f₁ x₁)})

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
    {b₀₁ₚ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₚ (B₀₁ x₀₁)}
    (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)) →
    in-U~ₜ (πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ) (πₚ a₁ₚ a₁~ₚ b₁ₚ b₁~ₚ)
      (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ)

in-U : Set → Set₁
in-U A = Σsp (in-Uₚ A) in-Uₜ

in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁
in-U~ {A₀}{A₁}(a₀ₚ ,sp a₀)(a₁ₚ ,sp a₁) A₀₁ = Σsp (in-U~ₚ A₀₁) (in-U~ₜ a₀ₚ a₁ₚ)

bool : in-U 𝟚
bool = boolₚ ,sp boolₜ

π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
    in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))
    
π {A}(aₚ ,sp a){A~}(a~ₚ ,sp a~){B} b {B~} b~ =
  πₚ aₚ a~ₚ (λ x → proj₁sp (b x)) (λ x₀₁ → proj₁sp (b~ x₀₁)) ,sp
  πₜ a a~ (λ x → proj₂sp (b x)) (λ x₀₁ → proj₂sp (b~ x₀₁))

bool~ : in-U~ bool bool λ x₀ x₁ → x₀ ≟𝟚 x₁
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
        (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (A₀₁ x₀ x₁)) → B₀₁ (un↑ps x₀₁) (f₀ x₀) (f₁ x₁)})
π~ {A₀}{a₀ₚ ,sp a₀}{A₀~}{a₀~ₚ ,sp a₀~}{A₁}{a₁ₚ ,sp a₁}{A₁~}{a₁~ₚ ,sp a₁~}{A₀₁}(a₀₁ₚ ,sp a₀₁){B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{B₀₁} b₀₁ =
  π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ (λ x → proj₁sp (b₀ x)) (λ x₀₁ → proj₁sp (b₀~ x₀₁)) (λ x → proj₁sp (b₁ x)) (λ x₀₁ → proj₁sp (b₁~ x₀₁)) (λ x₀₁ → proj₁sp (b₀₁ x₀₁)) ,sp
  π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ (λ x → proj₂sp (b₀ x)) (λ x₀₁ → proj₂sp (b₀~ x₀₁)) (λ x → proj₂sp (b₁ x)) (λ x₀₁ → proj₂sp (b₁~ x₀₁)) (λ x₀₁ → proj₂sp (b₀₁ x₀₁))

-- simple eliminator targetting propositions

module simpleProp
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
  
  ind-in-U (boolₚ ,sp _) = boolᴰ
  ind-in-U (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp πₜ a a~ b b~) =
    πᴰ (ind-in-U (aₚ ,sp a)) (ind-in-U~ (a~ₚ ,sp a~)) (λ x → ind-in-U (bₚ x ,sp b x)) (λ x₀₁ → ind-in-U~ (b~ₚ x₀₁ ,sp b~ x₀₁))

  ind-in-U~ (bool~ₚ ,sp bool~ₜ) = bool~ᴰ
  ind-in-U~ (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁) =
    π~ᴰ (ind-in-U (a₀ₚ ,sp a₀)) (ind-in-U~ (a₀~ₚ ,sp a₀~)) (ind-in-U (a₁ₚ ,sp a₁)) (ind-in-U~ (a₁~ₚ ,sp a₁~)) (ind-in-U~ (a₀₁ₚ ,sp a₀₁))
    (λ x → ind-in-U (b₀ₚ x ,sp b₀ x)) (λ x₀₁ → ind-in-U~ (b₀~ₚ x₀₁ ,sp b₀~ x₀₁)) (λ x → ind-in-U (b₁ₚ x ,sp b₁ x)) (λ x₀₁ → ind-in-U~ (b₁~ₚ x₀₁ ,sp b₁~ x₀₁))
    λ x₀₁ → ind-in-U~ (b₀₁ₚ x₀₁ ,sp b₀₁ x₀₁)

-- simple eliminator targetting sets

open import Agda.Builtin.Equality

withProp : ∀{i j} {P : Prop i} {Q : Prop j} -> P -> (P -> Q) -> Q
withProp p f = f p

postulate
  _≡p_ : ∀{i} {A : Set i} -> A -> A -> Prop i
  reflp : ∀{i} {A : Set i} {a : A} -> a ≡p a
  transp-≡p : ∀{i j}{A : Set i} {x y : A} (P : A → Set j) → x ≡p y → P x → P y

to-≡ : ∀{i} {A : Set i} {x y : A} -> x ≡p y -> x ≡ y
to-≡ e = transp-≡p (λ y → _ ≡ y) e refl

module simple
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

  ind-in-U' : {A : Set} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> in-Uᴰ (aₚ ,sp aₜ)
  ind-in-U~' : {A₀ A₁ : Set} {A₀₁ : A₀ → A₁ → Prop} {a₀ : in-U A₀}{a₁ : in-U A₁}
               (a₀₁ₚ : in-U~ₚ A₀₁)
               (a₀₁ₜ : in-U~ₜ (proj₁sp a₀) (proj₁sp a₁) a₀₁ₚ)
             → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} (a₀₁ₚ ,sp a₀₁ₜ)

  ind-in-U' boolₚ y = boolᴰ
  ind-in-U' (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ) w =
    πᴰ (ind-in-U' aₚ a)
       (ind-in-U~' a~ₚ a~)
       (λ x → ind-in-U' (bₚ x) (b x))
       (λ x₀₁ → ind-in-U~' (b~ₚ x₀₁) (b~ x₀₁))
    where
      a : in-Uₜ aₚ
      a = withProp w (λ { (πₜ x _ _ _) → x })
      a~ : in-U~ₜ aₚ aₚ a~ₚ
      a~ = withProp w (λ { (πₜ _ x _ _) → x })
      b : (x : _) -> in-Uₜ (bₚ x)
      b x = withProp w (λ { (πₜ _ _ y _) → y x })
      b~ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)
      b~ = withProp w λ { (πₜ _ _ _ b~) → b~ }

  ind-in-U~' {a₀ = a₀} {a₁} bool~ₚ y =
    goal (to-≡ (withProp y (λ { bool~ₜ → reflp }))) (to-≡ (withProp y (λ { bool~ₜ → reflp })))
    where
      goal : a₀ ≡ bool -> a₁ ≡ bool -> _
      goal refl refl = bool~ᴰ
  ind-in-U~' {a₀ = x₀} {x₁} (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ) p =
    goal (to-≡ (withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ _) → reflp }))
         (to-≡ (withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ _) → reflp }))
    where
      a₀ₜ = withProp p λ { (π~ₜ x _ _ _ _ _ _ _ _ _) → x }
      a₀~ₜ = withProp p λ { (π~ₜ _ x _ _ _ _ _ _ _ _) → x }
      b₀ₜ : (x : _) -> in-Uₜ (b₀ₚ x)
      b₀ₜ = withProp p λ { (π~ₜ _ _ _ _ _ x _ _ _ _) → x }
      b₀~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁)
      b₀~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ x _ _ _) → x }
      a₁ₜ = withProp p λ { (π~ₜ _ _ x _ _ _ _ _ _ _) → x }
      a₁~ₜ = withProp p λ { (π~ₜ _ _ _ x _ _ _ _ _ _) → x }
      b₁ₜ : (x : _) -> in-Uₜ (b₁ₚ x)
      b₁ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ x _ _) → x }
      b₁~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁)
      b₁~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ x _) → x }
      a₀₁ₜ : in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ
      a₀₁ₜ = withProp p λ { (π~ₜ _ _ _ _ x _ _ _ _ _) → x }
      b₀₁ₜ : {x₀ : _} {x₁ : _} (x₀₁ : _) -> in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)
      b₀₁ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ x) → x }

      goal : x₀ ≡ π (a₀ₚ ,sp a₀ₜ) (a₀~ₚ ,sp a₀~ₜ) (λ x → b₀ₚ x ,sp b₀ₜ x) (λ x₀₁ → b₀~ₚ x₀₁ ,sp b₀~ₜ x₀₁)
           → x₁ ≡ π (a₁ₚ ,sp a₁ₜ) (a₁~ₚ ,sp a₁~ₜ) (λ x → b₁ₚ x ,sp b₁ₜ x) (λ x₀₁ → b₁~ₚ x₀₁ ,sp b₁~ₜ x₀₁)
           → _
      goal refl refl =
        π~ᴰ (ind-in-U' a₀ₚ a₀ₜ)
            (ind-in-U~' a₀~ₚ a₀~ₜ)
            (ind-in-U' a₁ₚ a₁ₜ)
            (ind-in-U~' a₁~ₚ a₁~ₜ)
            (ind-in-U~' a₀₁ₚ a₀₁ₜ)
            (λ x → ind-in-U' (b₀ₚ x) (b₀ₜ x))
            (λ x₀₁ → ind-in-U~' (b₀~ₚ x₀₁) (b₀~ₜ x₀₁))
            (λ x → ind-in-U' (b₁ₚ x) (b₁ₜ x))
            (λ x₀₁ → ind-in-U~' (b₁~ₚ x₀₁) (b₁~ₜ x₀₁))
            (λ x₀₁ → ind-in-U~' (b₀₁ₚ x₀₁) (b₀₁ₜ x₀₁))

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U (a ,sp a') = ind-in-U' a a'

  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
               (a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U~ (a ,sp a') = ind-in-U~' a a'
