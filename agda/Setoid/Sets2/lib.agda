{-# OPTIONS --without-K --prop #-}

module Setoid.Sets2.lib where

-- typing defined recursively and not inductively as in Sets1.lib

open import Setoid.lib

-- preterms

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

-- typing predicates

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ x
infix 8 _≡_

in-Uₜ : {A : Set} → in-Uₚ A → Prop₁
in-U~ₜ : {A₀ A₁ : Set}(a₀ : in-Uₚ A₀)(a₁ : in-Uₚ A₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ₚ A₀₁ → Prop₁

in-Uₜ boolₚ = ↑pl ⊤p
in-Uₜ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ) =
  in-Uₜ aₚ ×p
  in-U~ₜ aₚ aₚ a~ₚ ×p
  ((x : A) → in-Uₜ (bₚ x)) ×p
  ({x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁))
in-U~ₜ a₀ a₁ bool~ₚ = a₀ ≡ boolₚ ×p a₁ ≡ boolₚ
in-U~ₜ c₀ c₁ (π~ₚ {A₀} a₀ₚ {A₀~} a₀~ₚ {A₁} a₁ₚ {A₁~} a₁~ₚ {A₀₁} a₀₁ₚ {B₀} b₀ₚ {B₀~} b₀~ₚ {B₁} b₁ₚ {B₁~} b₁~ₚ {B₀₁} b₀₁ₚ) =
  c₀ ≡ πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ ×p
  c₁ ≡ πₚ a₁ₚ a₁~ₚ b₁ₚ b₁~ₚ ×p
  in-Uₜ a₀ₚ ×p
  in-U~ₜ a₀ₚ a₀ₚ a₀~ₚ ×p
  in-Uₜ a₁ₚ ×p
  in-U~ₜ a₁ₚ a₁ₚ a₁~ₚ ×p
  in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ ×p
  ((x : A₀) → in-Uₜ (b₀ₚ x)) ×p
  ({x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁)) ×p
  ((x : A₁) → in-Uₜ (b₁ₚ x)) ×p
  ({x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ₜ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁)) ×p
  ({x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁))

-- reconstructing the IIT

in-U : Set → Set₁
in-U A = Σsp (in-Uₚ A) in-Uₜ

in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁
in-U~ {A₀}{A₁}(a₀ₚ ,sp a₀)(a₁ₚ ,sp a₁) A₀₁ = Σsp (in-U~ₚ A₀₁) (in-U~ₜ a₀ₚ a₁ₚ)

bool : in-U 𝟚
bool = boolₚ ,sp mk↑pl ttp

π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
    in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁)))
π {A}(aₚ ,sp a){A~}(a~ₚ ,sp a~){B} b {B~} b~ =
  πₚ aₚ a~ₚ (λ x → proj₁sp (b x)) (λ x₀₁ → proj₁sp (b~ x₀₁)) ,sp
  (a ,p a~ ,p (λ x → proj₂sp (b x)) ,p λ x₀₁ → proj₂sp (b~ x₀₁))

bool~ : in-U~ bool bool λ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
bool~ = bool~ₚ ,sp (refl ,p refl)

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
π~ {A₀}{a₀ₚ ,sp a₀}{A₀~}{a₀~ₚ ,sp a₀~}{A₁}{a₁ₚ ,sp a₁}{A₁~}{a₁~ₚ ,sp a₁~}{A₀₁}(a₀₁ₚ ,sp a₀₁){B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{B₀₁} b₀₁ =
  π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ (λ x → proj₁sp (b₀ x)) (λ x₀₁ → proj₁sp (b₀~ x₀₁)) (λ x → proj₁sp (b₁ x)) (λ x₀₁ → proj₁sp (b₁~ x₀₁)) (λ x₀₁ → proj₁sp (b₀₁ x₀₁)) ,sp
  (refl ,p refl ,p a₀ ,p a₀~ ,p a₁ ,p a₁~ ,p a₀₁ ,p (λ x → proj₂sp (b₀ x)) ,p (λ x₀₁ → proj₂sp (b₀~ x₀₁)) ,p (λ x → proj₂sp (b₁ x)) ,p (λ x₀₁ → proj₂sp (b₁~ x₀₁)) ,p λ x₀₁ → proj₂sp (b₀₁ x₀₁))

-- simple eliminator targetting propositions

module props
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
  ind-in-U (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp (a ,p a~ ,p b ,p b~)) =
    πᴰ (ind-in-U (aₚ ,sp a)) (ind-in-U~ (a~ₚ ,sp a~)) (λ x → ind-in-U (bₚ x ,sp b x)) (λ x₀₁ → ind-in-U~ (b~ₚ x₀₁ ,sp b~ x₀₁))
  ind-in-U~ {a₀ = a₀ₚ ,sp a₀}{a₁ = a₁ₚ ,sp a₁} (bool~ₚ ,sp (refl ,p refl)) = bool~ᴰ
  ind-in-U~ (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp (refl ,p refl ,p a₀ ,p a₀~ ,p a₁ ,p a₁~ ,p a₀₁ ,p b₀ ,p b₀~ ,p b₁ ,p b₁~ ,p b₀₁)) =
    π~ᴰ (ind-in-U (a₀ₚ ,sp a₀)) (ind-in-U~ (a₀~ₚ ,sp a₀~)) (ind-in-U (a₁ₚ ,sp a₁)) (ind-in-U~ (a₁~ₚ ,sp a₁~)) (ind-in-U~ (a₀₁ₚ ,sp a₀₁))
    (λ x → ind-in-U (b₀ₚ x ,sp b₀ x)) (λ x₀₁ → ind-in-U~ (b₀~ₚ x₀₁ ,sp b₀~ x₀₁)) (λ x → ind-in-U (b₁ₚ x ,sp b₁ x)) (λ x₀₁ → ind-in-U~ (b₁~ₚ x₀₁ ,sp b₁~ x₀₁))
    λ x₀₁ → ind-in-U~ (b₀₁ₚ x₀₁ ,sp b₀₁ x₀₁)

-- simple eliminator targetting sets

_⁻¹ : ∀{ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

_◾_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl

transpP : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Prop ℓ'){x y : A}(p : x ≡ y) → P x → P y
transpP P refl u = u

postulate
  transp : ∀{ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A}(p : x ≡ y) → P x → P y

J : ∀{ℓ ℓ'}{A : Set ℓ} {x : A} (P : {y : A} → x ≡ y → Set ℓ') → P refl → {y : A} → (w : x ≡ y) → P w
J {x = x} P pr w = transp (λ y → (e : x ≡ y) → P e) w (λ _ → pr) w

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

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U (boolₚ ,sp _) = boolᴰ
  ind-in-U (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp (a ,p a~ ,p b ,p b~)) =
    πᴰ (ind-in-U (aₚ ,sp a)) (ind-in-U~ (a~ₚ ,sp a~)) (λ x → ind-in-U (bₚ x ,sp b x)) (λ x₀₁ → ind-in-U~ (b~ₚ x₀₁ ,sp b~ x₀₁))
  ind-in-U~ {a₀ = a₀ₚ ,sp a₀}{a₁ = a₁ₚ ,sp a₁} (bool~ₚ ,sp (e₀ ,p e₁)) =
     J (λ {z} e → in-U~ᴰ {_}{_}{z ,sp transpP in-Uₜ (e₀ ◾ e) a₀}{a₁ₚ ,sp a₁} (bool~ₚ ,sp (e ⁻¹ ,p e₁)))
       (J (λ {z} e → in-U~ᴰ {_}{_}{boolₚ ,sp mk↑pl ttp}{z ,sp transpP in-Uₜ (e₁ ◾ e) a₁} (bool~ₚ ,sp (refl ,p (e ⁻¹))))
          bool~ᴰ (e₁ ⁻¹))
       (e₀ ⁻¹) 
  ind-in-U~ {a₀ = c₀ₚ ,sp c₀}{a₁ = c₁ₚ ,sp c₁}(π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp (e₀ ,p e₁ ,p a₀ ,p a₀~ ,p a₁ ,p a₁~ ,p a₀₁ ,p b₀ ,p b₀~ ,p b₁ ,p b₁~ ,p b₀₁)) =
    J (λ {z} e → in-U~ᴰ {_}{_}{z ,sp transpP in-Uₜ (e₀ ◾ e) c₀}{c₁ₚ ,sp c₁} (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp (e ⁻¹ ,p e₁ ,p a₀ ,p a₀~ ,p a₁ ,p a₁~ ,p a₀₁ ,p b₀ ,p b₀~ ,p b₁ ,p b₁~ ,p b₀₁)))
      (J (λ {z} e → in-U~ᴰ {_}{_}{πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ ,sp (a₀ ,p a₀~ ,p b₀ ,p b₀~)}{z ,sp transpP in-Uₜ (e₁ ◾ e) c₁} (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp (refl ,p (e ⁻¹) ,p a₀ ,p a₀~ ,p a₁ ,p a₁~ ,p a₀₁ ,p b₀ ,p b₀~ ,p b₁ ,p b₁~ ,p b₀₁)))
         (π~ᴰ
           (ind-in-U (a₀ₚ ,sp a₀))
           (ind-in-U~ (a₀~ₚ ,sp a₀~))
           (ind-in-U (a₁ₚ ,sp a₁))
           (ind-in-U~ (a₁~ₚ ,sp a₁~))
           (ind-in-U~ (a₀₁ₚ ,sp a₀₁))
           (λ x → ind-in-U (b₀ₚ x ,sp b₀ x))
           (λ x₀₁ → ind-in-U~ (b₀~ₚ x₀₁ ,sp b₀~ x₀₁))
           (λ x → ind-in-U (b₁ₚ x ,sp b₁ x))
           (λ x₀₁ → ind-in-U~ (b₁~ₚ x₀₁ ,sp b₁~ x₀₁))
           (λ x₀₁ → ind-in-U~ (b₀₁ₚ x₀₁ ,sp b₀₁ x₀₁)))
         (e₁ ⁻¹))
      (e₀ ⁻¹)
