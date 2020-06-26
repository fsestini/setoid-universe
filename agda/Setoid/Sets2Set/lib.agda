{-# OPTIONS --without-K --prop #-}

module Setoid.Sets2Set.lib where

-- typing is in Set

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
      (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : A₀₁ x₀ x₁) → B₀₁ x₀₁ (f₀ x₀) (f₁ x₁)})

-- typing predicates

open import Agda.Primitive

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x
infix 8 _≡_

record ↑l {ℓ ℓ'}(A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor mk↑l
  field
    un↑l : A
open ↑l public

in-Uₜ : {A : Set} → in-Uₚ A → Set₁
in-U~ₜ : {A₀ A₁ : Set}(a₀ : in-Uₚ A₀)(a₁ : in-Uₚ A₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ₚ A₀₁ → Set₁

in-Uₜ boolₚ = ↑l ⊤
in-Uₜ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ) =
  in-Uₜ aₚ ×
  in-U~ₜ aₚ aₚ a~ₚ ×
  ((x : A) → in-Uₜ (bₚ x)) ×
  ({x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁))
in-U~ₜ a₀ a₁ bool~ₚ = a₀ ≡ boolₚ × a₁ ≡ boolₚ
in-U~ₜ c₀ c₁ (π~ₚ {A₀} a₀ₚ {A₀~} a₀~ₚ {A₁} a₁ₚ {A₁~} a₁~ₚ {A₀₁} a₀₁ₚ {B₀} b₀ₚ {B₀~} b₀~ₚ {B₁} b₁ₚ {B₁~} b₁~ₚ {B₀₁} b₀₁ₚ) =
  c₀ ≡ πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ ×
  c₁ ≡ πₚ a₁ₚ a₁~ₚ b₁ₚ b₁~ₚ ×
  in-Uₜ a₀ₚ ×
  in-U~ₜ a₀ₚ a₀ₚ a₀~ₚ ×
  in-Uₜ a₁ₚ ×
  in-U~ₜ a₁ₚ a₁ₚ a₁~ₚ ×
  in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ ×
  ((x : A₀) → in-Uₜ (b₀ₚ x)) ×
  ({x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁)) ×
  ((x : A₁) → in-Uₜ (b₁ₚ x)) ×
  ({x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ₜ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁)) ×
  ({x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁))

module tryToProveThatTypingIsProp where

  ap : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
      → f a₀ ≡ f a₁
  ap f refl = refl

  _◾_ : ∀{ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl ◾ refl = refl
  infixl 4 _◾_

  F : ∀{i} → Set i → Set i
  F A = A → A → A

  fst : ∀{i}{A : Set i} → F A
  fst = λ x x' → x

  snd : ∀{i}{A : Set i} → F A
  snd = λ x x' → x'

  isprop : ∀{i} → Set i → Set i
  isprop A = _≡_ {A = F A} fst snd

  fst1 : ∀{i}{A : Set i}{j}{B : A → Set j} → (x : A) → F (B x)
  fst1 x y y' = y

  snd1 : ∀{i}{A : Set i}{j}{B : A → Set j} → (x : A) → F (B x)
  snd1 x y y' = y'

  isprop1 : ∀{i}{A : Set i}{j}(B : A → Set j) → Set (i ⊔ j)
  isprop1 {_}{A} B = _≡_ {A = (x : A) → F (B x)} fst1 snd1

  isprop× : ∀{i}{A : Set i}{j}{B : Set j} → isprop A → isprop B → isprop (A × B)
  isprop× {A = A}{B = B} pA pB =
    ap (λ z → λ (w w' : A × B) → (z (proj₁ w) (proj₁ w') ,Σ proj₂ w))  pA ◾
    ap (λ z → λ (w w' : A × B) → (proj₁ w' ,Σ z (proj₂ w) (proj₂ w'))) pB

  ispropΠ : ∀{i}{A : Set i}{j}{B : A → Set j} → isprop1 B → isprop ((x : A) → B x)
  ispropΠ pB = ap (λ z → λ f f' x → z x (f x) (f' x)) pB

  ispropU : ∀{A}(aₚ : in-Uₚ A) → isprop (in-Uₜ {A} aₚ)
  ispropU boolₚ = refl
  ispropU (πₚ aₚ a~ₚ bₚ b~ₚ) = isprop× (isprop× (isprop× (ispropU aₚ) {!!}) (ispropΠ {!ispropU !})) {!!}
  {-
  ispropU1 : ∀{I : Set}{A}(aₚ : I → in-Uₚ A) → isprop1 (λ z → in-Uₜ {A} (aₚ z))
  ispropU1 boolₚ = refl
  ispropU1 (πₚ aₚ a~ₚ bₚ b~ₚ) = isprop× (isprop× (isprop× (ispropU aₚ) {!!}) (ispropΠ {!ispropU !})) {!!}
  -}

-- reconstructing the IIT

in-U : Set → Set₁
in-U A = Σ (in-Uₚ A) in-Uₜ

in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁
in-U~ {A₀}{A₁}(a₀ₚ ,Σ a₀)(a₁ₚ ,Σ a₁) A₀₁ = Σ (in-U~ₚ A₀₁) (in-U~ₜ a₀ₚ a₁ₚ)

bool : in-U 𝟚
bool = boolₚ ,Σ mk↑l tt

π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
    in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : A~ x₀ x₁) → B~ x₀₁ (f x₀) (f x₁)))
π {A}(aₚ ,Σ a){A~}(a~ₚ ,Σ a~){B} b {B~} b~ =
  πₚ aₚ a~ₚ (λ x → proj₁ (b x)) (λ x₀₁ → proj₁ (b~ x₀₁)) ,Σ
  (a ,Σ a~ ,Σ (λ x → proj₂ (b x)) ,Σ λ x₀₁ → proj₂ (b~ x₀₁))

bool~ : in-U~ bool bool λ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
bool~ = bool~ₚ ,Σ (refl ,Σ refl)

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
        (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : A₀₁ x₀ x₁) → B₀₁ x₀₁ (f₀ x₀) (f₁ x₁)})
π~ {A₀}{a₀ₚ ,Σ a₀}{A₀~}{a₀~ₚ ,Σ a₀~}{A₁}{a₁ₚ ,Σ a₁}{A₁~}{a₁~ₚ ,Σ a₁~}{A₀₁}(a₀₁ₚ ,Σ a₀₁){B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{B₀₁} b₀₁ =
  π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ (λ x → proj₁ (b₀ x)) (λ x₀₁ → proj₁ (b₀~ x₀₁)) (λ x → proj₁ (b₁ x)) (λ x₀₁ → proj₁ (b₁~ x₀₁)) (λ x₀₁ → proj₁ (b₀₁ x₀₁)) ,Σ
  (refl ,Σ refl ,Σ a₀ ,Σ a₀~ ,Σ a₁ ,Σ a₁~ ,Σ a₀₁ ,Σ (λ x → proj₂ (b₀ x)) ,Σ (λ x₀₁ → proj₂ (b₀~ x₀₁)) ,Σ (λ x → proj₂ (b₁ x)) ,Σ (λ x₀₁ → proj₂ (b₁~ x₀₁)) ,Σ λ x₀₁ → proj₂ (b₀₁ x₀₁))

-- simple eliminator

module props
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
  ind-in-U (boolₚ ,Σ _) = boolᴰ
  ind-in-U (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,Σ (a ,Σ a~ ,Σ b ,Σ b~)) =
    πᴰ (ind-in-U (aₚ ,Σ a)) (ind-in-U~ (a~ₚ ,Σ a~)) (λ x → ind-in-U (bₚ x ,Σ b x)) (λ x₀₁ → ind-in-U~ (b~ₚ x₀₁ ,Σ b~ x₀₁))
  ind-in-U~ {a₀ = a₀ₚ ,Σ a₀}{a₁ = a₁ₚ ,Σ a₁} (bool~ₚ ,Σ (refl ,Σ refl)) = bool~ᴰ
  ind-in-U~ {a₀ = c₀ₚ ,Σ c₀}{a₁ = c₁ₚ ,Σ c₁}
    (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,Σ
    (refl ,Σ refl ,Σ a₀ ,Σ a₀~ ,Σ a₁ ,Σ a₁~ ,Σ a₀₁ ,Σ b₀ ,Σ b₀~ ,Σ b₁ ,Σ b₁~ ,Σ b₀₁)) =
    {!π~ᴰ
      (ind-in-U (a₀ₚ ,Σ a₀))
      (ind-in-U~ (a₀~ₚ ,Σ a₀~))
      (ind-in-U (a₁ₚ ,Σ a₁))
      (ind-in-U~ (a₁~ₚ ,Σ a₁~))
      (ind-in-U~ (a₀₁ₚ ,Σ a₀₁))
      (λ x → ind-in-U (b₀ₚ x ,Σ b₀ x))
      (λ x₀₁ → ind-in-U~ (b₀~ₚ x₀₁ ,Σ b₀~ x₀₁))
      (λ x → ind-in-U (b₁ₚ x ,Σ b₁ x))
      (λ x₀₁ → ind-in-U~ (b₁~ₚ x₀₁ ,Σ b₁~ x₀₁))
      (λ x₀₁ → ind-in-U~ (b₀₁ₚ x₀₁ ,Σ b₀₁ x₀₁))!}
    
-- this doesn't work because typing is not in Prop. to prove that typing is in hprop we need funext
