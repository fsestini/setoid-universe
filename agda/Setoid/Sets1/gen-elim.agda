{-# OPTIONS --without-K --prop #-}

module Setoid.Sets1.gen-elim where

open import Setoid.lib
open import Setoid.Sets1.lib
open import Agda.Builtin.Equality
open import Agda.Primitive

variable i j k l : Level

withProp : ∀{i j} {P : Prop i} {Q : Prop j} -> P -> (P -> Q) -> Q
withProp p f = f p

postulate
  _≡p_ : ∀{i} {A : Set i} -> A -> A -> Prop i
  reflp : ∀{i} {A : Set i} {a : A} -> a ≡p a
  to-≡ : ∀{i} {A : Set i} {x y : A} -> x ≡p y -> x ≡ y

subst-T : {A B : Set i} -> A ≡ B -> A -> B
subst-T refl x = x

subst : {A : Set i} (C : A -> Set j) {x y : A} -> x ≡ y -> C x -> C y
subst _ refl x = x

withP : {P : Prop j} {Q : Prop k} {A : Set i} (x y : A)
      → P
      → (P -> x ≡p y)
      → (x ≡ y -> Q)
      → Q
withP x y p f g = g (to-≡ (f p))

module general
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Prop j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ aᴰ aᴰ a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ boolᴰ boolᴰ bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)) → 
    in-U~ᴰ (πᴰ a₀ᴰ a₀~ᴰ b₀ᴰ b₀~ᴰ) (πᴰ a₁ᴰ a₁~ᴰ b₁ᴰ b₁~ᴰ) (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁))
  where

  data R-U : {A : Set} (a : in-U A) -> in-Uᴰ a -> Prop (lsuc (i ⊔ j))
  data R-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (a₀₁ : in-U~ a₀ a₁ A₀₁)
            → in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁ -> Prop (lsuc i ⊔ lsuc j)

  data R-U where
    R-bool : R-U bool boolᴰ
    R-π :
      {A : Set}{a : in-U A}{aᴰ : in-Uᴰ a}(R-a : R-U a aᴰ)
      {A~ : A → A → Prop}{a~ : in-U~ a a A~}{a~ᴰ : in-U~ᴰ aᴰ aᴰ a~}(R-a~ : R-U~ a~ a~ᴰ)
      {B : A → Set}{b : (x : A) → in-U (B x)}{bᴰ : (x : A) → in-Uᴰ (b x)}(R-b : (x : A) -> R-U (b x) (bᴰ x))
      {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
      {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
      {b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ x₀₁)}
      (R-B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → R-U~ (b~ x₀₁) (b~ᴰ x₀₁))
      → R-U (π a a~ b b~) (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ)

  data R-U~ where
    R-bool~ : R-U~ bool~ bool~ᴰ
    R-π~ : {A₀ : Set}{a₀ : in-U A₀}{a₀ᴰ : in-Uᴰ a₀}(R-a₀ : R-U a₀ a₀ᴰ)
           {A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}{a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~}(R-a₀~ : R-U~ a₀~ a₀~ᴰ)
           {A₁ : Set}{a₁ : in-U A₁}{a₁ᴰ : in-Uᴰ a₁}(R-a₁ : R-U a₁ a₁ᴰ)
           {A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}{a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~}(R-a₁~ : R-U~ a₁~ a₁~ᴰ)
           {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}{a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁}(R-a₀₁ : R-U~ a₀₁ a₀₁ᴰ)
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀)}(R-b₀ : (x : _) -> R-U (b₀ x) (b₀ᴰ x))

           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁)}
           (R-b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → R-U~ (b₀~ x₀₁) (b₀~ᴰ x₀₁))
           
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁)}(R-b₁ : (x₁ : A₁) → R-U (b₁ x₁) (b₁ᴰ x₁))

           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
           {b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁)}
           (R-b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → R-U~ (b₁~ x₀₁) (b₁~ᴰ x₀₁))
           
           {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
           {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
           {b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)}
           (R-b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → R-U~ (b₀₁ x₀₁) (b₀₁ᴰ x₀₁))
        → R-U~
            (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
            (π~ᴰ a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ b₀₁ᴰ)

  postulate
    invert : ∀{i} {P : Prop i} {A : Set}{aₚ : in-Uₚ A}{A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}
        {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}
        {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
        {b~ₚ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ₚ (B~ x₀₁)}
        {aₜ : _} {a~ₜ : _} {bₜ : _} {b~ₜ : {x₀ x₁ : A} (x₀₁ : A~ x₀ x₁) → _}
        {xᴰ : _}
      → R-U (πₚ aₚ a~ₚ bₚ b~ₚ ,sp πₜ aₜ a~ₜ bₜ λ x₀₁ → b~ₜ x₀₁) xᴰ
      → ({aᴰ : _} {a~ᴰ : _} {bᴰ : (x : _) -> _} {b~ᴰ : {x₀ x₁ : A} (x₀₁ : A~ x₀ x₁) → _}
          -> R-U (aₚ ,sp aₜ) aᴰ
          -> R-U~ (a~ₚ ,sp a~ₜ) a~ᴰ
          -> ((x : _) -> R-U (bₚ x ,sp bₜ x) (bᴰ x))
          -> ({x₀ x₁ : A} (x₀₁ : A~ x₀ x₁) → R-U~ (b~ₚ x₀₁ ,sp b~ₜ x₀₁) (b~ᴰ x₀₁))
          -> πᴰ {a = aₚ ,sp aₜ} aᴰ {a~ = a~ₚ ,sp a~ₜ} a~ᴰ
                {b = λ x → bₚ x ,sp bₜ x} bᴰ {b~ = λ x₀₁ → b~ₚ x₀₁ ,sp b~ₜ x₀₁} b~ᴰ ≡ xᴰ
          -> P)
      → P

  exists-U : {A : Set} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> Σsp (in-Uᴰ (aₚ ,sp aₜ)) (R-U (aₚ ,sp aₜ))
  exists-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (p₀ : R-U a₀ a₀ᴰ) (p₁ : R-U a₁ a₁ᴰ)
              (a₀₁ₚ : in-U~ₚ A₀₁) (a₀₁ₜ : in-U~ₜ (proj₁sp a₀) (proj₁sp a₁) a₀₁ₚ)
            → Σp (in-U~ᴰ a₀ᴰ a₁ᴰ (a₀₁ₚ ,sp a₀₁ₜ)) (R-U~ (a₀₁ₚ ,sp a₀₁ₜ))

  exists-U boolₚ aₜ = _ ,sp R-bool
  exists-U (πₚ aₚ a~ₚ bₚ b~ₚ) p = _ ,sp
    R-π ih-a (proj₂p (exists-U~ ih-a ih-a a~ₚ a~ₜ)) ih-b
        (λ x₀₁ → proj₂p (exists-U~ (ih-b _) (ih-b _) (b~ₚ x₀₁) (b~ₜ x₀₁)))
    where
      aₜ : in-Uₜ aₚ
      aₜ = withProp p λ { (πₜ x _ _ _) → x }
      a~ₜ : in-U~ₜ aₚ aₚ a~ₚ
      a~ₜ = withProp p λ { (πₜ _ x _ _) → x }
      ih-a = proj₂sp (exists-U aₚ aₜ)
      bₜ : (x : _) -> in-Uₜ (bₚ x)
      bₜ x = withProp p λ { (πₜ _ _ f _) → f x }
      ih-b : (x : _) -> _
      ih-b x = proj₂sp (exists-U (bₚ x) (bₜ x))
      b~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)
      b~ₜ xx = withProp p λ { (πₜ _ _ _ f) → f xx }

  exists-U~ {a₀ = a₀} {a₁} {a₀ᴰ = a₀ᴰ} {a₁ᴰ} p₀ p₁ bool~ₚ y =
    goal (to-≡ (withProp y (λ { bool~ₜ → reflp }))) (to-≡ (withProp y (λ { bool~ₜ → reflp })))
    where
      goal : boolₚ ≡ proj₁sp a₀ -> boolₚ ≡ proj₁sp a₁ -> _
      goal refl refl =
        goal' (to-≡ (withProp p₀ (λ { R-bool → reflp})))
              (to-≡ (withProp p₁ (λ { R-bool → reflp})))
        where
          goal' : boolᴰ ≡ a₀ᴰ -> boolᴰ ≡ a₁ᴰ -> _
          goal' refl refl = bool~ᴰ ,p R-bool~

  exists-U~ {a₀ᴰ = xᴰ} {yᴰ} p₀ p₁
    (π~ₚ {A₀ = A₀} a₀ {A₀~ = A₀~} a₀~ {A₁ = A₁} a₁ {A₁~ = A₁~} a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)
    (π~ₜ a₀ₜ a₀~ₜ a₁ₜ a₁~ₜ a₀₁ₜ b₀ₜ b₀~ₜ b₁ₜ b₁~ₜ b₀₁ₜ) =
    invert p₀ λ x x₁ x₂ x₃ x₄ → invert p₁ λ x₅ x₆ x₇ x₈ x₉ →
      aux x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉
    where
      aux : {a₀ᴰ : _} {a₀~ᴰ : _} {b₀ᴰ : (x : _) -> _} {b₀~ᴰ : {x₀ x₁ : A₀} (x₀₁ : A₀~ x₀ x₁) → _}
         -> R-U (a₀ ,sp a₀ₜ) a₀ᴰ
         -> R-U~ (a₀~ ,sp a₀~ₜ) a₀~ᴰ
         -> ((x : _) -> R-U (b₀ x ,sp b₀ₜ x) (b₀ᴰ x))
         -> ({x₀ x₁ : A₀} (x₀₁ : A₀~ x₀ x₁) → R-U~ (b₀~ x₀₁ ,sp b₀~ₜ x₀₁) (b₀~ᴰ x₀₁))
         -> πᴰ {a = a₀ ,sp _} a₀ᴰ {a~ = a₀~ ,sp _} a₀~ᴰ {b = _} b₀ᴰ {b~ = λ x₀₁ → b₀~ x₀₁ ,sp b₀~ₜ x₀₁} b₀~ᴰ ≡ xᴰ

         -> {a₁ᴰ : _} {a₁~ᴰ : _} {b₁ᴰ : (x : _) -> _} {b₁~ᴰ : {x₀ x₁ : A₁} (x₀₁ : A₁~ x₀ x₁) → _}
         -> R-U (a₁ ,sp a₁ₜ) a₁ᴰ
         -> R-U~ (a₁~ ,sp a₁~ₜ) a₁~ᴰ
         -> ((x : _) -> R-U (b₁ x ,sp b₁ₜ x) (b₁ᴰ x))
         -> ({x₀ x₁ : A₁} (x₀₁ : A₁~ x₀ x₁) → R-U~ (b₁~ x₀₁ ,sp b₁~ₜ x₀₁) (b₁~ᴰ x₀₁))
         -> πᴰ {a = a₁ ,sp _} a₁ᴰ {a~ = a₁~ ,sp _} a₁~ᴰ {b = _} b₁ᴰ {b~ = λ x₀₁ → b₁~ x₀₁ ,sp b₁~ₜ x₀₁} b₁~ᴰ ≡ yᴰ

         -> Σp (in-U~ᴰ xᴰ yᴰ (π~ₚ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁ ,sp
                                  π~ₜ a₀ₜ a₀~ₜ a₁ₜ a₁~ₜ a₀₁ₜ b₀ₜ b₀~ₜ b₁ₜ b₁~ₜ b₀₁ₜ))
               (R-U~ (π~ₚ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁ ,sp _))
      aux x x₁ x₂ x₃ refl x₄ x₅ x₆ x₇ refl =
        _ ,p R-π~ x x₁ x₄ x₅ (proj₂p ih) x₂ x₃ x₆ x₇ λ x₀₁ → proj₂p (ih' x₀₁)
        where
          ih = exists-U~ x x₄ a₀₁ a₀₁ₜ
          ih' : {x₀ : A₀} {x₁ : A₁} (x₀₁ : _) → _
          ih' {x₀} {x₁} x₀₁ = exists-U~ (x₂ x₀) (x₆ x₁) (b₀₁ x₀₁) (b₀₁ₜ x₀₁)

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U (aₚ ,sp aₜ) = proj₁sp (exists-U aₚ aₜ)
  
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (ind-in-U a₀) (ind-in-U a₁) a₀₁
  ind-in-U~ (a₀₁ₚ ,sp a₀₁ₜ) = proj₁p (exists-U~ (proj₂sp (exists-U _ _)) (proj₂sp (exists-U _ _)) a₀₁ₚ a₀₁ₜ)
