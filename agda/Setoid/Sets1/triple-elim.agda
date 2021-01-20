{-# OPTIONS --without-K --prop #-}

module Setoid.Sets1.triple-elim where

open import Setoid.lib
open import Setoid.Sets1.lib

module _
  {i}
  (theT : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → Set i)
  (b-b-b : theT bool bool bool)
  (b-b-p : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
         → theT bool bool (π a a~ b b~))
  (b-p-x : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
           {A' : Set} {x : in-U A'}
         → theT bool (π a a~ b b~) x)
  (p-b-x : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
           {A' : Set} {x : in-U A'}
         → theT (π a a~ b b~) bool x)
  (p-p-b : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
           {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
         → theT a₁ a₀ a₀
         → theT a₀ a₁ a₀
         → theT a₁ a₁ a₀
         → ((x₀ x₁ : A₀) (x₂ : A₁) → theT (b₀ x₀) (b₀ x₁) (b₁ x₂))
         → ((x₀ : A₁) (x₁ : A₀) (x₂ : A₁) → theT (b₁ x₀) (b₀ x₁) (b₁ x₂))
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₁) → theT (b₀ x₀) (b₁ x₁) (b₁ x₂))
         → theT (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) bool)
  (p-p-p : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
           {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
           {A₂ : Set}{a₂ : in-U A₂}{A₂~ : A₂ → A₂ → Prop}{a₂~ : in-U~ a₂ a₂ A₂~}
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
           {B₂ : A₂ → Set}{b₂ : (x₁ : A₂) → in-U (B₂ x₁)}
           {B₂~ : {x₀ x₁ : A₂}(x₀₁ : A₂~ x₀ x₁) → B₂ x₀ → B₂ x₁ → Prop}
           {b₂~ : {x₀ x₁ : A₂}(x₀₁ : A₂~ x₀ x₁) → in-U~ (b₂ x₀) (b₂ x₁) (B₂~ x₀₁)}
         → theT a₁ a₀ a₀ -- a100
         → theT a₀ a₁ a₀ -- a010
         → theT a₁ a₁ a₀ -- a110
         → theT a₁ a₀ a₁ -- a101
         → theT a₀ a₁ a₂
         → theT a₀ a₂ a₁
         → theT a₀ a₁ a₁
         → theT a₂ a₁ a₁
         → ((x₀ x₁ : A₀) (x₂ : A₁) → theT (b₀ x₀) (b₀ x₁) (b₁ x₂))        -- b001
         → ((x₀ : A₁) (x₁ : A₀) (x₂ : A₁) → theT (b₁ x₀) (b₀ x₁) (b₁ x₂)) -- b101
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₁) → theT (b₀ x₀) (b₁ x₁) (b₁ x₂)) -- b011
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₂) → theT (b₀ x₀) (b₁ x₁) (b₂ x₂))
         → ((x₀ : A₁) (x₁ : A₁) (x₂ : A₂) → theT (b₁ x₀) (b₁ x₁) (b₂ x₂))
         → theT (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (π a₂ a₂~ b₂ b₂~))
  where


  triple' : {A₀ A₁ A₂ : _} (a₀ₚ : in-Uₚ A₀) (a₁ₚ : in-Uₚ A₁) (a₂ₚ : in-Uₚ A₂)
            (a₀ₜ : in-Uₜ a₀ₚ) (a₁ₜ : in-Uₜ a₁ₚ) (a₂ₜ : in-Uₜ a₂ₚ)
          → theT (a₀ₚ ,sp a₀ₜ) (a₁ₚ ,sp a₁ₜ) (a₂ₚ ,sp a₂ₜ)
  triple' boolₚ boolₚ boolₚ a₀ₜ a₁ₜ a₂ₜ = b-b-b
  triple' boolₚ boolₚ (πₚ a₂ₚ a~ₚ bₚ b~ₚ) a₀ₜ a₁ₜ a₂ₜ =
    b-b-p {a = a₂ₚ ,sp aₜ} {a~ = a~ₚ ,sp a~ₜ} {b = λ x → bₚ x ,sp bₜ x} {b~ = λ x₀₁ → b~ₚ x₀₁ ,sp b~ₜ x₀₁}
    where
      aₜ = withProp a₂ₜ (λ{ (πₜ a a~ b b~) → a})
      bₜ : (x : _) -> _
      bₜ = withProp a₂ₜ (λ{ (πₜ a a~ b b~) → b})
      a~ₜ = withProp a₂ₜ (λ{ (πₜ a a~ b b~) → a~ })
      b~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x)
      b~ₜ = withProp a₂ₜ (λ{ (πₜ a a~ b b~) → b~})

  triple' boolₚ (πₚ a₁ₚ a~ₚ bₚ b~ₚ) t₂ p₀ p₁ p₂ =
    b-p-x {a = a₁ₚ ,sp a₁ₜ} {a~ = a~ₚ ,sp a₁~ₜ} {b = λ x → bₚ x ,sp bₜ₁ x} {b~ = λ x₀₁ → b~ₚ x₀₁ ,sp b₁~ₜ x₀₁}
    where
      a₁ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a})
      a₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a~})
      bₜ₁ : (x : _) -> in-Uₜ (bₚ x)
      bₜ₁ = withProp p₁ (λ{ (πₜ a a~ b b~) → b})
      b₁~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x)
      b₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → b~})
  triple' (πₚ a₀ₚ a~ₚ bₚ b~ₚ) boolₚ _ p₀ p₁ p₂ =
    p-b-x {a = a₀ₚ ,sp a₀ₜ} {a~ = a~ₚ ,sp a₀~ₜ} {b = λ x → bₚ x ,sp bₜ₀ x} {b~ = λ x₀₁ → b~ₚ x₀₁ ,sp b₀~ₜ x₀₁}
    where
      a₀ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a})
      a₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a~})
      bₜ₀ : (x : _) -> in-Uₜ (bₚ x)
      bₜ₀ = withProp p₀ (λ{ (πₜ a a~ b b~) → b})
      b₀~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x)
      b₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → b~})

  triple' (πₚ a₀ₚ a~ₚ bₚ₀ b~ₚ₀) (πₚ a₁ₚ a~ₚ₁ bₚ₁ b~ₚ₁) boolₚ p₀ p₁ p₂ =
    p-p-b {a₀ = a₀ₚ ,sp a₀ₜ} {a₀~ = a~ₚ ,sp a₀~ₜ} {a₁ = a₁ₚ ,sp a₁ₜ} {a₁~ = a~ₚ₁ ,sp a₁~ₜ}
          {b₀ = λ x → bₚ₀ x ,sp bₜ₀ x} {b₀~ = λ x₀₁ → b~ₚ₀ x₀₁ ,sp b₀~ₜ x₀₁}
          {b₁ = λ x → bₚ₁ x ,sp bₜ₁ x} {b₁~ = λ x₀₁ → b~ₚ₁ x₀₁ ,sp b₁~ₜ x₀₁}
          (triple' a₁ₚ a₀ₚ a₀ₚ a₁ₜ a₀ₜ a₀ₜ)
          (triple' a₀ₚ a₁ₚ a₀ₚ a₀ₜ a₁ₜ a₀ₜ)
          (triple' a₁ₚ a₁ₚ a₀ₚ a₁ₜ a₁ₜ a₀ₜ)
          (λ x₀ x₁ x₂ → triple' (bₚ₀ x₀) (bₚ₀ x₁) (bₚ₁ x₂) (bₜ₀ x₀) (bₜ₀ x₁) (bₜ₁ x₂))
          (λ x₀ x₁ x₂ → triple' (bₚ₁ x₀) (bₚ₀ x₁) (bₚ₁ x₂) (bₜ₁ x₀) (bₜ₀ x₁) (bₜ₁ x₂))
          (λ x₀ x₁ x₂ → triple' (bₚ₀ x₀) (bₚ₁ x₁) (bₚ₁ x₂) (bₜ₀ x₀) (bₜ₁ x₁) (bₜ₁ x₂))
    where
      a₀ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a})
      a₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a~})
      a₁ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a})
      a₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a~})
      bₜ₀ : (x : _) -> in-Uₜ (bₚ₀ x)
      bₜ₀ = withProp p₀ (λ{ (πₜ a a~ b b~) → b})
      bₜ₁ : (x : _) -> in-Uₜ (bₚ₁ x)
      bₜ₁ = withProp p₁ (λ{ (πₜ a a~ b b~) → b})
      b₀~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ₀ x₀) (bₚ₀ x₁) (b~ₚ₀ x)
      b₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → b~})
      b₁~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ₁ x₀) (bₚ₁ x₁) (b~ₚ₁ x)
      b₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → b~})
      
  triple' (πₚ a₀ₚ a~ₚ bₚ₀ b~ₚ₀) (πₚ a₁ₚ a~ₚ₁ bₚ₁ b~ₚ₁) (πₚ a₂ₚ a~ₚ₂ bₚ₂ b~ₚ₂) p₀ p₁ p₂ =
    p-p-p
      {a₀ = a₀ₚ ,sp a₀ₜ} {a₀~ = a~ₚ ,sp a₀~ₜ} {a₁ = a₁ₚ ,sp a₁ₜ} {a₁~ = a~ₚ₁ ,sp a₁~ₜ} {a₂ = a₂ₚ ,sp a₂ₜ} {a₂~ = a~ₚ₂ ,sp a₂~ₜ}
      {b₀ = λ x → bₚ₀ x ,sp bₜ₀ x} {b₀~ = λ x₀₁ → b~ₚ₀ x₀₁ ,sp b₀~ₜ x₀₁}
      {b₁ = λ x → bₚ₁ x ,sp bₜ₁ x} {b₁~ = λ x₀₁ → b~ₚ₁ x₀₁ ,sp b₁~ₜ x₀₁}
      {b₂ = λ x → bₚ₂ x ,sp bₜ₂ x} {b₂~ = λ x₀₁ → b~ₚ₂ x₀₁ ,sp b₂~ₜ x₀₁}
      (triple' a₁ₚ a₀ₚ a₀ₚ a₁ₜ a₀ₜ a₀ₜ)
      (triple' a₀ₚ a₁ₚ a₀ₚ a₀ₜ a₁ₜ a₀ₜ)
      (triple' a₁ₚ a₁ₚ a₀ₚ a₁ₜ a₁ₜ a₀ₜ)
      (triple' a₁ₚ a₀ₚ a₁ₚ a₁ₜ a₀ₜ a₁ₜ)
      (triple' a₀ₚ a₁ₚ a₂ₚ a₀ₜ a₁ₜ a₂ₜ)
      (triple' a₀ₚ a₂ₚ a₁ₚ a₀ₜ a₂ₜ a₁ₜ)
      (triple' a₀ₚ a₁ₚ a₁ₚ a₀ₜ a₁ₜ a₁ₜ)
      (triple' a₂ₚ a₁ₚ a₁ₚ a₂ₜ a₁ₜ a₁ₜ)
      (λ x₀ x₁ x₂ → triple' (bₚ₀ x₀) (bₚ₀ x₁) (bₚ₁ x₂) (bₜ₀ x₀) (bₜ₀ x₁) (bₜ₁ x₂))
      (λ x₀ x₁ x₂ → triple' (bₚ₁ x₀) (bₚ₀ x₁) (bₚ₁ x₂) (bₜ₁ x₀) (bₜ₀ x₁) (bₜ₁ x₂))
      (λ x₀ x₁ x₂ → triple' (bₚ₀ x₀) (bₚ₁ x₁) (bₚ₁ x₂) (bₜ₀ x₀) (bₜ₁ x₁) (bₜ₁ x₂))
      (λ x₀ x₁ x₂ → triple' (bₚ₀ x₀) (bₚ₁ x₁) (bₚ₂ x₂) (bₜ₀ x₀) (bₜ₁ x₁) (bₜ₂ x₂))
      (λ x₀ x₁ x₂ → triple' (bₚ₁ x₀) (bₚ₁ x₁) (bₚ₂ x₂) (bₜ₁ x₀) (bₜ₁ x₁) (bₜ₂ x₂))
    where
      a₀ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a})
      a₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → a~})
      a₁ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a})
      a₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → a~})
      a₂ₜ = withProp p₂ (λ{ (πₜ a a~ b b~) → a})
      a₂~ₜ = withProp p₂ (λ{ (πₜ a a~ b b~) → a~})
      bₜ₀ : (x : _) -> _
      bₜ₀ = withProp p₀ (λ{ (πₜ a a~ b b~) → b})
      bₜ₁ : (x : _) -> _
      bₜ₁ = withProp p₁ (λ{ (πₜ a a~ b b~) → b})
      bₜ₂ : (x : _) -> _
      bₜ₂ = withProp p₂ (λ{ (πₜ a a~ b b~) → b})
      b₀~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ₀ x₀) (bₚ₀ x₁) (b~ₚ₀ x)
      b₀~ₜ = withProp p₀ (λ{ (πₜ a a~ b b~) → b~})
      b₁~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ₁ x₀) (bₚ₁ x₁) (b~ₚ₁ x)
      b₁~ₜ = withProp p₁ (λ{ (πₜ a a~ b b~) → b~})
      b₂~ₜ : {x₀ : _}{x₁ : _} (x : _) -> in-U~ₜ (bₚ₂ x₀) (bₚ₂ x₁) (b~ₚ₂ x)
      b₂~ₜ = withProp p₂ (λ{ (πₜ a a~ b b~) → b~})

  triple : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → theT a₀ a₁ a₂
  triple (a0 ,sp a0') (a1 ,sp a1') (a2 ,sp a2') = triple' a0 a1 a2 a0' a1' a2'
