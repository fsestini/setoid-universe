{-# OPTIONS --prop --without-K #-}

module Setoid.Sets3.mini-univ-encoding where

open import Setoid.lib

data in-U : Set → Set₁
data in-P : Prop → Set₁

data in-U where
  in-𝟚 : in-U 𝟚
  in-Σ : ∀{A} {B : A → Set} {A~ : A → A → Prop}
          {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
       → in-U A → (∀ x₀ x₁ → in-P (A~ x₀ x₁))
       → (∀ x → in-U (B x))
       → (∀{x₀ x₁} x₀₁ (b₀ : B x₀) (b₁ : B x₁) → in-P (B~ x₀₁ b₀ b₁))
       → in-U (Σsp ((x : A) -> B x) λ f →
      (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁))

data in-P where
  in-≟𝟚 : (x y : 𝟚) → in-P (x ≟𝟚 y)
  in-fun : ∀{A₀ A₁} {B₀ : A₀ → Set} {B₁ : A₁ → Set} {A₀₁ : A₀ -> A₁ -> Prop}
           {B₀₁ : ∀{x₀ x₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
         → in-U A₀ → in-U A₁ → (∀ x y → in-P (A₀₁ x y))
         → (∀ x → in-U (B₀ x)) → (∀ x → in-U (B₁ x))
         → (∀{x₀ x₁} (x₀₁ : A₀₁ x₀ x₁) (b₀ : B₀ x₀) (b₁ : B₁ x₁) → in-P (B₀₁ x₀₁ b₀ b₁))
         → (f₀ : (a : A₀) → B₀ a) (f₁ : (a : A₁) → B₁ a)
         → in-P ((x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (A₀₁ x₀ x₁)) → B₀₁ (un↑ps x₀₁) (f₀ x₀) (f₁ x₁))

U = Σ _ in-U
P = Σ _ in-P

El : U → Set
El = proj₁

ElP : P → Prop
ElP = proj₁

𝟚-U : U
𝟚-U = _ ,Σ in-𝟚

Σsp-U : (A : U) (B : El A -> U)
        (A~ : El A -> El A -> P)
        (B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P)
      → U
Σsp-U A B A~ B~ = _ ,Σ in-Σ (proj₂ A) (λ x₀ x₁ → proj₂ (A~ x₀ x₁)) (λ x → proj₂ (B x))
                       λ x₀₁ b₀ b₁ → proj₂ (B~ x₀₁ b₀ b₁)

_≟𝟚-P_ : 𝟚 -> 𝟚 -> P
x ≟𝟚-P y = _ ,Σ in-≟𝟚 x y

fun-≡-P : (A₀ A₁ : U) (A₀₁ : El A₀ -> El A₁ -> P)
          (B₀ : El A₀ → U)(B₁ : El A₁ -> U)
          (B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P)
          (f₀ : (a : El A₀) → El (B₀ a)) (f₁ : (a : El A₁) → El (B₁ a))
        -> P
fun-≡-P A₀ A₁ A₀₁ B₀ B₁ B₀₁ f₀ f₁ =
  _ ,Σ in-fun (proj₂ A₀) (proj₂ A₁) (λ x y → proj₂ (A₀₁ x y))
    (λ x → proj₂ (B₀ x)) (λ x → proj₂ (B₁ x)) (λ x₀₁ b₀ b₁ → proj₂ (B₀₁ x₀₁ b₀ b₁))
    f₀ f₁
