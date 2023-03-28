{-# OPTIONS --prop --without-K #-}

module Setoid.Sets3.mini-univ where

open import Setoid.lib

data U : Set₁
data P : Set₁
El : U -> Set
ElP : P -> Prop

data U where
  𝟚-U : U
  -- Π-U : (A : U) -> (El A -> U) -> U
  Σsp-U : (A : U) (B : El A -> U)
          (A~ : El A -> El A -> P)
          (B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P)
        → U

El 𝟚-U = 𝟚
-- El (Π-U A B) = (a : El A) -> El (B a)
El (Σsp-U A B A~ B~) =
  Σsp ((x : El A) -> El (B x)) λ f →
      (x₀ x₁ : El A)(x₀₁ : ↑ps (ElP (A~ x₀ x₁))) → ElP (B~ (un↑ps x₀₁) (f x₀) (f x₁))

data P where
  _≟𝟚-P_ : 𝟚 -> 𝟚 -> P
  fun-≡-P : (A₀ A₁ : U) (A₀₁ : El A₀ -> El A₁ -> P)
            (B₀ : El A₀ → U)(B₁ : El A₁ -> U)
            (B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P)
            (f₀ : (a : El A₀) → El (B₀ a)) (f₁ : (a : El A₁) → El (B₁ a))
          -> P
  -- ⊤p-P : P
  -- ⊥p-P : P
  
ElP (x ≟𝟚-P y) = x ≟𝟚 y
ElP (fun-≡-P A₀ A₁ A₀₁ B₀ B₁ B₀₁ f₀ f₁) =
  (x₀ : El A₀)(x₁ : El A₁)(x₀₁ : ↑ps (ElP (A₀₁ x₀ x₁))) → ElP (B₀₁ (un↑ps x₀₁) (f₀ x₀) (f₁ x₁))
-- ElP ⊤p-P = ⊤p
-- ElP ⊥p-P = ⊥p
