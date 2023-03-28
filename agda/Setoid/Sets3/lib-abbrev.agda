{-# OPTIONS --prop --without-K #-}

module Setoid.Sets3.lib-abbrev where

open import Setoid.lib
open import Setoid.Sets3.mini-univ
open import Relation.Binary.PropositionalEquality

data in-U : U -> Set₁
data in-U~ : ∀{A₀ A₁} (a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : El A₀ -> El A₁ -> P) → Set₁

record Std : Set₁ where
  inductive
  constructor std
  field
    {∣_∣} : U
    pf : in-U ∣_∣
    {_~} : El ∣_∣ → El ∣_∣ → P
    pf~ : in-U~ pf pf _~
open Std public

record Std-Rel (A₀ A₁ : Std) : Set₁ where
  inductive
  constructor rel
  field
    {∣_∣} : El ∣ A₀ ∣ → El ∣ A₁ ∣ → P
    pf : in-U~ (pf A₀) (pf A₁) ∣_∣
open Std-Rel public

record IxStd (S : Std) : Set₁ where
  inductive
  constructor ixstd
  private
    A = ∣ S ∣
    A~ = S ~
  field
    {∣_∣} : El A → U
    pf : (x : _) → in-U (∣_∣ x)
    {_~} : ∀{x₀ x₁} (x₀₁ : ElP (A~ x₀ x₁)) → El (∣_∣ x₀) → El (∣_∣ x₁) → P
    pf~ : ∀{x₀ x₁} (x₀₁ : ElP (A~ x₀ x₁)) → in-U~ (pf x₀) (pf x₁) (_~ x₀₁)
open IxStd public

record IxStd-Rel {A₀ A₁ : Std} (B₀ : IxStd A₀) (B₁ : IxStd A₁) (A₀₁ : Std-Rel A₀ A₁) : Set₁ where
  inductive
  constructor ixrel
  field
    {∣_∣} : ∀{x₀ x₁}(x₀₁ : ElP (∣ A₀₁ ∣ x₀ x₁)) → El (∣ B₀ ∣ x₀) → El (∣ B₁ ∣ x₁) → P
    pf : {x₀ : _}{x₁ : _} → (x₀₁ : ElP (Std-Rel.∣_∣ A₀₁ x₀ x₁)) → in-U~ ((pf B₀) x₀) ((pf B₁) x₁) (∣_∣ x₀₁)
open IxStd-Rel public

data in-U where
  bool : in-U 𝟚-U
  π : (A : Std) → (B : IxStd A) → in-U (Σsp-U ∣ A ∣ ∣ B ∣ (A ~) (B ~))

data in-U~ where
  bool~ : in-U~ bool bool (λ x₀ x₁ → x₀ ≟𝟚-P x₁)
  π~ : ∀{A₀ A₁ B₀ B₁} (A₀₁ : Std-Rel A₀ A₁) (B₀₁ : IxStd-Rel B₀ B₁ A₀₁)
    → in-U~ (π A₀ B₀) (π A₁ B₁) λ f₀ f₁ → fun-≡-P _ _ (∣ A₀₁ ∣) _ _ (∣ B₀₁ ∣) (proj₁sp f₀) (proj₁sp f₁)
