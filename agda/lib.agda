{-# OPTIONS --without-K --prop #-}

module lib where

open import Agda.Primitive

data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_
