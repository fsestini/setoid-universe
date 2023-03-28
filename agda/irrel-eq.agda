{-# OPTIONS --without-K --prop --rewriting #-}

module irrel-eq where

open import Relation.Binary.PropositionalEquality

postulate
  _≡p_ : ∀{i} {A : Set i} -> A -> A -> Prop i
  reflp : ∀{i} {A : Set i} {a : A} -> a ≡p a
  transp : ∀{i j} {A : Set i} (B : A → Set j) {x y : A} -> x ≡p y → B x → B y
  transp-refl : ∀{i j} {A : Set i} (B : A → Set j) {x : A} (b : B x) (p : x ≡p x) → transp B p b ≡ b

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE transp-refl #-}

to-≡ : ∀{i} {A : Set i} {x y : A} -> x ≡p y -> x ≡ y
to-≡ {x = x} p = transp (x ≡_) p refl

from-≡ : ∀{i} {A : Set i} {x y : A} -> x ≡ y -> x ≡p y
from-≡ refl = reflp
