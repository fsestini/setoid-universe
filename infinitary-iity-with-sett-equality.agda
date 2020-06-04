{-# OPTIONS --without-K --prop --rewriting #-}

open import Agda.Primitive
open import Agda.Builtin.Equality renaming (_≡_ to _⇒_ ; refl to reduce)

variable
  i j k l : Level

record Lift {i} (P : Prop i) : Set i where
  constructor lift
  field
    unlift : P
open Lift

record ⊤ {i} : Prop i where
  constructor tt

record Σ {i j} (A : Set i) (P : A -> Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ
infix 4 _,_

data ∥_∥ (A : Set i) : Prop i where
  ∣_∣ : A -> ∥ A ∥

useTrunc : {A : Set i} {P : Prop j} -> ∥ A ∥ -> (A -> P) -> P
useTrunc ∣ x ∣ f = f x

_×_ : ∀{i j} -> Set i -> Set j -> Set (i ⊔ j)
A × B = Σ A (λ _ → B)

record ΣP {i j} (A : Prop i) (P : A -> Prop j) : Prop (i ⊔ j) where
  constructor _,P_
  field
    fstP : A
    sndP : P fstP
open ΣP
infix 4 _,P_

postulate
  _≡_ : {A : Set i} -> A -> A -> Prop i

  refl : {A : Set i} (x : A) -> x ≡ x

  coe : {A : Set i} (C : A -> Set j) {x y : A}
      -> x ≡ y -> C x -> C y

  coe-refl : {A : Set i} (C : A -> Set j) {x : A} {c : C x}
           -> coe C (refl x) c ⇒ c

  ≡fun : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a}
       -> f ≡ g ⇒ ({x y : A} (p : x ≡ y) -> coe B p (f x) ≡ g y)

  ≡Σ : {A : Set i} {B : A -> Set j} {p q : Σ A B}
     -> p ≡ q ⇒ ΣP (fst p ≡ fst q) λ r → coe B r (snd p) ≡ snd q

  ≡Lift : {P : Prop i} {p q : Lift P}
        -> p ≡ q ⇒ ⊤

{-# BUILTIN REWRITE _⇒_ #-}
{-# REWRITE ≡fun ≡Σ ≡Lift coe-refl #-}

coeP : {A : Set i} (P : A -> Prop j) {x y : A}
       -> x ≡ y -> P x -> P y
coeP P p x = unlift (coe (λ z → Lift (P z)) p (lift x))

module _ {A : Set i} {x : A} (C : (y : A) -> x ≡ y -> Set j) (d : C x (refl x)) where

  J : {y : A} -> (p : x ≡ y) -> C y p
  J {y} p = coe C' {x = x , lift (refl x)} {y , lift p} (p ,P tt) d
    where
      C' : Σ A (λ y → Lift (x ≡ y)) -> Set j
      C' (y , lift p) = C y p

module _ {A : Set i} {x : A} (C : (y : A) -> x ≡ y -> Prop j) (d : C x (refl x)) where

  JP : {y : A} -> (p : x ≡ y) -> C y p
  JP p = unlift (J (λ y p → Lift (C y p)) (lift d) p)

sym : (A : Set i) {a0 a1 : A} -> a0 ≡ a1 -> a1 ≡ a0
sym A p = {!!}

trans : (A : Set i) {a0 a1 a2 : A} -> a0 ≡ a1 -> a1 ≡ a2 -> a0 ≡ a2
trans A p q = {!!}

module _ {A : Set i} {B : Set j} (f : A -> B) {a0 a1 : A} (p : a0 ≡ a1) where

  cong : f a0 ≡ f a1
  cong = {!!}

-- to-⇒ : {A : Set i} {x y : A} -> x ≡ y -> x ⇒ y
-- to-⇒ {x = x} {y} p = coe (λ z → x ⇒ z) p reduce

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

record Σp {i j} (A : Set i) (P : A -> Prop j) : Set (i ⊔ j) where
  constructor _,p_
  field
    fst' : A
    snd' : P fst'
open Σp
infix 4 _,p_

-- data Con : Set
-- data Ty : Con -> Set

-- data Con where
--   ● : Con
--   _,_ : (Γ : Con) -> Ty Γ -> Con

-- data Ty where
--   π∞ : (Γ : Con) -> (ℕ -> Ty Γ) -> Ty Γ

data Con₀ : Set
data Ty₀ : Set

data Con₀ where
  ●₀ : Con₀
  _‣₀_ : Con₀ -> Ty₀ -> Con₀

data Ty₀ where
  π∞₀ : (ℕ -> Ty₀) -> Ty₀

data Con₁ : Con₀ -> Prop
data Ty₁ : Con₀ -> Ty₀ -> Prop

data Con₁ where
  ●₁ : Con₁ ●₀
  _‣₁_ : {Γ : Con₀} {A : Ty₀} -> Con₁ Γ -> Ty₁ Γ A -> Con₁ (Γ ‣₀ A)

data Ty₁ where
  π∞₁ : {Γ : Con₀} {f : ℕ -> Ty₀}
      → Con₁ Γ -> ((n : ℕ) -> Ty₁ Γ (f n)) -> Ty₁ Γ (π∞₀ f)

Con : Set
Con = Σp Con₀ Con₁

Ty : Con -> Set
Ty (p ,p q) = Σp Ty₀ (Ty₁ p)

● : Con
● = ●₀ ,p ●₁

_‣_ : (Γ : Con) -> Ty Γ -> Con
(Γ ,p p) ‣ (A ,p q) = _ ,p p ‣₁ q

π∞ : (Γ : Con) -> (ℕ -> Ty Γ) -> Ty Γ
π∞ (Γ ,p p) f = _ ,p π∞₁ p λ n → snd' (f n)

record Alg : Set₁ where
  field
    C : Set
    T : C -> Set
    ●a : C
    _‣a_ : (c : C) -> T c -> C
    π∞a : (c : C) -> (ℕ -> T c) -> T c

use : {P : Prop i} {Q : Prop j}
     -> P -> (P -> Q) -> Q
use p f = f p

funext : {A : Set i} {B : A -> Set j} {f g : (a : A) -> B a}
       -> ((x : A) -> f x ≡ g x) -> f ≡ g
funext {B = B} h {x = x} {y} p = {!!} -- definable

record DAlg : Set₁ where
  field
    Conᴰ : Con -> Set
    Tyᴰ : {Γ : Con} -> Conᴰ Γ -> Ty Γ -> Set
    ●ᴰ : Conᴰ ●
    _‣ᴰ_ : ∀{Γ A} (Γᴰ : Conᴰ Γ) -> Tyᴰ Γᴰ A -> Conᴰ (Γ ‣ A)
    π∞ᴰ : ∀{Γ} {f : ℕ -> Ty Γ} (Γᴰ : Conᴰ Γ) -> ((n : ℕ) -> Tyᴰ Γᴰ (f n))
        -> Tyᴰ Γᴰ (π∞ Γ f)

module eliminator (D : DAlg) where

  open DAlg D

  data R-Con : (Γ : Con) -> Conᴰ Γ -> Prop
  data R-Ty : ∀{Γ} {Γᴰ : Conᴰ Γ} (A : Ty Γ) -> Tyᴰ Γᴰ A -> Prop

  data R-Con where
    R-● : R-Con ● ●ᴰ
    R-‣ : {Γ : Con} {Γᴰ : Conᴰ Γ} {A : Ty Γ} {Aᴰ : Tyᴰ Γᴰ A}
        → R-Con Γ Γᴰ → R-Ty A Aᴰ
        → R-Con (Γ ‣ A) (Γᴰ ‣ᴰ Aᴰ)
    
  data R-Ty where
    R-π∞ : {Γ : Con} {Γᴰ : Conᴰ Γ} {f : ℕ -> Ty Γ} {fᴰ : (n : ℕ) → Tyᴰ Γᴰ (f n)}
         → R-Con Γ Γᴰ → ((n : ℕ) -> R-Ty (f n) (fᴰ n))
         → R-Ty (π∞ Γ f) (π∞ᴰ Γᴰ fᴰ)

  destruct : ∀ {Γ₀} {F₀} -> Ty₁ Γ₀ (π∞₀ F₀) -> ΣP (Con₁ Γ₀) λ Γ₁ → (n : ℕ) → Ty₁ Γ₀ (F₀ n)
  destruct (π∞₁ Γ₁ F₁) = Γ₁ ,P F₁

  mutual
    e-Con : ∀ Γ₀ (Γ₁ : Con₁ Γ₀) -> Σp (Conᴰ (Γ₀ ,p Γ₁)) (R-Con (Γ₀ ,p Γ₁))
    e-Con ●₀ Γ₁ = _ ,p R-●
    e-Con (Γ₀ ‣₀ A₀) Γ₁ = _ ,p R-‣ (snd' ih1) (snd' ih2)
      where
        ih1 = e-Con Γ₀ (use Γ₁ λ { (x ‣₁ _) → x})
        ih2 = e-Ty A₀ (use Γ₁ λ { (_ ‣₁ x) → x}) (snd' ih1)
  
    e-Ty : ∀{Γ} {Γᴰ : Conᴰ Γ} (A₀ : Ty₀) (A₁ : Ty₁ (fst' Γ) A₀) -> R-Con Γ Γᴰ
         -> Σp (Tyᴰ Γᴰ (A₀ ,p A₁)) (R-Ty (A₀ ,p A₁))
    e-Ty (π∞₀ F₀) A₁ r =
      _ ,p R-π∞ r λ n → let aux = sndP (destruct A₁) n in snd' (e-Ty _ aux r)

  aux : ∀{Γ₀} {Γ₁ : Con₁ Γ₀} {F₀ : ℕ -> Ty₀} (F₁ : (n : ℕ) → Ty₁ Γ₀ (F₀ n))
              {Γ : Conᴰ (Γ₀ ,p Γ₁)} (A : _)
      -> R-Ty (π∞₀ F₀ ,p π∞₁ Γ₁ F₁) A
      -> ∥ (Σ ((n : ℕ) -> Tyᴰ Γ (F₀ n ,p F₁ n)) λ F -> Lift (A ≡ π∞ᴰ Γ F) × ((n : _) -> Lift (R-Ty (F₀ n ,p F₁ n) (F n)))) ∥
  aux F₁ {Γ} _ (R-π∞ {fᴰ = fᴰ} x y) = ∣ _ , (lift (refl (π∞ᴰ Γ fᴰ)) , λ n → lift (y n)) ∣

  mutual
    uniq-Con : ∀ Γ₀ (Γ₁ : Con₁ Γ₀) (Γ Γ' : Conᴰ (Γ₀ ,p Γ₁))
             -> R-Con (Γ₀ ,p Γ₁) Γ -> R-Con (Γ₀ ,p Γ₁) Γ' -> Γ ≡ Γ'
    uniq-Con ●₀ ●₁ Γ .Γ R-● R-● = refl Γ
    uniq-Con (_ ‣₀ _) (Γ₁ ‣₁ A₁) _ _ (R-‣ {Γᴰ = Γ} {Aᴰ = A} p f) (R-‣ {Γᴰ = Γ'} {Aᴰ = A'} q g) = goal
      where
        ih = uniq-Con _ _ _ _ p q
        f' : R-Ty {Γᴰ = Γ'} _ (coe (λ z → Tyᴰ z _) ih A)
        f' = JP (λ Γ p → R-Ty {Γᴰ = Γ} _ (coe (λ z → Tyᴰ z _) p A)) f ih
        goal : (Γ ‣ᴰ A) ≡ (Γ' ‣ᴰ A')
        goal = coeP {A = Σ (Conᴰ _) λ Γ → Tyᴰ Γ _}
                    (λ z → (Γ ‣ᴰ A) ≡ (fst z ‣ᴰ snd z))
                    (ih ,P uniq-Ty _ _ q _ _ f' g)
                    (refl (Γ ‣ᴰ A))

    uniq-Ty : ∀{Γ} {Γᴰ : Conᴰ Γ} (A₀ : Ty₀) (A₁ : Ty₁ (fst' Γ) A₀) -> R-Con Γ Γᴰ
            -> (A A' : Tyᴰ Γᴰ (A₀ ,p A₁)) -> R-Ty (A₀ ,p A₁) A -> R-Ty (A₀ ,p A₁) A' -> A ≡ A'
    uniq-Ty (π∞₀ F₀) (π∞₁ Γ₁ F₁) x A A' p q =
      useTrunc (aux F₁ A p) λ aux1 →
      useTrunc (aux F₁ A' q) λ aux2 →
        let eq : fst aux1 ≡ fst aux2
            eq r = funext {f = fst aux1} {fst aux2}
                     (λ n → uniq-Ty _ (F₁ n) x _ _
                       (unlift (snd (snd aux1) n)) (unlift (snd (snd aux2) n))) r
        in trans (Tyᴰ _ (π∞₀ F₀ ,p _)) (unlift (fst (snd aux1)))
          (trans (Tyᴰ _ (π∞₀ F₀ ,p _)) (cong (π∞ᴰ _) eq)
                 (sym (Tyᴰ _ (π∞₀ F₀ ,p _)) (unlift (fst (snd aux2)))))
