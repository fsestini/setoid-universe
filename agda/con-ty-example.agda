open import Agda.Primitive
open import Agda.Builtin.Equality

variable
  i j k l : Level

subst : {A : Set i} (P : A -> Set j) {x y : A}
      -> x ≡ y -> P x -> P y
subst P refl x = x

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

record Σ {i j} (A : Set i) (P : A -> Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ
infix 4 _,_

-- data Con : Set
-- data Ty : Con -> Set

-- data Con where
--   ● : Con
--   _‣_ : (Γ : Con) -> Ty Γ -> Con

-- data Ty where
--   ι : Ty Γ
--   π : {Γ : Con} (A : Ty Γ) -> Ty (Γ ‣ A) -> Ty Γ

data Con₀ : Set
data Ty₀ : Set

data Con₀ where
  ●₀ : Con₀
  _‣₀_ : Con₀ -> Ty₀ -> Con₀

data Ty₀ where
  ι₀ : Con₀ -> Ty₀
  π₀ : Con₀ -> Ty₀ -> Ty₀ -> Ty₀

data Con₁ : Con₀ -> Set
data Ty₁ : Con₀ -> Ty₀ -> Set

data Con₁ where
  ●₁ : Con₁ ●₀
  _‣₁_ : {Γ : Con₀} {A : Ty₀} -> Con₁ Γ -> Ty₁ Γ A -> Con₁ (Γ ‣₀ A)

data Ty₁ where
  ι₁ : {Γ₀ : Con₀} -> Con₁ Γ₀ -> Ty₁ Γ₀ (ι₀ Γ₀)
  π₁ : {Γ₀ : Con₀} {A₀ : Ty₀} {B₀ : Ty₀}
     → Con₁ Γ₀
     → Ty₁ Γ₀ A₀
     → Ty₁ (Γ₀ ‣₀ A₀) B₀
     → Ty₁ Γ₀ (π₀ Γ₀ A₀ B₀)

Con : Set
Con = Σ Con₀ Con₁

Ty : Con -> Set
Ty (p , q) = Σ Ty₀ (Ty₁ p)

● : Con
● = ●₀ , ●₁

_‣_ : (Γ : Con) -> Ty Γ -> Con
(Γ , p) ‣ (A , q) = _ , p ‣₁ q

ι : (Γ : Con) -> Ty Γ
ι (Γ₀ , Γ₁) = ι₀ Γ₀ , ι₁ Γ₁

π : (Γ : Con) (A : Ty Γ) -> Ty (Γ ‣ A) -> Ty Γ
π (Γ₀ , Γ₁) (A₀ , A₁) (B₀ , B₁) = π₀ Γ₀ A₀ B₀ , π₁ Γ₁ A₁ B₁

mutual
  Con₁-is-prop : (Γ₀ : Con₀) (p q : Con₁ Γ₀) -> p ≡ q
  Con₁-is-prop ●₀ ●₁ ●₁ = refl
  Con₁-is-prop (Γ₀ ‣₀ A₀) (p ‣₁ p') (q ‣₁ q')
    rewrite Con₁-is-prop _ p q
          | Ty₁-is-prop A₀ p' q' = refl

  Ty₁-is-prop : {Γ₀ : Con₀} (A₀ : Ty₀) (p q : Ty₁ Γ₀ A₀) -> p ≡ q
  Ty₁-is-prop (ι₀ Γ₀) (ι₁ p) (ι₁ q) rewrite Con₁-is-prop _ p q = refl
  Ty₁-is-prop (π₀ Γ₀ A₀ B₀) (π₁ Γ₁ A₁ B₁) (π₁ Γ₁' A₁' B₁')
    rewrite Con₁-is-prop _ Γ₁ Γ₁'
          | Ty₁-is-prop _ A₁ A₁'
          | Ty₁-is-prop _ B₁ B₁' = refl

module GeneralEliminator
  (Conᴰ : Con -> Set)
  (Tyᴰ : {Γ : Con} -> Conᴰ Γ -> Ty Γ -> Set)
  (●ᴰ : Conᴰ ●)
  (_‣ᴰ_ : ∀{Γ A} (Γᴰ : Conᴰ Γ) -> Tyᴰ Γᴰ A -> Conᴰ (Γ ‣ A))
  (ιᴰ : {Γ : Con} (Γᴰ : Conᴰ Γ) -> Tyᴰ Γᴰ (ι Γ))
  (πᴰ : ∀{Γ A B} (Γᴰ : Conᴰ Γ) (Aᴰ : Tyᴰ Γᴰ A) (Bᴰ : Tyᴰ (Γᴰ ‣ᴰ Aᴰ) B)
     -> Tyᴰ Γᴰ (π Γ A B))
  where

  data R-Con : (Γ : Con) -> Conᴰ Γ -> Set
  data R-Ty : ∀{Γ} {Γᴰ : Conᴰ Γ} (A : Ty Γ) -> Tyᴰ Γᴰ A -> Set

  data R-Con where
    R-● : R-Con ● ●ᴰ
    R-‣ : {Γ : Con} {Γᴰ : Conᴰ Γ} {A : Ty Γ} {Aᴰ : Tyᴰ Γᴰ A}
        → R-Con Γ Γᴰ → R-Ty A Aᴰ
        → R-Con (Γ ‣ A) (Γᴰ ‣ᴰ Aᴰ)
    
  data R-Ty where
    R-ι : {Γ : Con} {Γᴰ : Conᴰ Γ}
        -> R-Con Γ Γᴰ
        -> R-Ty (ι Γ) (ιᴰ Γᴰ)
    R-π : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ‣ A)}
          {Γᴰ : Conᴰ Γ} {Aᴰ : Tyᴰ Γᴰ A} {Bᴰ : Tyᴰ (Γᴰ ‣ᴰ Aᴰ) B}
        → R-Con Γ Γᴰ → R-Ty A Aᴰ → R-Ty B Bᴰ
        → R-Ty (π Γ A B) (πᴰ Γᴰ Aᴰ Bᴰ)

  mutual
    e-Con : ∀{Γ₀} (Γ₁ : Con₁ Γ₀) -> Σ (Conᴰ (Γ₀ , Γ₁)) (R-Con (Γ₀ , Γ₁))
    e-Con ●₁ = ●ᴰ , R-●
    e-Con (Γ₁ ‣₁ A₁) = _ , R-‣ ih (snd (e-Ty A₁ ih))
      where ih = snd (e-Con Γ₁)
  
    e-Ty : ∀{Γ} {Γᴰ : Conᴰ Γ} {A₀ : Ty₀} (A₁ : Ty₁ (fst Γ) A₀) -> R-Con Γ Γᴰ -> Σ (Tyᴰ Γᴰ (A₀ , A₁)) (R-Ty (A₀ , A₁))
    e-Ty {Γ = Γ₀ , Γ₁} (ι₁ Γ₁') p rewrite Con₁-is-prop _ Γ₁ Γ₁' = _ , R-ι p
    e-Ty {Γ = Γ₀ , Γ₁} (π₁ Γ₁' A₁ B₁) p rewrite Con₁-is-prop _ Γ₁ Γ₁' =
      _ , R-π p ih (snd (e-Ty B₁ (R-‣ p ih)))
      where ih = snd (e-Ty A₁ p)

  elim-Con : (Γ : Con) -> Conᴰ Γ
  elim-Con Γ = fst (e-Con (snd Γ))

  elim-Ty : {Γ : Con} (A : Ty Γ) -> Tyᴰ (elim-Con Γ) A
  elim-Ty {Γ = Γ} A = fst (e-Ty (snd A) (snd (e-Con (snd Γ))))
