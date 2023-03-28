{-# OPTIONS --prop --without-K --rewriting #-}

module Setoid.Sets3.encoding-abbrev where

open import Setoid.lib
import Setoid.Sets3.encoding as E
import Setoid.Sets3.gen-elim as GE
open import Setoid.Sets3.mini-univ
open import Relation.Binary.PropositionalEquality

in-U : U -> Set₁
in-U = E.in-U

in-U~ : ∀{A₀ A₁} (a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : El A₀ -> El A₁ -> P) → Set₁
in-U~ = E.in-U~ _ _

record Std : Set₁ where
  inductive
  field
    ∣_∣ : U
    pf : in-U ∣_∣
    _~ : El ∣_∣ → El ∣_∣ → P
    pf~ : in-U~ pf pf _~
open Std public

record Std-Rel (A₀ A₁ : Std) : Set₁ where
  inductive
  field
    ∣_∣ : El ∣ A₀ ∣ → El ∣ A₁ ∣ → P
    pf : in-U~ (pf A₀) (pf A₁) ∣_∣
open Std-Rel public

record IxStd (S : Std) : Set₁ where
  inductive
  private
    A = ∣ S ∣
    A~ = S ~
  field
    ∣_∣ : El A → U
    pf : (x : _) → in-U (∣_∣ x)
    _~ : ∀{x₀ x₁} (x₀₁ : ElP (A~ x₀ x₁)) → El (∣_∣ x₀) → El (∣_∣ x₁) → P
    pf~ : ∀{x₀ x₁} (x₀₁ : ElP (A~ x₀ x₁)) → in-U~ (pf x₀) (pf x₁) (_~ x₀₁)
open IxStd public

record IxStd-Rel {A₀ A₁ : Std} (B₀ : IxStd A₀) (B₁ : IxStd A₁) (A₀₁ : Std-Rel A₀ A₁) : Set₁ where
  inductive
  field
    ∣_∣ : ∀{x₀ x₁}(x₀₁ : ElP (∣ A₀₁ ∣ x₀ x₁)) → El (∣ B₀ ∣ x₀) → El (∣ B₁ ∣ x₁) → P
    pf : {x₀ : _}{x₁ : _} → (x₀₁ : ElP (Std-Rel.∣_∣ A₀₁ x₀ x₁)) → in-U~ ((pf B₀) x₀) ((pf B₁) x₁) (∣_∣ x₀₁)
open IxStd-Rel public

bool : in-U 𝟚-U
bool = E.bool

π : (A : Std) → (B : IxStd A) → in-U (Σsp-U ∣ A ∣ ∣ B ∣ (A ~) (B ~))
π A B = E.π (pf A) (pf~ A) (pf B) (pf~ B)

bool~ : in-U~ bool bool (λ x₀ x₁ → x₀ ≟𝟚-P x₁)
bool~ = E.bool~

π~ : ∀{A₀ A₁ B₀ B₁} (A₀₁ : Std-Rel A₀ A₁) (B₀₁ : IxStd-Rel B₀ B₁ A₀₁)
   → in-U~ (π A₀ B₀) (π A₁ B₁) λ f₀ f₁ → fun-≡-P _ _ (∣ A₀₁ ∣) _ _ (∣ B₀₁ ∣) (proj₁sp f₀) (proj₁sp f₁)
π~ {A₀} {A₁} {B₀} {B₁} A₀₁ B₀₁ =
  E.π~ {a₀ = pf A₀} {a₀~ = pf~ A₀} {a₁ = pf A₁} {a₁~ = pf~ A₁} (pf A₀₁)
       {b₀ = pf B₀} {b₀~ = pf~ B₀} {b₁ = pf B₁} {b₁~ = pf~ B₁} (pf B₀₁)

open import Agda.Primitive

variable i j k l : Level

record GeneralData i j : Set (lsuc (i ⊔ j)) where
  field 
    in-Uᴰ : ∀{A} → in-U A → Set i
    in-U~ᴰ : ∀{A₀ A₁ a₀ a₁} {A₀₁ : El A₀ → El A₁ → P}
           → in-Uᴰ a₀ → in-Uᴰ a₁ → in-U~ a₀ a₁ A₀₁ → Set j
  Stdᴰ : Std → Set _
  Stdᴰ A = Σ (in-Uᴰ (pf A)) (λ aᴰ → in-U~ᴰ aᴰ aᴰ (pf~ A))
  IxStdᴰ : ∀ {A} → IxStd A → Set _
  IxStdᴰ {A} B = Σ ((x : _) → in-Uᴰ (pf B x)) λ bᴰ →
                   ∀{x₀ x₁}(x₀₁ : ElP ((A ~) x₀ x₁)) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (pf~ B x₀₁)
  Std-Relᴰ : ∀{A₀ A₁} → Stdᴰ A₀ → Stdᴰ A₁ → Std-Rel A₀ A₁ → Set _
  Std-Relᴰ A₀ᴰ A₁ᴰ R = in-U~ᴰ (proj₁ A₀ᴰ) (proj₁ A₁ᴰ) (pf R)
  IxStd-Relᴰ : ∀{A₀ A₁ B₀ B₁} {R : Std-Rel A₀ A₁} → IxStdᴰ B₀ → IxStdᴰ B₁ → IxStd-Rel B₀ B₁ R → Set _
  IxStd-Relᴰ B₀ᴰ B₁ᴰ R' = ∀ {x₀ x₁} x₀₁ → in-U~ᴰ (proj₁ B₀ᴰ x₀) (proj₁ B₁ᴰ x₁) (pf R' x₀₁)

  field
    boolᴰ : in-Uᴰ bool
    πᴰ : ∀{A B} → Stdᴰ A → IxStdᴰ B → in-Uᴰ (π A B)
    bool~ᴰ : in-U~ᴰ boolᴰ boolᴰ bool~
    π~ᴰ : ∀{A₀ A₁} {R : Std-Rel A₀ A₁} {B₀ : IxStd A₀} {B₁ : IxStd A₁} {R' : IxStd-Rel B₀ B₁ R}
        → (A₀ᴰ : Stdᴰ A₀) (A₁ᴰ : Stdᴰ A₁) (B₀ᴰ : IxStdᴰ B₀) (B₁ᴰ : IxStdᴰ B₁)
        → Std-Relᴰ A₀ᴰ A₁ᴰ R → IxStd-Relᴰ B₀ᴰ B₁ᴰ R'
        → in-U~ᴰ (πᴰ A₀ᴰ B₀ᴰ) (πᴰ A₁ᴰ B₁ᴰ) (π~ R R')

module general {i} {j} (dt : GeneralData i j) where

  open GeneralData dt

  open GE.general in-Uᴰ (λ a₀ᴰ a₁ᴰ x → in-U~ᴰ a₀ᴰ a₁ᴰ x)
    boolᴰ (λ aᴰ a~ᴰ bᴰ b~ᴰ → πᴰ (aᴰ ,Σ a~ᴰ) (bᴰ ,Σ b~ᴰ))
    bool~ᴰ (λ a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ b₀₁ᴰ
      → π~ᴰ (a₀ᴰ ,Σ a₀~ᴰ) (a₁ᴰ ,Σ a₁~ᴰ) (b₀ᴰ ,Σ b₀~ᴰ) (b₁ᴰ ,Σ b₁~ᴰ) a₀₁ᴰ b₀₁ᴰ)

  elim-U' : {A : U} (a : in-U A) → in-Uᴰ a
  elim-U' = elim-U

  elim-U~' : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}
            (a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (elim-U' a₀) (elim-U' a₁) a₀₁
  elim-U~' = elim-U~

  elim-Std : (A : Std) → Stdᴰ A
  elim-Std A = elim-U (pf A) ,Σ elim-U~ (pf~ A)

  elim-IxStd : ∀{A} (B : IxStd A) → IxStdᴰ B
  elim-IxStd B = _ ,Σ λ x₀₁ → elim-U~ (pf~ B x₀₁)

  elim-StdRel : ∀{A₀ A₁} (R : Std-Rel A₀ A₁) → Std-Relᴰ (elim-Std A₀) (elim-Std A₁) R
  elim-StdRel R = elim-U~ (pf R)

  elim-IxStdRel : ∀{A₀ A₁ B₀ B₁} {A₀₁ : Std-Rel A₀ A₁}
                → (B₀₁ : IxStd-Rel B₀ B₁ A₀₁) → IxStd-Relᴰ (elim-IxStd B₀) (elim-IxStd B₁) B₀₁
  elim-IxStdRel R' = λ x₀₁ → elim-U~ (pf R' x₀₁)

  bool-≡ : elim-U bool ≡ boolᴰ
  bool-≡ = refl

  π-≡ : ∀{A B} → elim-U (π A B) ≡ πᴰ (elim-Std A) (elim-IxStd B)
  π-≡ = refl

  bool~-≡ : elim-U~ bool~ ≡ bool~ᴰ
  bool~-≡ = refl

  π~-≡ : ∀{A₀ A₁ B₀ B₁} {A₀₁ : Std-Rel A₀ A₁} {B₀₁ : IxStd-Rel B₀ B₁ A₀₁}
       → elim-U~ (π~ A₀₁ B₀₁)
       ≡ π~ᴰ (elim-Std A₀) (elim-Std A₁) (elim-IxStd B₀) (elim-IxStd B₁)
             (elim-StdRel A₀₁) (elim-IxStdRel B₀₁)
  π~-≡ = refl

