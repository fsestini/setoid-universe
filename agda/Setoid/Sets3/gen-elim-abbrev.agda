{-# OPTIONS --prop --rewriting #-}

module Setoid.Sets3.gen-elim-abbrev where

open import Setoid.lib
open import Setoid.Sets3.mini-univ
open import Setoid.Sets3.encoding-abbrev
open import Relation.Binary.PropositionalEquality -- Agda.Builtin.Equality
open import Agda.Primitive
open import irrel-eq

variable i j k l : Level

withProp : {P : Prop i} {Q : Prop j} -> P -> (P -> Q) -> Q
withProp p f = f p

withSet : {A : Set i} {B : Set j} -> A -> (A -> B) -> B
withSet x f = f x

subst-T : {A B : Set i} -> A ≡ B -> A -> B
subst-T refl x = x

-- subst : {A : Set i} (C : A -> Set j) {x y : A} -> x ≡ y -> C x -> C y
-- subst _ refl x = x

withP : {P : Prop j} {Q : Prop k} {A : Set i} (x y : A)
      → P
      → (P -> x ≡p y)
      → (x ≡ y -> Q)
      → Q
withP x y p f g = g (to-≡ (f p))

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

  data R-U : ∀{A} (a : in-U A) -> in-Uᴰ a -> Set (lsuc (i ⊔ j))
  data R-U~ : ∀{A₀ A₁ a₀ a₁} {A₀₁ : El A₀ → El A₁ → P}
              (a₀ᴰ : in-Uᴰ a₀) (a₁ᴰ : in-Uᴰ a₁) (a₀₁ : in-U~ a₀ a₁ A₀₁)
            → in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁ -> Set (lsuc (i ⊔ j))

  R-Std : (A : Std) → Stdᴰ A → Set _
  R-Std A Aᴰ = R-U (pf A) (proj₁ Aᴰ) × R-U~ _ _ (pf~ A) (proj₂ Aᴰ)

  R-IxStd : ∀{A} (B : IxStd A) → IxStdᴰ B → Set _
  R-IxStd B Bᴰ = (∀ x → R-U (pf B x) (proj₁ Bᴰ x)) × (∀{x₀ x₁} x₀₁ → R-U~ (proj₁ Bᴰ x₀) (proj₁ Bᴰ x₁) (pf~ B x₀₁) (proj₂ Bᴰ x₀₁))

  R-StdRel : ∀{A₀ A₁} A₀ᴰ A₁ᴰ (R : Std-Rel A₀ A₁) → Std-Relᴰ A₀ᴰ A₁ᴰ R → Set _
  R-StdRel _ _ R Rᴰ = R-U~ _ _ (pf R) Rᴰ

  R-IxStdRel : ∀{A₀ A₁ B₀ B₁} B₀ᴰ B₁ᴰ {R : Std-Rel A₀ A₁}
             → (R' : IxStd-Rel B₀ B₁ R) → IxStd-Relᴰ B₀ᴰ B₁ᴰ R' → Set _
  R-IxStdRel B₀ᴰ B₁ᴰ R' R'ᴰ = ∀{x₀ x₁} x₀₁ → R-U~ (proj₁ B₀ᴰ x₀) (proj₁ B₁ᴰ x₁) (pf R' x₀₁) (R'ᴰ x₀₁)

  data R-U where
    R-bool : R-U bool boolᴰ
    R-π : ∀{A Aᴰ B Bᴰ} → R-Std A Aᴰ → R-IxStd B Bᴰ → R-U (π A B) (πᴰ Aᴰ Bᴰ)

  data R-U~ where
    R-bool~ : R-U~ boolᴰ boolᴰ bool~ bool~ᴰ
    R-π~ : ∀{A₀ A₁} {R : Std-Rel A₀ A₁} {B₀ : IxStd A₀} {B₁ : IxStd A₁} {R' : IxStd-Rel B₀ B₁ R}
           → {A₀ᴰ : Stdᴰ A₀} {A₁ᴰ : Stdᴰ A₁} {B₀ᴰ : IxStdᴰ B₀} {B₁ᴰ : IxStdᴰ B₁}
           → {Rᴰ : Std-Relᴰ A₀ᴰ A₁ᴰ R} {R'ᴰ : IxStd-Relᴰ B₀ᴰ B₁ᴰ R'}
           → R-Std A₀ A₀ᴰ → R-Std A₁ A₁ᴰ → R-IxStd B₀ B₀ᴰ → R-IxStd B₁ B₁ᴰ
           → R-StdRel A₀ᴰ A₁ᴰ R Rᴰ
           → R-IxStdRel B₀ᴰ B₁ᴰ R' R'ᴰ -- (∀{x₀ x₁} x₀₁ → R-U~ (proj₁ B₀ᴰ x₀) (proj₁ B₁ᴰ x₁) (pf R' x₀₁) (R'ᴰ x₀₁))
           → R-U~ (πᴰ A₀ᴰ B₀ᴰ) (πᴰ A₁ᴰ B₁ᴰ) (π~ R R') (π~ᴰ A₀ᴰ A₁ᴰ B₀ᴰ B₁ᴰ Rᴰ R'ᴰ)

  exists-U : {A : U} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> Σ (in-Uᴰ (aₚ ,sp aₜ)) (R-U (aₚ ,sp aₜ))
  exists-U~ : ∀{A₀ A₁} {a₀ : in-U A₀} {a₁ A₀₁} {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (p₀ : R-U a₀ a₀ᴰ) (p₁ : R-U a₁ a₁ᴰ)
              (a₀₁ₚ : in-U~ₚ A₀ A₁ A₀₁) (a₀₁ₜ : in-U~ₜ (proj₁sp a₀) (proj₁sp a₁) a₀₁ₚ)
            → Σ (in-U~ᴰ a₀ᴰ a₁ᴰ (a₀₁ₚ ,sp a₀₁ₜ)) (R-U~ a₀ᴰ a₁ᴰ (a₀₁ₚ ,sp a₀₁ₜ))

  exists-Std : (A : Std) → Σ (Stdᴰ A) (R-Std A)
  exists-IxStd : ∀{A Aᴰ} → R-Std A Aᴰ → (B : IxStd A) → Σ _ (R-IxStd B)
  exists-StdRel : ∀{A₀ A₁ A₀ᴰ A₁ᴰ} → R-Std A₀ A₀ᴰ → R-Std A₁ A₁ᴰ
                  → (R : Std-Rel A₀ A₁) → Σ (Std-Relᴰ A₀ᴰ A₁ᴰ R) (R-StdRel A₀ᴰ A₁ᴰ R)
  exists-IxStdRel : ∀{A₀ A₁ B₀ B₁ B₀ᴰ B₁ᴰ}
                  → R-IxStd B₀ B₀ᴰ → R-IxStd B₁ B₁ᴰ -- R-Std A₀ A₀ᴰ → R-Std A₁ A₁ᴰ
                  → {R : Std-Rel A₀ A₁}
                  → (R' : IxStd-Rel B₀ B₁ R)
                  → Σ (IxStd-Relᴰ B₀ᴰ B₁ᴰ R') (R-IxStdRel B₀ᴰ B₁ᴰ R')

  {-# TERMINATING #-}
  exists-Std A = _ ,Σ (proj₂ aux ,Σ proj₂ aux')
    where aux = exists-U _ (proj₂sp (pf A))
          aux' = exists-U~ (proj₂ aux) (proj₂ aux) _ (proj₂sp (pf~ A))

  exists-IxStd r b = (λ x → proj₁ (aux x)) ,Σ (λ x₀₁ → proj₁ (aux' x₀₁)) ,Σ
                     ((λ x → proj₂ (aux x)) ,Σ λ x₀₁ → proj₂ (aux' x₀₁))
    where
      aux = λ x → exists-U _ (proj₂sp (pf b x))
      aux' = λ{x₀ x₁} x₀₁ → exists-U~ (proj₂ (aux x₀)) (proj₂ (aux x₁)) _ (proj₂sp (pf~ b x₀₁))

  exists-StdRel x y R = exists-U~ (proj₁ x) (proj₁ y) (proj₁sp (pf R)) (proj₂sp (pf R))

  exists-IxStdRel x y R' = (λ x₀₁ → proj₁ (ih x₀₁)) ,Σ λ x₀₁ → proj₂ (ih x₀₁)
    where ih = λ{x₀ x₁} x₀₁ → exists-U~ (proj₁ x x₀) (proj₁ y x₁) (proj₁sp (pf R' x₀₁)) (proj₂sp (pf R' x₀₁))

  exists-U boolₚ aₜ = _ ,Σ R-bool
  exists-U (πₚ A B) aₜ = _ ,Σ R-π (proj₂ ih) (proj₂ ih')
    where
      ih = exists-Std (to-Std A {!!})
      ih' = exists-IxStd (proj₂ ih) (to-IxStd {!!} B {!!})

  inv-π~ : ∀{A₀ₚ A₁ₚ B₀ₚ B₁ₚ A₀₁ B₀₁ x y}
         → in-U~ₜ x y (π~ₚ {A₀ₚ} {A₁ₚ} {B₀ₚ} {B₁ₚ} A₀₁ B₀₁)
         → (x ≡p πₚ A₀ₚ B₀ₚ) ×p (y ≡p πₚ A₁ₚ B₁ₚ)
  inv-π~ (π~ₜ _ _ _ _ _ _) = reflp ,p reflp

  exists-U~ R-bool R-bool bool~ₚ a₀₁ₜ = _ ,Σ R-bool~
  exists-U~ (R-π {A₀'} {A₀ᴰ} {B₀} {B₀ᴰ} ra₀ rb₀)
            (R-π {A₁'} {A₁ᴰ} {B₁} {B₁ᴰ} ra₁ rb₁)
            (π~ₚ {A₀ₚ} {A₁ₚ} {B₀ₚ} {B₁ₚ} A₀₁ B₀₁) a₀₁ₜ =
              goal (to-≡ (proj₁p (inv-π~ a₀₁ₜ))) (to-≡ (proj₂p (inv-π~ a₀₁ₜ)))
    where
      goal : _ → _ → Σ (in-U~ᴰ {a₀ = π A₀' B₀} {π A₁' B₁} (πᴰ A₀ᴰ B₀ᴰ) (πᴰ A₁ᴰ B₁ᴰ) (π~ₚ {A₀ₚ} {A₁ₚ} {B₀ₚ} {B₁ₚ} A₀₁ B₀₁ ,sp _)) (R-U~ (πᴰ A₀ᴰ B₀ᴰ) (πᴰ A₁ᴰ B₁ᴰ) (π~ₚ A₀₁ B₀₁ ,sp _))
      goal refl refl =
        π~ᴰ {A₀'} {A₁'} {R} {B₀} {B₁} {R'} A₀ᴰ A₁ᴰ B₀ᴰ B₁ᴰ (proj₁ ih-R) (proj₁ ih-R') ,Σ
        R-π~ ra₀ ra₁ rb₀ rb₁ (proj₂ ih-R) (proj₂ ih-R')
        where
          A₀ₜ = withProp a₀₁ₜ (λ {(π~ₜ x _ _ _ _ _) → x})
          A₁ₜ = withProp a₀₁ₜ (λ {(π~ₜ _ y _ _ _ _) → y})
          A₀₁ₜ = withProp a₀₁ₜ (λ {(π~ₜ _ _ _ _ x _) → x})
          B₀₁ₜ = withProp a₀₁ₜ (λ {(π~ₜ _ _ _ _ _ y) → y})
          R : Std-Rel A₀' A₁'
          R = to-StdRel A₀ₜ A₁ₜ A₀₁ A₀₁ₜ
          ih-R = exists-StdRel ra₀ ra₁ R
          R' : IxStd-Rel B₀ B₁ R
          R' = to-IxStdRel B₀₁ ? -- B₀₁ₜ
          ih-R' = exists-IxStdRel rb₀ rb₁ R'

  elim-U : {A : U} (a : in-U A) → in-Uᴰ a
  elim-U a = proj₁ (exists-U (proj₁sp a) (proj₂sp a))

  elim-U~ : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}
            (a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (elim-U a₀) (elim-U a₁) a₀₁
  elim-U~ a~ = proj₁ (exists-U~ (proj₂ (exists-U _ _)) (proj₂ (exists-U _ _)) (proj₁sp a~) (proj₂sp a~))

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
