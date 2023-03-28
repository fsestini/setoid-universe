{-# OPTIONS --prop --rewriting --without-K #-}

module Setoid.Sets.gen-elim where

open import Relation.Binary.PropositionalEquality -- Agda.Builtin.Equality
open import Agda.Primitive
open import Setoid.lib
open import Setoid.Sets.lib

withSet : ∀{i j}{A : Set i} {B : Set j} -> A -> (A -> B) -> B
withSet x f = f x

module general
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Set j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ aᴰ aᴰ a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → (B x₀) → (B x₁) → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ boolᴰ boolᴰ bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → (B₀ x₀) → (B₀ x₁) → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → (B₁ x₀) → (B₁ x₁) → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → (B₀ x₀) → (B₁ x₁) → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)) → 
    in-U~ᴰ (πᴰ a₀ᴰ a₀~ᴰ b₀ᴰ b₀~ᴰ) (πᴰ a₁ᴰ a₁~ᴰ b₁ᴰ b₁~ᴰ) (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁))
  where

  data R-U : {A : Set} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> in-Uᴰ (aₚ ,sp aₜ) -> Set (lsuc (i ⊔ j))
  data R-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (a₀₁ : in-U~ a₀ a₁ A₀₁)
            → in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁ -> Set (lsuc i ⊔ lsuc j)

  data R-U where
    R-bool : R-U boolₚ boolₜ boolᴰ
    R-π :
      {A : Set}{aₚ : in-Uₚ A}{aₜ : in-Uₜ aₚ}{aᴰ : in-Uᴰ (aₚ ,sp aₜ)}(R-a : R-U aₚ aₜ aᴰ)
      {A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}{a~ₜ : in-U~ₜ aₚ aₚ a~ₚ}
        {a~ᴰ : in-U~ᴰ aᴰ aᴰ (a~ₚ ,sp a~ₜ)}(R-a~ : R-U~ (a~ₚ ,sp a~ₜ) a~ᴰ)
      {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}{bₜ : (x : A) → in-Uₜ (bₚ x)}
        {bᴰ : (x : A) → in-Uᴰ (bₚ x ,sp bₜ x)}(R-b : (x : A) -> R-U (bₚ x) (bₜ x) (bᴰ x))
      {B~ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → (B x₀) → (B x₁) → Prop}
        {b~ₚ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ₚ (B~ x₀₁)}
        {b~ₜ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)}
        {b~ᴰ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ₚ x₀₁ ,sp b~ₜ x₀₁)}
      (R-B~ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → R-U~ (b~ₚ x₀₁ ,sp b~ₜ x₀₁) (b~ᴰ x₀₁))
      → R-U {(Σsp ((x : A) → B x)
                 (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))}
                 (πₚ aₚ a~ₚ bₚ b~ₚ) (πₜ aₜ a~ₜ bₜ b~ₜ) (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ)

  data R-U~ where
    R-bool~ : R-U~ bool~ bool~ᴰ
    R-π~ : {A₀ : Set}{a₀ : in-U A₀}{a₀ᴰ : in-Uᴰ a₀}(R-a₀ : R-U (proj₁sp a₀) (proj₂sp a₀) a₀ᴰ)
           {A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}{a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~}(R-a₀~ : R-U~ a₀~ a₀~ᴰ)
           {A₁ : Set}{a₁ : in-U A₁}{a₁ᴰ : in-Uᴰ a₁}(R-a₁ : R-U (proj₁sp a₁) (proj₂sp a₁) a₁ᴰ)
           {A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}{a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~}(R-a₁~ : R-U~ a₁~ a₁~ᴰ)
           {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}{a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁}(R-a₀₁ : R-U~ a₀₁ a₀₁ᴰ)
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀)}(R-b₀ : (x : _) -> R-U (proj₁sp (b₀ x)) (proj₂sp (b₀ x)) (b₀ᴰ x))

           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → (B₀ x₀) → (B₀ x₁) → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁)}
           (R-b₀~ : {x₀ x₁ : A₀}(x₀₁ : (A₀~ x₀ x₁)) → R-U~ (b₀~ x₀₁) (b₀~ᴰ x₀₁))
           
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁)}(R-b₁ : (x₁ : A₁) → R-U (proj₁sp (b₁ x₁)) (proj₂sp (b₁ x₁)) (b₁ᴰ x₁))

           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → (B₁ x₀) → (B₁ x₁) → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
           {b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁)}
           (R-b₁~ : {x₀ x₁ : A₁}(x₀₁ : (A₁~ x₀ x₁)) → R-U~ (b₁~ x₀₁) (b₁~ᴰ x₀₁))
           
           {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → (B₀ x₀) → (B₁ x₁) → Prop}
           {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
           {b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)}
           (R-b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : (A₀₁ x₀ x₁)) → R-U~ (b₀₁ x₀₁) (b₀₁ᴰ x₀₁))
        → R-U~
            (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
            (π~ᴰ a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ b₀₁ᴰ)

  invert : ∀{i}{Q : Set i}{A : Set}{aₚ : in-Uₚ A}{aₜ : in-Uₜ aₚ}
           {A~ : A → A → Prop}{a~ₚ : in-U~ₚ A~}{a~ₜ : in-U~ₜ aₚ aₚ a~ₚ}
           {B : A → Set}{bₚ : (x : A) → in-Uₚ (B x)}{bₜ : (x : A) → in-Uₜ (bₚ x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → (B x₀) → (B x₁) → Prop}
             {b~ₚ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ₚ (B~ x₀₁)}
             {b~ₜ : {x₀ x₁ : A}(x₀₁ : (A~ x₀ x₁)) → in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)}
         → {x : in-Uᴰ (πₚ aₚ a~ₚ bₚ b~ₚ ,sp πₜ aₜ a~ₜ bₜ b~ₜ)}
         → R-U {(Σsp ((x : A) → B x)
                 (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))}
               (πₚ aₚ a~ₚ bₚ {B~ = B~} b~ₚ) (πₜ aₜ a~ₜ bₜ b~ₜ) x
         → ({aᴰ : _} {a~ᴰ : _} {bᴰ : (x : _) -> _} {b~ᴰ : {x₀ x₁ : _} (x₀₁ : (A~ x₀ x₁)) → _}
             -> R-U aₚ aₜ aᴰ
             -> R-U~ (a~ₚ ,sp a~ₜ) a~ᴰ
             -> ((x : _) -> R-U (bₚ x) (bₜ x) (bᴰ x))
             -> ({x₀ x₁ : A} (x₀₁ : (A~ x₀ x₁)) → R-U~ (b~ₚ x₀₁ ,sp b~ₜ x₀₁) (b~ᴰ x₀₁))
             -> (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ) ≡ x
             -> Q)
         → Q
  invert (R-π R-a R-a~ R-b R-b~) f = f R-a R-a~ R-b R-b~ refl

  exists-U : {A : Set} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> Σ (in-Uᴰ (aₚ ,sp aₜ)) (R-U aₚ aₜ)
  exists-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (p₀ : R-U (proj₁sp a₀) (proj₂sp a₀) a₀ᴰ) (p₁ : R-U (proj₁sp a₁) (proj₂sp a₁) a₁ᴰ)
              (a₀₁ₚ : in-U~ₚ A₀₁) (a₀₁ₜ : in-U~ₜ (proj₁sp a₀) (proj₁sp a₁) a₀₁ₚ)
            → Σ (in-U~ᴰ a₀ᴰ a₁ᴰ (a₀₁ₚ ,sp a₀₁ₜ)) (R-U~ (a₀₁ₚ ,sp a₀₁ₜ))

  exists-U boolₚ aₜ = _ ,Σ R-bool
  exists-U (πₚ aₚ a~ₚ bₚ b~ₚ) p = _ ,Σ
    R-π ih-a (proj₂ (exists-U~ ih-a ih-a a~ₚ a~ₜ))
        ih-b (λ x₀₁ → proj₂ (exists-U~ (ih-b _) (ih-b _) (b~ₚ x₀₁) (b~ₜ x₀₁)))
    where
      aₜ : in-Uₜ aₚ
      aₜ = withProp p λ { (πₜ x _ _ _) → x }
      a~ₜ : in-U~ₜ aₚ aₚ a~ₚ
      a~ₜ = withProp p λ { (πₜ _ x _ _) → x }
      ih-a = proj₂ (exists-U aₚ aₜ)
      bₜ : (x : _) -> in-Uₜ (bₚ x)
      bₜ x = withProp p λ { (πₜ _ _ f _) → f x }
      ih-b : (x : _) -> _
      ih-b x = proj₂ (exists-U (bₚ x) (bₜ x))
      b~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)
      b~ₜ xx = withProp p λ { (πₜ _ _ _ f) → f xx }

  exists-U~ {a₀ = a₀} {a₁} {a₀ᴰ = a₀ᴰ} {a₁ᴰ} p₀ p₁ bool~ₚ p =
    goal (to-≡ (withProp p (λ { bool~ₜ → reflp })))
         (to-≡ (withProp p (λ { bool~ₜ → reflp })))
    where
      goal : a₀ ≡ bool -> a₁ ≡ bool -> Σ (in-U~ᴰ a₀ᴰ a₁ᴰ (bool~ₚ ,sp p)) (R-U~ _)
      goal refl refl = withSet p₀ λ { R-bool → withSet p₁ λ { R-bool → _ ,Σ R-bool~ } }

  exists-U~ {a₀ = pi₀} {pi₁} {a₀ᴰ = pi₀ᴰ} {pi₁ᴰ} p₀ p₁
    (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ) p =
    goal eq1 eq2
    where
      a₀ₜ : in-Uₜ a₀ₚ
      a₀ₜ = withProp p λ { (π~ₜ x _ _ _ _ _ _ _ _ _) → x }
      a₀~ₜ = withProp p λ { (π~ₜ _ x _ _ _ _ _ _ _ _) → x }
      b₀ₜ : (x : _) -> in-Uₜ (b₀ₚ x)
      b₀ₜ = withProp p λ { (π~ₜ _ _ _ _ _ x _ _ _ _) → x }
      b₀~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁)
      b₀~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ x _ _ _) → x }

      eq1 : pi₀ ≡ π (a₀ₚ ,sp a₀ₜ) (a₀~ₚ ,sp a₀~ₜ)
                    (λ x → b₀ₚ x ,sp b₀ₜ x) λ x₀₁ → b₀~ₚ x₀₁ ,sp b₀~ₜ x₀₁
      eq1 = to-≡ (withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ _) → reflp })

      a₁ₜ = withProp p λ { (π~ₜ _ _ x _ _ _ _ _ _ _) → x }
      a₁~ₜ = withProp p λ { (π~ₜ _ _ _ x _ _ _ _ _ _) → x }
      b₁ₜ : (x : _) -> in-Uₜ (b₁ₚ x)
      b₁ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ x _ _) → x }
      b₁~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁)
      b₁~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ x _) → x }

      a₀₁ₜ : in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ
      a₀₁ₜ = (withProp p (λ { (π~ₜ _ _ _ _ x _ _ _ _ _) → x }))

      b₀₁ₜ : ∀{x₀ x₁} (x₀₁ : _) → in-U~ₜ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)
      b₀₁ₜ = withProp p (λ { (π~ₜ _ _ _ _ _ _ _ _ _ x) → x })

      eq2 : pi₁ ≡ π (a₁ₚ ,sp a₁ₜ) (a₁~ₚ ,sp a₁~ₜ)
                    (λ x → b₁ₚ x ,sp b₁ₜ x) (λ x₀₁ → b₁~ₚ x₀₁ ,sp b₁~ₜ x₀₁)
      eq2 = to-≡ (withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ _) → reflp })

      ty : in-Uᴰ pi₀ → in-Uᴰ pi₁ → Set _
      ty x y = Σ (in-U~ᴰ x y (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp p)) (R-U~ (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ ,sp p))

      goal : pi₀ ≡ π (a₀ₚ ,sp a₀ₜ) (a₀~ₚ ,sp a₀~ₜ)
                     (λ x → b₀ₚ x ,sp b₀ₜ x) (λ x₀₁ → b₀~ₚ x₀₁ ,sp b₀~ₜ x₀₁)
           → pi₁ ≡ π (a₁ₚ ,sp a₁ₜ) (a₁~ₚ ,sp a₁~ₜ)
                    (λ x → b₁ₚ x ,sp b₁ₜ x) (λ x₀₁ → b₁~ₚ x₀₁ ,sp b₁~ₜ x₀₁)
           → ty pi₀ᴰ pi₁ᴰ
      goal refl refl =
        invert {aₜ = a₀ₜ} {a~ₜ = a₀~ₜ} {bₜ = b₀ₜ} {b~ₜ = b₀~ₜ} p₀ λ {aᴰ} {a~ᴰ} {bᴰ} {b~ᴰ} R-a R-a~ R-b R-b~ e →
          invert {aₜ = a₁ₜ} {a~ₜ = a₁~ₜ} {bₜ = b₁ₜ} {b~ₜ = b₁~ₜ} p₁ λ R-a' R-a~' R-b' R-b~' e' →
            subst (λ x → ty x pi₁ᴰ) e (subst (λ x → ty (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ) x) e'
              (_ ,Σ (R-π~ R-a R-a~ R-a' R-a~' (proj₂ (exists-U~ R-a R-a' a₀₁ₚ a₀₁ₜ)) R-b R-b~ R-b' R-b~' (λ x₀₁ → proj₂ (exists-U~ (R-b _) (R-b' _) (b₀₁ₚ x₀₁) (b₀₁ₜ x₀₁))))))

  elim-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  elim-in-U (aₚ ,sp aₜ) = proj₁ (exists-U aₚ aₜ)
  
  elim-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (elim-in-U a₀) (elim-in-U a₁) a₀₁
  elim-in-U~ (a₀₁ₚ ,sp a₀₁ₜ) = proj₁ (exists-U~ (proj₂ (exists-U _ _)) (proj₂ (exists-U _ _)) a₀₁ₚ a₀₁ₜ)

  bool-β : elim-in-U bool ≡ boolᴰ
  bool-β = refl

  π-β :
    {A : Set}(a : in-U A){A~ : A -> A -> Prop}(a~ : in-U~ a a A~)
    {B : A -> Set}
    (b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ :  (A~ x₀ x₁)) → (B x₀) → (B x₁) → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ :  (A~ x₀ x₁)) → in-U~ (b x₀) (b x₁) (B~ x₀₁))
    → elim-in-U (π a a~ b b~)
    ≡ πᴰ (elim-in-U a) (elim-in-U~ a~) (λ x → elim-in-U (b x)) (λ x₀₁ → elim-in-U~ (b~ x₀₁))
  π-β a a~ b b~ = refl

  bool~-β : elim-in-U~ bool~ ≡ bool~ᴰ
  bool~-β = refl

  π~-β : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
       {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
       {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)
  
       {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
         {B₀~ : {x₀ x₁ : A₀}(x₀₁ :  (A₀~ x₀ x₁)) → (B₀ x₀) → (B₀ x₁) → Prop}
         {b₀~ : {x₀ x₁ : A₀}(x₀₁ :  (A₀~ x₀ x₁)) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
       {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
         {B₁~ : {x₀ x₁ : A₁}(x₀₁ :  (A₁~ x₀ x₁)) → (B₁ x₀) → (B₁ x₁) → Prop}
         {b₁~ : {x₀ x₁ : A₁}(x₀₁ :  (A₁~ x₀ x₁)) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
       {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ :  (A₀₁ x₀ x₁)) → (B₀ x₀) → (B₁ x₁) → Prop}
       (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ :  (A₀₁ x₀ x₁)) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁))
     → elim-in-U~ (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁
                     {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
     ≡ π~ᴰ (elim-in-U a₀) (elim-in-U~ a₀~) (elim-in-U a₁) (elim-in-U~ a₁~) (elim-in-U~ a₀₁)
           (λ x₀ → elim-in-U (b₀ x₀)) (λ x₀₁ → elim-in-U~ (b₀~ x₀₁)) (λ x₁ → elim-in-U (b₁ x₁)) (λ x₀₁ → elim-in-U~ (b₁~ x₀₁)) λ x₀₁ → elim-in-U~ (b₀₁ x₀₁)
  π~-β a₀₁ b₀₁ = refl
