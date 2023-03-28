{-# OPTIONS --prop --rewriting --without-K #-}

module Setoid.Sets3.gen-elim where

open import Setoid.lib
open import Setoid.Sets3.mini-univ
open import Setoid.Sets3.encoding
open import Relation.Binary.PropositionalEquality -- Agda.Builtin.Equality
open import Agda.Primitive
open import irrel-eq public

variable i j k l : Level

withProp : {P : Prop i} {Q : Prop j} -> P -> (P -> Q) -> Q
withProp p f = f p

withSet : {A : Set i} {B : Set j} -> A -> (A -> B) -> B
withSet x f = f x

subst-T : {A B : Set i} -> A ≡ B -> A -> B
subst-T refl x = x

withP : {P : Prop j} {Q : Prop k} {A : Set i} (x y : A)
      → P
      → (P -> x ≡p y)
      → (x ≡ y -> Q)
      → Q
withP x y p f g = g (to-≡ (f p))

module general
  {i}
  {j}
  (in-Uᴰ : ∀{A : U} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : U}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₀₁ : El A₀ → El A₁ → P} → in-U~ A₀ A₁ a₀ a₁ A₀₁ → Set j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : U}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : El A → El A → P}{a~ : in-U~ A A a a A~}(a~ᴰ : in-U~ᴰ aᴰ aᴰ a~)
    {B : El A → U}{b : (x : El A) → in-U (B x)}(bᴰ : (x : El A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
    {b~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ _ _ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ boolᴰ boolᴰ bool~)
  (π~ᴰ : {A₀ : U}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : El A₀ → El A₀ → P}{a₀~ : in-U~ _ _ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~)
    {A₁ : U}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : El A₁ → El A₁ → P}{a₁~ : in-U~ _ _ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~)
    {A₀₁ : El A₀ → El A₁ → P}{a₀₁ : in-U~ _ _ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁)
    {B₀ : El A₀ → U}{b₀ : (x₀ : El A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : El A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → El (B₀ x₀) → El (B₀ x₁) → P}
      {b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ _ _ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁))
    {B₁ : El A₁ → U}{b₁ : (x₁ : El A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : El A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → El (B₁ x₀) → El (B₁ x₁) → P}
      {b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ _ _ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁))
    {B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P}
    {b₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ _ _ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)) → 
    in-U~ᴰ (πᴰ a₀ᴰ a₀~ᴰ b₀ᴰ b₀~ᴰ) (πᴰ a₁ᴰ a₁~ᴰ b₁ᴰ b₁~ᴰ) (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁))
  where

  data R-U : {A : U} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> in-Uᴰ (aₚ ,sp aₜ) -> Set (lsuc (i ⊔ j))
  data R-U~ : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (a₀₁ : in-U~ A₀ A₁ a₀ a₁ A₀₁)
            → in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁ -> Set (lsuc i ⊔ lsuc j)

  data R-U where
    R-bool : R-U boolₚ boolₜ boolᴰ
    R-π :
      {A : U}{aₚ : in-Uₚ A}{aₜ : in-Uₜ aₚ}{aᴰ : in-Uᴰ (aₚ ,sp aₜ)}(R-a : R-U aₚ aₜ aᴰ)
      {A~ : El A → El A → P}{a~ₚ : in-U~ₚ A A A~}{a~ₜ : in-U~ₜ A A aₚ aₚ a~ₚ}
        {a~ᴰ : in-U~ᴰ aᴰ aᴰ (a~ₚ ,sp a~ₜ)}(R-a~ : R-U~ (a~ₚ ,sp a~ₜ) a~ᴰ)
      {B : El A → U}{bₚ : (x : El A) → in-Uₚ (B x)}{bₜ : (x : El A) → in-Uₜ (bₚ x)}
        {bᴰ : (x : El A) → in-Uᴰ (bₚ x ,sp bₜ x)}(R-b : (x : El A) -> R-U (bₚ x) (bₜ x) (bᴰ x))
      {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
        {b~ₚ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ _ _ (B~ x₀₁)}
        {b~ₜ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₜ _ _ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)}
        {b~ᴰ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ₚ x₀₁ ,sp b~ₜ x₀₁)}
      (R-B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → R-U~ (b~ₚ x₀₁ ,sp b~ₜ x₀₁) (b~ᴰ x₀₁))
      → R-U (πₚ aₚ a~ₚ bₚ b~ₚ) (πₜ aₜ a~ₜ bₜ b~ₜ) (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ)

  data R-U~ where
    R-bool~ : R-U~ bool~ bool~ᴰ
    R-π~ : {A₀ : U}{a₀ : in-U A₀}{a₀ᴰ : in-Uᴰ a₀}(R-a₀ : R-U (proj₁sp a₀) (proj₂sp a₀) a₀ᴰ)
           {A₀~ : El A₀ → El A₀ → P}{a₀~ : in-U~ _ _ a₀ a₀ A₀~}{a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~}(R-a₀~ : R-U~ a₀~ a₀~ᴰ)
           {A₁ : U}{a₁ : in-U A₁}{a₁ᴰ : in-Uᴰ a₁}(R-a₁ : R-U (proj₁sp a₁) (proj₂sp a₁) a₁ᴰ)
           {A₁~ : El A₁ → El A₁ → P}{a₁~ : in-U~ _ _ a₁ a₁ A₁~}{a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~}(R-a₁~ : R-U~ a₁~ a₁~ᴰ)
           {A₀₁ : El A₀ → El A₁ → P}{a₀₁ : in-U~ _ _ a₀ a₁ A₀₁}{a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁}(R-a₀₁ : R-U~ a₀₁ a₀₁ᴰ)
           {B₀ : El A₀ → U}{b₀ : (x₀ : El A₀) → in-U (B₀ x₀)}{b₀ᴰ : (x₀ : El A₀) → in-Uᴰ (b₀ x₀)}(R-b₀ : (x : _) -> R-U (proj₁sp (b₀ x)) (proj₂sp (b₀ x)) (b₀ᴰ x))

           {B₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → El (B₀ x₀) → El (B₀ x₁) → P}
           {b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ _ _ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {b₀~ᴰ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁)}
           (R-b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → R-U~ (b₀~ x₀₁) (b₀~ᴰ x₀₁))
           
           {B₁ : El A₁ → U}{b₁ : (x₁ : El A₁) → in-U (B₁ x₁)}{b₁ᴰ : (x₁ : El A₁) → in-Uᴰ (b₁ x₁)}(R-b₁ : (x₁ : El A₁) → R-U (proj₁sp (b₁ x₁)) (proj₂sp (b₁ x₁)) (b₁ᴰ x₁))

           {B₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → El (B₁ x₀) → El (B₁ x₁) → P}
           {b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ _ _ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
           {b₁~ᴰ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁)}
           (R-b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → R-U~ (b₁~ x₀₁) (b₁~ᴰ x₀₁))
           
           {B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P}
           {b₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ _ _ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
           {b₀₁ᴰ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)}
           (R-b₀₁ᴰ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → R-U~ (b₀₁ x₀₁) (b₀₁ᴰ x₀₁))
        → R-U~
            (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁ {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
            (π~ᴰ a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ b₀₁ᴰ)

  invert : ∀{i}{Q : Set i}{A : U}{aₚ : in-Uₚ A}{aₜ : in-Uₜ aₚ}
           {A~ : El A → El A → P}{a~ₚ : in-U~ₚ A A A~}{a~ₜ : in-U~ₜ A A aₚ aₚ a~ₚ}
           {B : El A → U}{bₚ : (x : El A) → in-Uₚ (B x)}{bₜ : (x : El A) → in-Uₜ (bₚ x)}
           {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
             {b~ₚ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ _ _ (B~ x₀₁)}
             {b~ₜ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₜ _ _ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)}
         → {x : _}
         → R-U {Σsp-U A B A~ B~} (πₚ aₚ a~ₚ bₚ b~ₚ) (πₜ aₜ a~ₜ bₜ b~ₜ) x
         → ({aᴰ : _} {a~ᴰ : _} {bᴰ : (x : _) -> _} {b~ᴰ : {x₀ x₁ : _} (x₀₁ : ElP (A~ x₀ x₁)) → _}
             -> R-U aₚ aₜ aᴰ
             -> R-U~ (a~ₚ ,sp a~ₜ) a~ᴰ
             -> ((x : _) -> R-U (bₚ x) (bₜ x) (bᴰ x))
             -> ({x₀ x₁ : El A} (x₀₁ : ElP (A~ x₀ x₁)) → R-U~ (b~ₚ x₀₁ ,sp b~ₜ x₀₁) (b~ᴰ x₀₁))
             -> (πᴰ aᴰ a~ᴰ bᴰ b~ᴰ) ≡ x
             -> Q)
         → Q
  invert (R-π R-a R-a~ R-b R-b~) f = f R-a R-a~ R-b R-b~ refl

  exists-U : {A : U} (aₚ : in-Uₚ A) (aₜ : in-Uₜ aₚ) -> Σ (in-Uᴰ (aₚ ,sp aₜ)) (R-U aₚ aₜ)
  exists-U~ : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}
              {a₀ᴰ : in-Uᴰ a₀} {a₁ᴰ : in-Uᴰ a₁} (p₀ : R-U (proj₁sp a₀) (proj₂sp a₀) a₀ᴰ) (p₁ : R-U (proj₁sp a₁) (proj₂sp a₁) a₁ᴰ)
              (a₀₁ₚ : in-U~ₚ A₀ A₁ A₀₁) (a₀₁ₜ : in-U~ₜ A₀ A₁ (proj₁sp a₀) (proj₁sp a₁) a₀₁ₚ)
            → Σ (in-U~ᴰ a₀ᴰ a₁ᴰ (a₀₁ₚ ,sp a₀₁ₜ)) (R-U~ (a₀₁ₚ ,sp a₀₁ₜ))

  exists-U boolₚ aₜ = _ ,Σ R-bool
  exists-U (πₚ aₚ a~ₚ bₚ b~ₚ) p = _ ,Σ
    R-π ih-a (proj₂ (exists-U~ ih-a ih-a a~ₚ a~ₜ))
        ih-b (λ x₀₁ → proj₂ (exists-U~ (ih-b _) (ih-b _) (b~ₚ x₀₁) (b~ₜ x₀₁)))
    where
      aₜ : in-Uₜ aₚ
      aₜ = withProp p λ { (πₜ x _ _ _) → x }
      a~ₜ : in-U~ₜ _ _ aₚ aₚ a~ₚ
      a~ₜ = withProp p λ { (πₜ _ x _ _) → x }
      ih-a = proj₂ (exists-U aₚ aₜ)
      bₜ : (x : _) -> in-Uₜ (bₚ x)
      bₜ x = withProp p λ { (πₜ _ _ f _) → f x }
      ih-b : (x : _) -> _
      ih-b x = proj₂ (exists-U (bₚ x) (bₜ x))
      b~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ _ _ (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)
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
      b₀~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ _ _ (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁)
      b₀~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ x _ _ _) → x }

      eq1 : pi₀ ≡ π (a₀ₚ ,sp a₀ₜ) (a₀~ₚ ,sp a₀~ₜ)
                    (λ x → b₀ₚ x ,sp b₀ₜ x) λ x₀₁ → b₀~ₚ x₀₁ ,sp b₀~ₜ x₀₁
      eq1 = to-≡ (withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ _ _) → reflp })

      a₁ₜ = withProp p λ { (π~ₜ _ _ x _ _ _ _ _ _ _) → x }
      a₁~ₜ = withProp p λ { (π~ₜ _ _ _ x _ _ _ _ _ _) → x }
      b₁ₜ : (x : _) -> in-Uₜ (b₁ₚ x)
      b₁ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ x _ _) → x }
      b₁~ₜ : {x₀ x₁ : _} (x₀₁ : _) -> in-U~ₜ _ _ (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁)
      b₁~ₜ = withProp p λ { (π~ₜ _ _ _ _ _ _ _ _ x _) → x }

      a₀₁ₜ : in-U~ₜ _ _ a₀ₚ a₁ₚ a₀₁ₚ
      a₀₁ₜ = (withProp p (λ { (π~ₜ _ _ _ _ x _ _ _ _ _) → x }))

      b₀₁ₜ : ∀{x₀ x₁} (x₀₁ : _) → in-U~ₜ _ _ (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)
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

  elim-U : {A : U} (a : in-U A) → in-Uᴰ a
  elim-U a = proj₁ (exists-U (proj₁sp a) (proj₂sp a))

  elim-U~ : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}
            (a₀₁ : in-U~ A₀ A₁ a₀ a₁ A₀₁) → in-U~ᴰ (elim-U a₀) (elim-U a₁) a₀₁
  elim-U~ a~ = proj₁ (exists-U~ (proj₂ (exists-U _ _)) (proj₂ (exists-U _ _)) (proj₁sp a~) (proj₂sp a~))

  ind-in-U : ∀{A : U}(a : in-U A) → in-Uᴰ a
  ind-in-U (aₚ ,sp aₜ) = proj₁ (exists-U aₚ aₜ)
  
  ind-in-U~ : ∀{A₀ A₁ : U}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : El A₀ → El A₁ → P}(a₀₁ : in-U~ _ _ a₀ a₁ A₀₁) → in-U~ᴰ (ind-in-U a₀) (ind-in-U a₁) a₀₁
  ind-in-U~ (a₀₁ₚ ,sp a₀₁ₜ) = proj₁ (exists-U~ (proj₂ (exists-U _ _)) (proj₂ (exists-U _ _)) a₀₁ₚ a₀₁ₜ)

  bool-β : ind-in-U bool ≡ boolᴰ
  bool-β = refl

  π-β :
    {A : U}(a : in-U A){A~ : El A -> El A -> P}(a~ : in-U~ A A a a A~)
    {B : El A -> U}
    (b : (x : El A) → in-U (B x))
    {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
    (b~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ (B x₀) (B x₁) (b x₀) (b x₁) (B~ x₀₁))
    → ind-in-U (π a a~ b b~)
    ≡ πᴰ (ind-in-U a) (ind-in-U~ a~) (λ x → ind-in-U (b x)) (λ x₀₁ → ind-in-U~ (b~ x₀₁))
  π-β a a~ b b~ = refl

  bool~-β : ind-in-U~ bool~ ≡ bool~ᴰ
  bool~-β = refl

  π~-β : {A₀ : U}{a₀ : in-U A₀}{A₀~ : El A₀ → El A₀ → P}{a₀~ : in-U~ A₀ A₀ a₀ a₀ A₀~}
       {A₁ : U}{a₁ : in-U A₁}{A₁~ : El A₁ → El A₁ → P}{a₁~ : in-U~ A₁ A₁ a₁ a₁ A₁~}
       {A₀₁ : El A₀ → El A₁ → P}(a₀₁ : in-U~ A₀ A₁ a₀ a₁ A₀₁)
  
       {B₀ : El A₀ → U}{b₀ : (x₀ : El A₀) → in-U (B₀ x₀)}
         {B₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → El (B₀ x₀) → El (B₀ x₁) → P}
         {b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ (B₀ x₀) (B₀ x₁) (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
       {B₁ : El A₁ → U}{b₁ : (x₁ : El A₁) → in-U (B₁ x₁)}
         {B₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → El (B₁ x₀) → El (B₁ x₁) → P}
         {b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ (B₁ x₀) (B₁ x₁) (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
       {B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P}
       (b₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ (B₀ x₀) (B₁ x₁) (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁))
     → ind-in-U~ (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁
                     {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
     ≡ π~ᴰ (ind-in-U a₀) (ind-in-U~ a₀~) (ind-in-U a₁) (ind-in-U~ a₁~) (ind-in-U~ a₀₁)
           (λ x₀ → ind-in-U (b₀ x₀)) (λ x₀₁ → ind-in-U~ (b₀~ x₀₁)) (λ x₁ → ind-in-U (b₁ x₁)) (λ x₀₁ → ind-in-U~ (b₁~ x₀₁)) λ x₀₁ → ind-in-U~ (b₀₁ x₀₁)
  π~-β a₀₁ b₀₁ = refl
