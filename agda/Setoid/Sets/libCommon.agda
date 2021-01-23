{-# OPTIONS --without-K --prop #-}

module Setoid.Sets.libCommon where

open import Setoid.lib
-- should work with either of the following two libraries:
-- open import Setoid.Sets.lib public
open import Setoid.SetsII.lib public

module simple-just-U
  {i}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    → in-Uᴰ (π a a~ b b~))
  where
  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U = simple.ind-in-U in-Uᴰ (λ _ → ⊤) boolᴰ (λ aᴰ {A~}{a~} _ bᴰ {B~}{b~} _ → πᴰ aᴰ {A~}{a~} bᴰ {B~}{b~}) tt (λ _ _ _ _ _ _ _ _ _ _ → tt)

module simpleProp-just-U
  {i}
  (in-Uᴰ : ∀{A : Set} → in-U A → Prop i)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    → in-Uᴰ (π a a~ b b~))
  where

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U = simpleProp.ind-in-U in-Uᴰ (λ _ → ⊤p) boolᴰ
    (λ {A}{a} aᴰ {A~}{a~} _ {B}{b} bᴰ {B~}{b~} _ → πᴰ {A}{a} aᴰ {A~}{a~}{B}{b} bᴰ {B~}{b~})
    ttp (λ _ _ _ _ _ _ _ _ _ _ → ttp)

module simple-just-U~
  {j}
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Set j)
  (bool~ᴰ : in-U~ᴰ {a₀ = bool}{a₁ = bool} bool~)
  (π~ᴰ :
    {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₀} a₀~)
    {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ {a₀ = a₁}{a₁ = a₁} a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}(b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₀ x₁} (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}(b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ {a₀ = b₁ x₀}{a₁ = b₁ x₁} (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₁ x₁} (b₀₁ x₀₁)) → 
    in-U~ᴰ {a₀ = π a₀ a₀~ b₀ b₀~}{a₁ = π a₁ a₁~ b₁ b₁~} (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁))
  where
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U~ a₀₁ = simple.ind-in-U~
    (λ _ → ⊤)
    (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} → in-U~ᴰ {A₀}{A₁}{a₀}{a₁}{A₀₁})
    tt
    (λ _ _ _ _ → tt)
    bool~ᴰ
    (λ _ a₀~ᴰ _ a₁~ᴰ a₀₁ᴰ _ b₀~ᴰ _ b₁~ᴰ b₀₁ᴰ → π~ᴰ a₀~ᴰ a₁~ᴰ a₀₁ᴰ b₀~ᴰ b₁~ᴰ b₀₁ᴰ)
    a₀₁

module simpleProp-just-U~
  {j}
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Prop j)
  (bool~ᴰ : in-U~ᴰ {a₀ = bool}{a₁ = bool} bool~)
  (π~ᴰ :
    {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₀} a₀~)
    {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ {a₀ = a₁}{a₁ = a₁} a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}(b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₀ x₁} (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}(b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ {a₀ = b₁ x₀}{a₁ = b₁ x₁} (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ {a₀ = b₀ x₀}{a₁ = b₁ x₁} (b₀₁ x₀₁)) → 
    in-U~ᴰ {a₀ = π a₀ a₀~ b₀ b₀~}{a₁ = π a₁ a₁~ b₁ b₁~} (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁))
  where
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ {a₀ = a₀}{a₁ = a₁} a₀₁
  ind-in-U~ a₀₁ = simpleProp.ind-in-U~
    (λ _ → ⊤p)
    (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} → in-U~ᴰ {A₀}{A₁}{a₀}{a₁}{A₀₁})
    ttp
    (λ _ _ _ _ → ttp)
    bool~ᴰ
    (λ _ a₀~ᴰ _ a₁~ᴰ a₀₁ᴰ _ b₀~ᴰ _ b₁~ᴰ b₀₁ᴰ → π~ᴰ a₀~ᴰ a₁~ᴰ a₀₁ᴰ b₀~ᴰ b₁~ᴰ b₀₁ᴰ)
    a₀₁

module double
  {i}
  (in-Uᴰ : ∀{A⁰} → in-U A⁰ → ∀{A¹} → in-U A¹ → Set i)
  (boolboolᴰ : in-Uᴰ bool bool)
  (boolπᴰ : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →  in-Uᴰ bool (π a a~ b b~))
  (πboolᴰ : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →  in-Uᴰ (π a a~ b b~) bool)
  (ππᴰ : {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}(aᴰ : in-Uᴰ a⁰ a¹)
    {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}(a~⁰ : in-U~ a⁰ a⁰ A~⁰)(a~¹ : in-U~ a¹ a¹ A~¹)
    {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}(bᴰ : (x⁰ : A⁰)(x¹ : A¹) → in-Uᴰ (b⁰ x⁰) (b¹ x¹))
    {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
    (b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁))(b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)) → 
    in-Uᴰ (π a⁰ a~⁰ b⁰ b~⁰) (π a¹ a~¹ b¹ b~¹))
  where
  ind-in-U : ∀{A⁰ : Set}(a⁰ : in-U A⁰){A¹ : Set}(a¹ : in-U A¹) → in-Uᴰ a⁰ a¹
  ind-in-U = simple.ind-in-U (λ a⁰ → ∀{A¹}(a¹ : in-U A¹) → in-Uᴰ a⁰ a¹) (λ _ → ⊤)
    (simple.ind-in-U (λ a¹ → in-Uᴰ bool a¹) (λ _ → ⊤) boolboolᴰ (λ {A}{a} _ {A~}{a~} _ {B}{b} _ {B~}{b~} _ → boolπᴰ a a~ b b~) tt (λ _ _ _ _ _ _ _ _ _ _ → tt))
    (λ {A⁰}{a⁰} aᴰ' {A~⁰}{a~⁰} _ {B⁰}{b⁰} bᴰ' {B~⁰}{b~⁰} _ → simple.ind-in-U
      (λ c¹ → in-Uᴰ (π a⁰ a~⁰ b⁰ b~⁰) c¹) (λ _ → ⊤)
      (πboolᴰ a⁰ a~⁰ b⁰ b~⁰)
      (λ {A¹}{a¹} aᴰ {A~¹}{a~¹} _ {B¹}{b¹} bᴰ {B~¹}{b~¹} _ → ππᴰ {a⁰ = a⁰}{a¹} (aᴰ' a¹) a~⁰ a~¹ {b⁰ = b⁰}{b¹} (λ x⁰ x¹ → bᴰ' x⁰ (b¹ x¹)) b~⁰ b~¹)
      tt λ _ _ _ _ _ _ _ _ _ _ → tt)
    tt (λ _ _ _ _ _ _ _ _ _ _ → tt)

open import Agda.Builtin.Equality

ap : ∀{i j}{A : Set i}{B : Set j} {x y : A} (f : A → B) → (p : x ≡ y) → f x ≡ f y
ap f refl = refl
transp : ∀{i j}{A : Set i} {x y : A} (P : A → Set j) → x ≡ y → P x → P y
transp _ refl a = a
transpp : ∀{i j}{A : Set i} {x y : A} (P : A → Prop j) → x ≡ y → P x → P y
transpp _ refl a = a
_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

projΣ≡₁ : ∀{i j}{A : Set i}{B : A → Set j}{a₀ a₁ : A}{b₀ : B a₀}{b₁ : B a₁} → (a₀ ,Σ b₀) ≡ (a₁ ,Σ b₁) → a₀ ≡ a₁
projΣ≡₁ refl = refl

noconf : {A : Set}{a : in-U A}{A~ : A → A → Prop}{a~ : in-U~ a a A~}{B : A → Set}
  {b : (x : A) → in-U (B x)}{B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}{b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)} → 
  _≡_ {A = Σ _ in-U} (_ ,Σ π a a~ b b~) (_ ,Σ bool) → ⊥
noconf e = transp (λ X → X) (ap (λ w → simple-just-U.ind-in-U (λ _ → Set) ⊥ (λ _ _ → ⊤) (proj₂ w)) e) tt

no-bool-π :
  {A : Set}{a : in-U A}{A~ : A → A → Prop}{a~ : in-U~ a a A~}
  {B : A → Set}{b : (x : A) → in-U (B x)}{B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}{b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
  {C₀₁ : _} →
  in-U~ bool (π a a~ b b~) C₀₁ → ⊥
no-bool-π {A}{a}{A~}{a~}{B}{b}{B~}{b~}{C₀₁} c₀₁ = simple-just-U~.ind-in-U~
  (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} a₀₁ → (e₀ : _≡_ {A = Σ _ in-U} (_ ,Σ a₀) (_ ,Σ bool))(e₁ : _≡_ {A = Σ _ in-U} (_ ,Σ a₁) (_ ,Σ π a a~ b b~)) → ⊥)
  (λ _ e → noconf {a = a}{a~ = a~}{b = b}{b~ = b~} (e ⁻¹))
  (λ {_}{a₀}{_}{a₀~} _ _ _ {_}{b₀}{_}{b₀~} _ _ _ e _ → noconf {a = a₀}{a~ = a₀~}{b = b₀}{b~ = b₀~} e)
  c₀₁
  refl
  refl

no-π-bool :
  {A : Set}{a : in-U A}{A~ : A → A → Prop}{a~ : in-U~ a a A~}
  {B : A → Set}{b : (x : A) → in-U (B x)}{B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}{b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
  {C₀₁ : _} →
  in-U~ (π a a~ b b~) bool C₀₁ → ⊥
no-π-bool {A}{a}{A~}{a~}{B}{b}{B~}{b~}{C₀₁} c₀₁ = simple-just-U~.ind-in-U~
  (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} a₀₁ → (e₀ : _≡_ {A = Σ _ in-U} (_ ,Σ a₀) (_ ,Σ π a a~ b b~))(e₁ : _≡_ {A = Σ _ in-U} (_ ,Σ a₁) (_ ,Σ bool)) → ⊥)
  (λ e _ → noconf {a = a}{a~ = a~}{b = b}{b~ = b~} (e ⁻¹))
  (λ _ {_}{a₁}{_}{a₁~} _ _ _ {_}{b₁}{_}{b₁~} _ _ _ e → noconf {a = a₁}{a~ = a₁~}{b = b₁}{b~ = b₁~} e)
  c₀₁
  refl
  refl

projbool~p : ∀{i}(P : ∀{C₀₁} → in-U~ bool bool C₀₁ → Prop i) → P bool~ → ∀{C₀₁}(c₀₁ : in-U~ bool bool C₀₁) → P c₀₁
projbool~p P p {C₀₁} c₀₁ = simpleProp-just-U~.ind-in-U~
  (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} a₀₁ → (e₀ : (_ ,Σ a₀) ≡ (_ ,Σ bool))(e₁ : (_ ,Σ a₁) ≡ (_ ,Σ bool)) → P (f e₀ e₁ a₀₁))
  (λ { refl refl → p })
  (λ _ {_}{a₁}{_}{a₁~} _ _ _ {_}{b₁}{_}{b₁~} _ _ _ w → ⊥elimp (noconf {a = a₁}{a~ = a₁~}{b = b₁}{b~ = b₁~} w))
  c₀₁ refl refl
  where
  f' : ∀{A₀}{A₁}(e₀ : A₀ ≡ 𝟚)(e₁ : A₁ ≡ 𝟚)(A₀₁ : A₀ → A₁ → Prop) → (𝟚 → 𝟚 → Prop)
  f' refl refl A₀₁ = A₀₁
  f : ∀{A₀}{A₁}{a₀}{a₁}{A₀₁ : A₀ → A₁ → Prop}(e₀ : (A₀ ,Σ a₀) ≡ (𝟚 ,Σ bool))(e₁ : (A₁ ,Σ a₁) ≡ (𝟚 ,Σ bool)) → in-U~ a₀ a₁ A₀₁ → in-U~ bool bool (f' (projΣ≡₁ e₀) (projΣ≡₁ e₁) A₀₁)
  f refl refl a₀₁ = a₀₁

{-
{-
data F : Set → Set₁ where
  bb : (A B : Set) → F (A → B)
fff : {X Y : Set} →  _≡_ {A = Σ Set F} ((X → 𝟚) ,Σ bb X 𝟚) ((Y → 𝟚) ,Σ bb Y 𝟚) → Set
fff {X} refl = {!!}
-}

f' : ∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
  {C₀}{C₁}
  (e₀ : C₀ ≡ (Σsp ((x : A₀) → B₀ x) (λ f → (x₀ x₁ : A₀)(x₀₁ : ↑ps (A₀~ x₀ x₁)) → B₀~ (un↑ps x₀₁) (f x₀) (f x₁))))
  (e₁ : C₁ ≡ (Σsp ((x : A₁) → B₁ x) (λ f → (x₀ x₁ : A₁)(x₀₁ : ↑ps (A₁~ x₀ x₁)) → B₁~ (un↑ps x₀₁) (f x₀) (f x₁))))
  (C₀₁ : C₀ → C₁ → Prop) → ((Σsp ((x : A₀) → B₀ x) (λ f → (x₀ x₁ : A₀)(x₀₁ : ↑ps (A₀~ x₀ x₁)) → B₀~ (un↑ps x₀₁) (f x₀) (f x₁))) → (Σsp ((x : A₁) → B₁ x) (λ f → (x₀ x₁ : A₁)(x₀₁ : ↑ps (A₁~ x₀ x₁)) → B₁~ (un↑ps x₀₁) (f x₀) (f x₁))) → Prop)
f' refl refl C₀₁ = C₀₁  
f : ∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
  {C₀}{C₁}{c₀ : in-U C₀}{c₁ : in-U C₁}{C₀₁ : C₀ → C₁ → Prop}
  (e₀ : _≡_ {A = Σ Set in-U} (C₀ ,Σ c₀) (_ ,Σ π a₀ a₀~ b₀ b₀~))
  (e₁ : _≡_ {A = Σ Set in-U} (C₁ ,Σ c₁) (_ ,Σ π a₁ a₁~ b₁ b₁~)) →
  in-U~ c₀ c₁ C₀₁ → in-U~ (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (f' {a₀~ = a₀~}{a₁~ = a₁~}{b₀~ = b₀~}{b₁~ = b₁~}(projΣ≡₁ e₀)(projΣ≡₁ e₁) C₀₁)
f refl refl c₀₁ = c₀₁

projπ~ : ∀{i} →
  (P : ∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}{C₀₁} →
    in-U~ (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) C₀₁ → Set i) → 
  (∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}{B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}{b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)} → 
    P {a₀~ = a₀~}{a₁~ = a₁~}{b₀~ = b₀~}{b₁~ = b₁~} (π~ a₀₁ b₀₁)) →
  ∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
  {C₀₁}(c₀₁ : in-U~ (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) C₀₁) → P c₀₁
projπ~ P p {A₀}{a₀}{A₀~}{a₀~}{A₁}{a₁}{A₁~}{a₁~}{B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{C₀₁} c₀₁ = simple-just-U~.ind-in-U~
  (λ {C₀}{C₁}{c₀}{c₁}{C₀₁} c₀₁ → ∀{A₀}{a₀ : in-U A₀}{A₀~}{a₀~ : in-U~ a₀ a₀ A₀~}{A₁}{a₁ : in-U A₁}{A₁~}{a₁~ : in-U~ a₁ a₁ A₁~}{B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}{B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}{B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}{B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}{b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}(e₀ : (_ ,Σ c₀) ≡ (_ ,Σ π a₀ a₀~ b₀ b₀~))(e₁ : (_ ,Σ c₁) ≡ (_ ,Σ π a₁ a₁~ b₁ b₁~)) → P (f e₀ e₁ c₀₁))
  (λ e → ⊥elim (noconf (e ⁻¹)))
  (λ {A₀}{a₀}{A₀~}{a₀~} a₀~ᴰ {A₁}{a₁}{A₁~}{a₁~} a₁~ᴰ {A₀₁}{a₀₁} a₀₁ᴰ {B₀}{b₀}{B₀~}{b₀~} b₀~ᴰ {B₁}{b₁}{B₁~}{b₁~} b₁~ᴰ {B₀₁}{b₀₁} b₀₁ᴰ → {!p!})
  c₀₁ {A₀}{a₀}{A₀~}{a₀~}{A₁}{a₁}{A₁~}{a₁~}{B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~} refl refl
-}
open import Data.Sum

pj-π-T : Set₁
pj-π-T = ⊤ ⊎ Σ Set λ A → in-U A × Σ (A -> Set) λ B → ((x : A) → in-U (B x))

pj-π : {A : _} → in-U A → pj-π-T
pj-π = simple-just-U.ind-in-U _ (inj₁ tt) (λ { {a = a} aᴰ {b = b} bᴰ → inj₂ (_ ,Σ (a ,Σ (_ ,Σ b))) })

⊤' : Set₁
⊤' = {A : Set} → A → A

ss : pj-π-T -> pj-π-T -> Set₁
ss (inj₁ x) y = ⊤'
ss (inj₂ x) (inj₁ x₁) = ⊤'
ss (inj₂ (A₀ ,Σ (a₀ ,Σ (B₀ ,Σ b₀)))) (inj₂ (A₁ ,Σ (a₁ ,Σ (B₁ ,Σ b₁)))) =
  Σ (A₀ → A₁ → Prop) λ A~ → in-U~ a₀ a₁ A~ × Σ ({x₀ : A₀} {x₁ : A₁} → A~ x₀ x₁ → B₀ x₀ → B₁ x₁ → Prop)
    (λ B~ → ({x₀ : A₀} {x₁ : A₁} (x₀₁ : A~ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B~ x₀₁)))

pj-π~ : {A₀ A₁ : _} {a₀ : in-U A₀} {a₁ : in-U A₁} {A~ : A₀ → A₁ → Prop}
      → in-U~ a₀ a₁ A~ → ss (pj-π a₀) (pj-π a₁)
pj-π~ {A₀}{A₁}{a₀}{a₁}{A~} = simple.ind-in-U~ (λ _ → ⊤) (λ {_} {_} {a₀} {a₁} _ → ss (pj-π a₀) (pj-π a₁))
  tt (λ _ _ _ _ → tt) (λ z → z) (λ {a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ {a₀₁ = a₀₁} a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ {b₀₁ = b₀₁} b₀₁ᴰ → _ ,Σ (a₀₁ ,Σ (_ ,Σ b₀₁))}) {A₀}{A₁}{a₀}{a₁}{A~} 

projπ~₁' : -- TODO: derive this from pj-π~
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} →
  ∀{C₀₁} → in-U~ (π a⁰ a~⁰ b⁰ b~⁰) (π a¹ a~¹ b¹ b~¹) C₀₁ →
  Σ _ λ A₀₁ → in-U~ a⁰ a¹ A₀₁
projπ~₁' {A₀}{A₁}{a₀}{a₁}{A~₀}{A~₁}{a~₀}{a~₁}{B₀}{B₁}{b₀}{b₁}{B~₀}{B~₁}{b~₀}{b~₁} w = _ ,Σ proj₁ (proj₂ ( pj-π~ {a₀ = π a₀ a~₀ b₀ b~₀}{a₁ = π a₁ a~₁ b₁ b~₁} w ))

projπ~₃ :
  {A₀ : Set}{A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}
  {A~₀ : A₀ → A₀ → Prop}{A~₁ : A₁ → A₁ → Prop}{a~₀ : in-U~ a₀ a₀ A~₀}{a~₁ : in-U~ a₁ a₁ A~₁}
  {B₀ : A₀ → Set}{B₁ : A₁ → Set}{b₀ : (x : A₀) → in-U (B₀ x)}{b₁ : (x : A₁) → in-U (B₁ x)}
  {B~₀ : {x₀ x₁ : A₀}(x₀₁ : A~₀ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}{B~₁ : {x₀ x₁ : A₁}(x₀₁ : A~₁ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
  {b~₀ : {x₀ x₁ : A₀}(x₀₁ : A~₀ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B~₀ x₀₁)}{b~₁ : {x₀ x₁ : A₁}(x₀₁ : A~₁ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B~₁ x₀₁)} →
  ∀{C₀₁}(c₀₁ : in-U~ (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) C₀₁) →
  C₀₁ ≡ (λ f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (proj₁ (pj-π~ {a₀ = π a₀ a~₀ b₀ b~₀}{π a₁ a~₁ b₁ b~₁} c₀₁) x₀ x₁)) → proj₁ (proj₂ (proj₂ (pj-π~ c₀₁))) (un↑ps x₀₁) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁))
projπ~₃ {A₀}{A₁}{a₀}{a₁}{A~₀}{A~₁}{a~₀}{a~₁}{B₀}{B₁}{b₀}{b₁}{B~₀}{B~₁}{b~₀}{b~₁}(π~ c₀₁ b₀₁) = refl
