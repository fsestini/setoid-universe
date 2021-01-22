{-# OPTIONS --without-K --prop #-}

module Setoid.Sets where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF
-- should work with either of the following two libraries:
-- open import Setoid.Sets.lib
open import Setoid.SetsII.lib

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ Set in-U

∣El∣ : ∣U∣ → Set
∣El∣ Â = proj₁ Â

_~U_ : ∣U∣ → ∣U∣ → Prop₁
Â₀ ~U Â₁ = Tr (Σ (proj₁ Â₀ → proj₁ Â₁ → Prop) (λ A₀₁ → in-U~ (proj₂ Â₀) (proj₂ Â₁) A₀₁))

open import Agda.Builtin.Equality

ap : ∀{i j}{A : Set i}{B : Set j} {x y : A} (f : A → B) → (p : x ≡ y) → f x ≡ f y
ap f refl = refl
transp : ∀{i j}{A : Set i} {x y : A} (P : A → Set j) → x ≡ y → P x → P y
transp _ refl a = a
_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

projΣ≡₁ : ∀{i j}{A : Set i}{B : A → Set j}{a₀ a₁ : A}{b₀ : B a₀}{b₁ : B a₁} → (a₀ ,Σ b₀) ≡ (a₁ ,Σ b₁) → a₀ ≡ a₁
projΣ≡₁ refl = refl

noconf : {A : Set}{a : in-U A}{A~ : A → A → Prop}{a~ : in-U~ a a A~}{B : A → Set}
  {b : (x : A) → in-U (B x)}{B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}{b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)} → 
  _≡_ {A = Σ _ in-U} (_ ,Σ π a a~ b b~) (_ ,Σ bool) → ⊥
noconf e = transp (λ X → X) (ap (λ w → simple-just-U.ind-in-U (λ _ → Set) ⊥ (λ _ _ → ⊤) (proj₂ w)) e) tt

f' : ∀{A₀}{A₁}(e₀ : A₀ ≡ 𝟚)(e₁ : A₁ ≡ 𝟚)(A₀₁ : A₀ → A₁ → Prop) → (𝟚 → 𝟚 → Prop)
f' refl refl A₀₁ = A₀₁

f : ∀{A₀}{A₁}{a₀}{a₁}{A₀₁ : A₀ → A₁ → Prop}(e₀ : (A₀ ,Σ a₀) ≡ (𝟚 ,Σ bool))(e₁ : (A₁ ,Σ a₁) ≡ (𝟚 ,Σ bool)) → in-U~ a₀ a₁ A₀₁ → in-U~ bool bool (f' (projΣ≡₁ e₀) (projΣ≡₁ e₁) A₀₁)
f refl refl a₀₁ = a₀₁

projbool~ : ∀{i}(P : {A₀₁ : 𝟚 → 𝟚 → Prop} → in-U~ bool bool A₀₁ → Set i) → P bool~ → ∀{A₀₁}(a₀₁ : in-U~ bool bool A₀₁) → P a₀₁
projbool~ P p {A₀₁} a₀₁ =  simple.ind-in-U~
  (λ _ → ⊤)
  (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} a₀₁ → (e₀ : (_ ,Σ a₀) ≡ (_ ,Σ bool))(e₁ : (_ ,Σ a₁) ≡ (_ ,Σ bool)) → P (f e₀ e₁ a₀₁))
  tt
  (λ _ _ _ _ → tt)
  (λ { refl refl → p })
  (λ _ _ _ _ _ _ _ _ _ _ ())
  a₀₁ refl refl 
projbool~p : ∀{i}(P : {A₀₁ : 𝟚 → 𝟚 → Prop} → in-U~ bool bool A₀₁ → Prop i) → P bool~ → ∀{A₀₁}(a₀₁ : in-U~ bool bool A₀₁) → P a₀₁
projbool~p P p {A₀₁} a₀₁ =  simpleProp.ind-in-U~
  (λ _ → ⊤p)
  (λ {A₀}{A₁}{a₀}{a₁}{A₀₁} a₀₁ → (e₀ : (_ ,Σ a₀) ≡ (_ ,Σ bool))(e₁ : (_ ,Σ a₁) ≡ (_ ,Σ bool)) → P (f e₀ e₁ a₀₁))
  ttp
  (λ _ _ _ _ → ttp)
  (λ { refl refl → p })
  (λ _ _ _ _ _ _ _ _ _ _ ())
  a₀₁ refl refl 

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
    (λ B~ → {x₀ : A₀} {x₁ : A₁} (x₀₁ : A~ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B~ x₀₁))

pj-π~ : {A₀ A₁ : _} {a₀ : in-U A₀} {a₁ : in-U A₁} {A~ : A₀ → A₁ → Prop}
      → in-U~ a₀ a₁ A~ → ss (pj-π a₀) (pj-π a₁)
pj-π~ {A₀}{A₁}{a₀}{a₁}{A~} =  simple.ind-in-U~ (λ _ → ⊤) (λ {_} {_} {a₀} {a₁} _ → ss (pj-π a₀) (pj-π a₁))
  tt (λ _ _ _ _ → tt) (λ z → z) (λ {a₀ᴰ a₀~ᴰ a₁ᴰ a₁~ᴰ {a₀₁ = a₀₁} a₀₁ᴰ b₀ᴰ b₀~ᴰ b₁ᴰ b₁~ᴰ {b₀₁ = b₀₁} b₀₁ᴰ → _ ,Σ (a₀₁ ,Σ (_ ,Σ b₀₁))}) {A₀}{A₁}{a₀}{a₁}{A~} 

projπ~₁ :
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)}
  → (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹)
  → (_ ,Σ a⁰) ~U (_ ,Σ a¹)
projπ~₁ {A₀}{A₁}{a₀}{a₁}{A~₀}{A~₁}{a~₀}{a~₁}{B₀}{B₁}{b₀}{b₁}{B~₀}{B~₁}{b~₀}{b~₁} w = withTrunc w λ w' → tr (_ ,Σ proj₁ (proj₂ ( pj-π~ {a₀ = π a₀ a~₀ b₀ b~₀}{a₁ = π a₁ a~₁ b₁ b~₁} (proj₂ w') )))

projπ~₁' :
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} →
  ∀{C₀₁} → in-U~ (π a⁰ a~⁰ b⁰ b~⁰) (π a¹ a~¹ b¹ b~¹) C₀₁ →
  Σ _ λ A₀₁ → in-U~ a⁰ a¹ A₀₁
projπ~₁' {A₀}{A₁}{a₀}{a₁}{A~₀}{A~₁}{a~₀}{a~₁}{B₀}{B₁}{b₀}{b₁}{B~₀}{B~₁}{b~₀}{b~₁} w = _ ,Σ proj₁ (proj₂ ( pj-π~ {a₀ = π a₀ a~₀ b₀ b~₀}{a₁ = π a₁ a~₁ b₁ b~₁} w ))

El~' : ∀{A₀}(a₀ : in-U A₀){A₁}(a₁ : in-U A₁) → Σsp
  ((A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop) λ A₀₁' →
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁' (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ ↔ A₀₁ x₀ x₁
El~' = double.ind-in-U
  (λ {A₀} a₀ {A₁} a₁ → Σsp
  ((A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop) λ A₀₁' →
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁' (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ ↔ A₀₁ x₀ x₁)
  ((λ _ x₀ x₁ → x₀ ≟𝟚 x₁) ,sp λ b₀₁ {b₀}{b₁} → projbool~p (λ {A₀₁} a₀₁ → (b₀ ≟𝟚 b₁) ↔ A₀₁ b₀ b₁) ((λ x₀₁ → x₀₁) ,p (λ x₀₁ → x₀₁)) b₀₁)
  (λ a a~ b b~ → (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ())
  (λ a a~ b b~ → (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ())
  (λ {A₀}{A₁}{a₀}{a₁} El~a₀a₁ {A~₀}{A~₁} a~₀ a~₁  {B₀}{B₁}{b₀}{b₁} El~b₀b₁  {B~₀}{B~₁} b~₀ b~₁ → (λ w f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (proj₁sp El~a₀a₁ (projπ~₁ {A₀}{A₁}{a₀}{a₁}{A~₀}{A~₁}{a~₀}{a~₁}{B₀}{B₁}{b₀}{b₁}{B~₀}{B~₁}{b~⁰ = b~₀}{b~¹ = b~₁} w) x₀ x₁)) →
    proj₁sp (El~b₀b₁ x₀ x₁) (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ ((proj₁p (proj₂sp El~a₀a₁ a₀₁)) (un↑ps x₀₁))) }) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁)) ,sp
    (λ { (π~ {A₀₁ = A₀₁} a₀₁ b₀₁) →
      (λ f₀₁ x₀ x₁ x₀₁ → proj₁p ((proj₂sp (El~b₀b₁ x₀ x₁)) (b₀₁ (un↑ps x₀₁))) (f₀₁ _ _ (mk↑ps (proj₂p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁))))) ,p
      (λ f₀₁ x₀ x₁ x₀₁ → proj₂p (proj₂sp (El~b₀b₁ x₀ x₁) (b₀₁ (proj₁p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps (proj₁p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁))))) }))

El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop
El~ {a₀ = a₀}{a₁} = proj₁sp (El~' a₀ a₁)

fromEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → A₀₁ x₀ x₁
fromEl~ {a₀ = a₀}{a₁} a~ = proj₁p (proj₂sp (El~' a₀ a₁) a~)

toEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁ x₀ x₁ → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁
toEl~ {a₀ = a₀}{a₁} a~ = proj₂p (proj₂sp (El~' a₀ a₁) a~)

projπ~₂ :
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} → 
  (w : (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹)) → {x⁰ : A⁰}{x¹ : A¹}(x⁰¹ : El~ (projπ~₁ w) x⁰ x¹) → (_ ,Σ b⁰ x⁰) ~U (_ ,Σ b¹ x¹)
projπ~₂ {a⁰ = a⁰}{a¹ = a¹} w = withTrunc w λ w' x⁰¹ → tr (_ ,Σ proj₂ (proj₂ (proj₂ (pj-π~ (proj₂ w')))) (fromEl~ (proj₁ (proj₂ (pj-π~ (proj₂ w')))) x⁰¹))

in-El~ : ∀{A₀}(a₀ : in-U A₀){A₁}(a₁ : in-U A₁)(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ = double.ind-in-U
  (λ {A₀} a₀ {A₁} a₁ → (w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w))
  (λ w → bool~)
  (λ a a~ b b~ w → ⊥pelim (withTrunc w λ ()))
  (λ a a~ b b~ w → ⊥pelim (withTrunc w λ ()))
  λ {A₀}{A₁} in-El~a₀a₁ a~₀ a~₁ in-El~b₀b₁ b~₀ b~₁ w → π~
    (in-El~a₀a₁ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ a₀₁) }))) -- TODO
    {B₀₁ = λ x₀₁ → El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }))} -- TODO
    λ x₀₁ → in-El~b₀b₁ _ _ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) })) -- TODO

_,π~_ : 
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} → 
  (Â₀₁ : (_ ,Σ a⁰) ~U (_ ,Σ a¹))(B̂₀₁ : {x⁰ : A⁰}{x¹ : A¹}(x⁰¹ : El~ Â₀₁ x⁰ x¹) → (_ ,Σ b⁰ x⁰) ~U (_ ,Σ b¹ x¹)) →
  (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹)
w₀ ,π~ w₁ = withTrunc w₀ λ w₀' → tr (_ ,Σ (π~ (proj₂ w₀') (λ {x₀}{x₁} x₀₁ → in-El~ _ _ (w₁ (toEl~ (proj₂ w₀') x₀₁)))))

refU : (Â : ∣U∣) → Â ~U Â
refU Â = simpleProp.ind-in-U (λ a → (_ ,Σ a) ~U (_ ,Σ a)) (λ _ → ⊤p)
  (tr (_ ,Σ bool~))
  (λ _ {A~}{a~} _ _ {B~}{b~} _ → tr (_ ,Σ π~ a~ {B₀₁ = B~} b~))
  ttp (λ _ _ _ _ _ _ _ _ _ _ → ttp) (proj₂ Â)

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → El~ (refU Â) x x
refEl {Â} x = simpleProp.ind-in-U (λ a → (x : ∣El∣ (_ ,Σ a)) → El~ (refU (_ ,Σ a)) x x) (λ _ → ⊤p)
  (λ { tt → ttp ; ff → ttp } )
  (λ {A}{a} refElA {A~}{a~} _ {B}{b} refElB {B~}{b~} _ (f ,sp f~) x₀ x₁ x₀₁ → toEl~ (b~ (fromEl~ a~ (un↑ps x₀₁))) (f~ _ _ (mk↑ps (fromEl~ a~ (un↑ps x₀₁)))))
  ttp (λ _ _ _ _ _ _ _ _ _ _ → ttp) (proj₂ Â) x

symU-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → Prop₁
symU-T {A₀} {A₁} a₀ a₁ = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → (A₁ ,Σ a₁) ~U (A₀ ,Σ a₀)

symEl-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → symU-T a₀ a₁ → Prop₁
symEl-T {A₀} {A₁} a₀ a₁ sy = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)){x₀ : A₀}{x₁ : A₁} → El~ Â₀₁ x₀ x₁ → El~ (sy Â₀₁) x₁ x₀

symEl⁻¹-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → symU-T a₀ a₁ → Prop₁
symEl⁻¹-T {A₀} {A₁} a₀ a₁ sy = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)){x₀ : A₀}{x₁ : A₁} → El~ (sy Â₀₁) x₁ x₀ → El~ Â₀₁ x₀ x₁

sym-combo-simple : {A₀ : _} (a₀ : in-U A₀) {A₁ : _} (a₁ : in-U A₁)
                 → Σp (symU-T a₀ a₁) λ sy → symEl-T a₀ a₁ sy ×p symEl⁻¹-T a₀ a₁ sy
sym-combo-simple =
  simple-just-U-prop.ind-in-U (λ a₀ → {A₁ : _} (a₁ : in-U A₁)
                 → Σp (symU-T a₀ a₁) λ sy → symEl-T a₀ a₁ sy ×p symEl⁻¹-T a₀ a₁ sy)
    (simple-just-U-prop.ind-in-U (λ a₁ → Σp (symU-T _ a₁) λ sy → symEl-T _ a₁ sy ×p symEl⁻¹-T _ a₁ sy)
      ((λ _ → tr (_ ,Σ bool~)) ,p ((λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }) ,p λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }))
      λ _ _ → (λ w → withTrunc w λ ()) ,p ((λ { (tr (_ ,Σ ())) }) ,p λ { (tr (_ ,Σ ())) })) -- (λ e → ⊥pelimp (withTrunc e λ e' → {!proj₂ e'!}))
    λ aᴰ bᴰ → simple-just-U-prop.ind-in-U ((λ a₁ → Σp (symU-T _ a₁) λ sy → symEl-T _ a₁ sy ×p symEl⁻¹-T _ a₁ sy))
      ((λ w → withTrunc w λ ()) ,p ((λ { (tr (_ ,Σ ())) }) ,p λ { (tr (_ ,Σ ())) }))
      λ { {a = a₁} aᴰ₁ {b = b₁} bᴰ₁ →
          (λ w → withTrunc w λ { (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) →
             proj₁p (aᴰ a₁) (tr (_ ,Σ a₀₁)) ,π~ λ {x₀}{x₁} x₀₁ →
             proj₁p ((bᴰ x₁) (b₁ x₀))
             (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (proj₂p (proj₂p (aᴰ a₁)) (tr (_ ,Σ a₀₁)) x₀₁)))) })
           ,p
           ((λ { (tr (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)) {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
                let x₁₀ = proj₂p (proj₂p (aᴰ a₁)) (tr (_ ,Σ a₀₁)) (un↑ps x₀₁)
                in proj₁p (proj₂p ((bᴰ x₁) (b₁ x₀))) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₁₀))) (f₀₁ _ _ (mk↑ps x₁₀))  })
           ,p
           λ { (tr (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)){f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
               let x₁₀ = proj₁p (proj₂p (aᴰ a₁)) (tr (_ ,Σ a₀₁)) (un↑ps x₀₁)
               in proj₂p (proj₂p ((bᴰ x₀) (b₁ x₁))) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps x₁₀)) })
             }

symU    : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
symU a₀ a₁ = proj₁p (sym-combo-simple a₀ a₁)

symEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
symEl a₀ a₁ = proj₁p (proj₂p (sym-combo-simple a₀ a₁))

symEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
symEl⁻¹ a₀ a₁ = proj₂p (proj₂p (sym-combo-simple a₀ a₁))

coeEl-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
coeEl-T {A₀} {A₁} a₀ a₁ = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → A₁

coeEl⁻¹-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
coeEl⁻¹-T {A₀} {A₁} a₀ a₁ = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₁ : A₁) → A₀

cohEl-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → coeEl-T a₀ a₁ → _
cohEl-T {A₀} {A₁} a₀ a₁ co = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → El~ Â₀₁ x₀ (co Â₀₁ x₀)

cohEl⁻¹-T : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → coeEl⁻¹-T a₀ a₁ → _
cohEl⁻¹-T {A₀} {A₁} a₀ a₁ co = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₁ : A₁) → El~ Â₀₁ (co Â₀₁ x₁) x₁

transU-T : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → _
transU-T {A₀} {A₁} {A₂} a₀ a₁ a₂ = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂)) → (A₀ ,Σ a₀) ~U (A₂ ,Σ a₂)

transEl-T : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → transU-T a₀ a₁ a₂ → _
transEl-T {A₀} {A₁} {A₂} a₀ a₁ a₂ t = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ Â₀₁ x₀ x₁ → El~ Â₁₂ x₁ x₂ → El~ (t Â₀₁ Â₁₂) x₀ x₂

transEl⁻¹-T : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → transU-T a₀ a₁ a₂ → _
transEl⁻¹-T {A₀} {A₁} {A₂} a₀ a₁ a₂ t = (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ (symU a₀ a₁ Â₀₁) x₁ x₀ → El~ (t Â₀₁ Â₁₂) x₀ x₂ → El~ Â₁₂ x₁ x₂

combo-T : {A₀ : _} (a₀ : in-U A₀) {A₁ : _} (a₁ : in-U A₁) {A₂ : _} (a₂ : in-U A₂) → _
combo-T a₀ a₁ a₂ =
  Σ (coeEl-T a₀ a₁) λ coeEl →
  Σsp (coeEl⁻¹-T a₀ a₁) λ coeEl⁻¹ →
  cohEl-T a₀ a₁ coeEl ×p cohEl⁻¹-T a₀ a₁ coeEl⁻¹ ×p
  Σp (transU-T a₀ a₁ a₂) λ transU →
  transEl-T a₀ a₁ a₂ transU ×p transEl⁻¹-T a₀ a₁ a₂ transU

combo-simple : {A₀ : _} (a₀ : in-U A₀) {A₁ : _} (a₁ : in-U A₁) {A₂ : _} (a₂ : in-U A₂)
             → combo-T a₀ a₁ a₂
combo-simple =
  simple-just-U.ind-in-U (λ a₀ → {A₁ : _} (a₁ : in-U A₁) {A₂ : _} (a₂ : in-U A₂) → combo-T a₀ a₁ a₂)
    (simple-just-U.ind-in-U (λ a₁ → {A₂ : _} (a₂ : in-U A₂) → combo-T _ a₁ a₂)
      (simple-just-U.ind-in-U (λ a₂ → combo-T _ _ a₂)
        ((λ _ x → x) ,Σ ((λ _ x → x) ,sp
         ((λ _ → λ { ff → ttp ; tt → ttp }) ,p (λ _ → λ { ff → ttp ; tt → ttp }) ,p
         ((λ _ _ → tr (_ ,Σ bool~)) ,p
         ((λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }) ,p
          (λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }))))))
        λ _ _ → (λ _ x → x) ,Σ ((λ _ x → x) ,sp (((λ _ → λ { ff → ttp ; tt → ttp }) ,p
          λ _ → λ { ff → ttp ; tt → ttp }) ,p ((λ { w (tr ()) }) ,p ((λ { w (tr ()) }) ,p λ { w (tr ()) })))))
      λ _ _ _ → (λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ ((λ w _ → ⊥pelim (withTrunc w λ ())) ,sp
          (((λ w _ → ⊥pelimp (withTrunc w λ ())) ,p λ w _ → ⊥pelimp (withTrunc w λ ())) ,p
            ((λ { (tr ()) }) ,p ((λ { (tr ()) }) ,p λ { (tr ()) })))))
    λ {_} {a₀} a₀ᴰ {_} {a₀~} {_} {b₀} b₀ᴰ {_} {b₀~} → simple-just-U.ind-in-U (λ a₁ → {A₂ : _} (a₂ : in-U A₂) → combo-T _ a₁ a₂)
      (λ _ → (λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ ((λ w _ → ⊥pelim (withTrunc w λ ())) ,sp
              (((λ w _ → ⊥pelimp (withTrunc w λ ())) ,p λ w _ → ⊥pelimp (withTrunc w λ ())) ,p
              ((λ { (tr ()) }) ,p ((λ { (tr ()) }) ,p λ { (tr ()) })))))
      λ {_} {a₁} a₁ᴰ {_} {a₁~} {_} {b₁} b₁ᴰ {_} {b₁~} → simple-just-U.ind-in-U (λ a₂ → combo-T _ _ a₂)
        (let
             coeEl-a : {A : _} (y : in-U A) → coeEl-T a₀ y
             coeEl-a y = proj₁ (a₀ᴰ y y)
         
             cohEl-a : {A : _} (y : in-U A) → cohEl-T a₀ y _
             cohEl-a y = proj₁p (proj₁p (proj₂sp (proj₂ (a₀ᴰ y y))))
         
             coeEl-b : ∀{A} (x : _) (y : in-U A) -> coeEl-T (b₀ x) y
             coeEl-b = λ x y → proj₁ (b₀ᴰ x y y)
         
             coeEl⁻¹-a : {A : _} (y : in-U A) → coeEl⁻¹-T a₀ y
             coeEl⁻¹-a y = proj₁sp (proj₂ (a₀ᴰ y y))
         
             coeEl⁻¹-b : {A : _} (x : _) (y : in-U A) → coeEl⁻¹-T (b₀ x) y
             coeEl⁻¹-b x y = proj₁sp (proj₂ (b₀ᴰ x y y))
         
             cohEl⁻¹-a : {A : _} (y : in-U A) → cohEl⁻¹-T a₀ y _
             cohEl⁻¹-a y = proj₂p (proj₁p (proj₂sp (proj₂ (a₀ᴰ y y))))
         
             cohEl⁻¹-b : {A : _} (x : _) (y : in-U A) → cohEl⁻¹-T (b₀ x) y _
             cohEl⁻¹-b x y = proj₂p (proj₁p (proj₂sp (proj₂ (b₀ᴰ x y y))))
         
             transEl-a : {A' A'' : _} (y : in-U A') (z : in-U A'') -> transEl-T a₀ y z _
             transEl-a y z = proj₁p (proj₂p (proj₂p (proj₂sp (proj₂ (a₀ᴰ y z)))))
         
             cohEl-b : ∀{A} (x : _) (y : in-U A) -> cohEl-T (b₀ x) y _
             cohEl-b = λ x y → proj₁p (proj₁p (proj₂sp (proj₂ (b₀ᴰ x y y))))
         
             transU-b : {A₀ A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂) → transU-T (b₀ x) y z
             transU-b x y z = proj₁p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z))))
         
             transEl-b : {A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂)
                         → transEl-T (b₀ x) y z _
             transEl-b x y z = proj₁p (proj₂p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z)))))
         
             transEl⁻¹-a : {A₁ A₂ : _} (y : in-U A₁) (z : in-U A₂)
                         → transEl⁻¹-T a₀ y z _
             transEl⁻¹-a y z = proj₂p (proj₂p (proj₂p (proj₂sp (proj₂ (a₀ᴰ y z)))))
         
             transEl⁻¹-b : {A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂)
                         → transEl⁻¹-T (b₀ x) y z _
             transEl⁻¹-b x y z = proj₂p (proj₂p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z)))))
         
             h1 : coeEl-T (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~)
             h1 = λ { w (f₀ ,sp f₀~) → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                  (λ x₁ → let x₀ = coeEl⁻¹-a a₁ Â₀₁ x₁ ; x₀₁ = cohEl⁻¹-a a₁ Â₀₁ x₁ in coeEl-b x₀ (b₁ x₁) (B̂₀₁ x₀₁) (f₀ x₀)) ,sp
                  (λ x₀₁ x₁₁ x-₁ →
                    let x₀₀ = coeEl⁻¹-a a₁ Â₀₁ x₀₁ ; x₀- = cohEl⁻¹-a a₁ Â₀₁ x₀₁ in
                    let x₁₀ = coeEl⁻¹-a a₁ Â₀₁ x₁₁ ; x₁- = cohEl⁻¹-a a₁ Â₀₁ x₁₁ in
                    let x-₀ = transEl-a a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (transEl-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- (toEl~ a₁~ (un↑ps x-₁))) (symEl a₀ a₁ Â₀₁ x₁-) in
                    let y₀₀ = f₀ x₀₀ ; y₀₁ = coeEl-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ ; y₀- = cohEl-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ in
                    let y₁₀ = f₀ x₁₀ ; y₁₁ = coeEl-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ ; y₁- = cohEl-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ in
                    let y-₀ = f₀~ x₀₀ x₁₀ (mk↑ps (fromEl~ a₀~ x-₀)) in
                    fromEl~ (b₁~ (un↑ps x-₁)) (transEl⁻¹-b x₀₀ (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ b₁~ (un↑ps x-₁))) (symEl (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀-)
                      (transEl-b x₀₀ (b₀ x₁₀) (b₁ x₁₁) (tr (_ ,Σ b₀~ (fromEl~ a₀~ x-₀))) (B̂₀₁ x₁-) (toEl~ (b₀~ (fromEl~ a₀~ x-₀)) y-₀) y₁- ))) }
         
             h2 : coeEl⁻¹-T (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~)
             h2 = λ { w (f₁ ,sp f₁~) → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                   (λ x₀ → let x₁ = coeEl-a a₁ Â₀₁ x₀ ; x₀₁ = cohEl-a a₁ Â₀₁ x₀ in coeEl⁻¹-b x₀ (b₁ x₁) (B̂₀₁ x₀₁) (f₁ x₁)) ,sp
                   (λ x₀₀ x₁₀ x-₀ →
                     let x₀₁ = coeEl-a a₁ Â₀₁ x₀₀ ; x₀- = cohEl-a a₁ Â₀₁ x₀₀ in
                     let x₁₁ = coeEl-a a₁ Â₀₁ x₁₀ ; x₁- = cohEl-a a₁ Â₀₁ x₁₀ in
                     let x-₁ = transEl⁻¹-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) (transEl⁻¹-a a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (symEl a₀ a₁ Â₀₁ x₀-) (toEl~ a₀~ (un↑ps x-₀))) x₁- in
                     let y₀₁ = f₁ x₀₁ ; y₀₀ = coeEl⁻¹-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ ; y₀- = cohEl⁻¹-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ in
                     let y₁₁ = f₁ x₁₁ ; y₁₀ = coeEl⁻¹-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ ; y₁- = cohEl⁻¹-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ in
                     let y-₁ = f₁~ x₀₁ x₁₁ (mk↑ps (fromEl~ a₁~ x-₁)) in
                   fromEl~ (b₀~ (un↑ps x-₀)) (transEl-b x₀₀ (b₁ x₁₁) (b₀ x₁₀) (B̂₀₁ (transEl-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- x-₁)) (symU _ _ (B̂₀₁ x₁-)) (transEl-b x₀₀ (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ b₁~ (fromEl~ a₁~ x-₁))) y₀- (toEl~ (b₁~ (fromEl~ a₁~ x-₁)) y-₁) ) (symEl (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁-))) }
         
             h3 = λ { w (f₀ ,sp f₀~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                     let x₂ = coeEl⁻¹-a a₁ Â₀₁ x₁ ; x₂₁ = cohEl⁻¹-a a₁ Â₀₁ x₁ ; x₀₂ = transEl-a a₁ a₀ Â₀₁ (symU _ _ Â₀₁) (un↑ps x₀₁) (symEl _ _ Â₀₁ x₂₁) in
                       transEl-b x₀ (b₀ x₂) (b₁ x₁) (tr (_ ,Σ b₀~ (fromEl~ a₀~ x₀₂))) (B̂₀₁ x₂₁) (toEl~ (b₀~ (fromEl~ a₀~ x₀₂))
                         (f₀~ _ _ (mk↑ps (fromEl~ a₀~ x₀₂)))) (cohEl-b x₂ (b₁ x₁) (B̂₀₁ x₂₁) (f₀ x₂)) }
                   
             h4 = λ { w (f₁ ,sp f₁~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                    let x₂ = coeEl-a a₁ Â₀₁ x₀ ; x₀₂ = cohEl-a a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹-a a₁ a₁ Â₀₁ (tr (_ ,Σ a₁~))
                               (symEl a₀ a₁ Â₀₁ (un↑ps x₀₁)) x₀₂ ; x₂₁ = fromEl~ a₁~ (symEl a₁ a₁ (tr (_ ,Σ a₁~)) x₁₂) in
                        transEl-b x₀ (b₁ x₂) (b₁ x₁) (B̂₀₁ x₀₂) (tr (_ ,Σ b₁~ x₂₁)) (cohEl⁻¹-b x₀ (b₁ x₂) (B̂₀₁ x₀₂) (f₁ x₂)) (toEl~ (b₁~ x₂₁) (f₁~ _ _ (mk↑ps x₂₁))) }

         in h1 ,Σ (h2 ,sp ((h3 ,p h4) ,p ((λ { w (tr ()) }) ,p ((λ { w (tr ()) }) ,p λ { w (tr ()) })))))
        λ {_} {a₂} a₂ᴰ {_} {a₂~} {_} {b₂} b₂ᴰ {_} {b₂~} →
          let
                coeEl-a : {A : _} (y : in-U A) → coeEl-T a₀ y
                coeEl-a y = proj₁ (a₀ᴰ y y)
            
                cohEl-a : {A : _} (y : in-U A) → cohEl-T a₀ y _
                cohEl-a y = proj₁p (proj₁p (proj₂sp (proj₂ (a₀ᴰ y y))))
            
                coeEl-b : ∀{A} (x : _) (y : in-U A) -> coeEl-T (b₀ x) y
                coeEl-b = λ x y → proj₁ (b₀ᴰ x y y)
            
                coeEl⁻¹-a : {A : _} (y : in-U A) → coeEl⁻¹-T a₀ y
                coeEl⁻¹-a y = proj₁sp (proj₂ (a₀ᴰ y y))
            
                coeEl⁻¹-b : {A : _} (x : _) (y : in-U A) → coeEl⁻¹-T (b₀ x) y
                coeEl⁻¹-b x y = proj₁sp (proj₂ (b₀ᴰ x y y))
            
                cohEl⁻¹-a : {A : _} (y : in-U A) → cohEl⁻¹-T a₀ y _
                cohEl⁻¹-a y = proj₂p (proj₁p (proj₂sp (proj₂ (a₀ᴰ y y))))
            
                cohEl⁻¹-b : {A : _} (x : _) (y : in-U A) → cohEl⁻¹-T (b₀ x) y _
                cohEl⁻¹-b x y = proj₂p (proj₁p (proj₂sp (proj₂ (b₀ᴰ x y y))))
            
                transEl-a : {A' A'' : _} (y : in-U A') (z : in-U A'') -> transEl-T a₀ y z _
                transEl-a y z = proj₁p (proj₂p (proj₂p (proj₂sp (proj₂ (a₀ᴰ y z)))))
            
                cohEl-b : ∀{A} (x : _) (y : in-U A) -> cohEl-T (b₀ x) y _
                cohEl-b = λ x y → proj₁p (proj₁p (proj₂sp (proj₂ (b₀ᴰ x y y))))
            
                transU-a : {A₁ A₂ : _} (y : in-U A₁) (z : in-U A₂) → transU-T a₀ y z
                transU-a y z = proj₁p (proj₂p (proj₂sp (proj₂ (a₀ᴰ y z))))
            
                transU-b : {A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂) → transU-T (b₀ x) y z
                transU-b x y z = proj₁p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z))))
            
                transEl-b : {A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂)
                            → transEl-T (b₀ x) y z _
                transEl-b x y z = proj₁p (proj₂p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z)))))
            
                transEl⁻¹-a : {A₁ A₂ : _} (y : in-U A₁) (z : in-U A₂)
                            → transEl⁻¹-T a₀ y z _
                transEl⁻¹-a y z = proj₂p (proj₂p (proj₂p (proj₂sp (proj₂ (a₀ᴰ y z)))))
            
                transEl⁻¹-b : {A₁ A₂ : _} (x : _) (y : in-U A₁) (z : in-U A₂)
                            → transEl⁻¹-T (b₀ x) y z _
                transEl⁻¹-b x y z = proj₂p (proj₂p (proj₂p (proj₂sp (proj₂ (b₀ᴰ x y z)))))
            
                h1 = λ { w (f₀ ,sp f₀~) → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                     (λ x₁ → let x₀ = coeEl⁻¹-a a₁ Â₀₁ x₁ ; x₀₁ = cohEl⁻¹-a a₁ Â₀₁ x₁ in coeEl-b x₀ (b₁ x₁) (B̂₀₁ x₀₁) (f₀ x₀)) ,sp
                     (λ x₀₁ x₁₁ x-₁ →
                       let x₀₀ = coeEl⁻¹-a a₁ Â₀₁ x₀₁ ; x₀- = cohEl⁻¹-a a₁ Â₀₁ x₀₁ in
                       let x₁₀ = coeEl⁻¹-a a₁ Â₀₁ x₁₁ ; x₁- = cohEl⁻¹-a a₁ Â₀₁ x₁₁ in
                       let x-₀ = transEl-a a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (transEl-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- (toEl~ a₁~ (un↑ps x-₁))) (symEl a₀ a₁ Â₀₁ x₁-) in
                       let y₀₀ = f₀ x₀₀ ; y₀₁ = coeEl-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ ; y₀- = cohEl-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ in
                       let y₁₀ = f₀ x₁₀ ; y₁₁ = coeEl-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ ; y₁- = cohEl-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ in
                       let y-₀ = f₀~ x₀₀ x₁₀ (mk↑ps (fromEl~ a₀~ x-₀)) in
                       fromEl~ (b₁~ (un↑ps x-₁)) (transEl⁻¹-b x₀₀ (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ b₁~ (un↑ps x-₁))) (symEl (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀-)
                         (transEl-b x₀₀ (b₀ x₁₀) (b₁ x₁₁) (tr (_ ,Σ b₀~ (fromEl~ a₀~ x-₀))) (B̂₀₁ x₁-) (toEl~ (b₀~ (fromEl~ a₀~ x-₀)) y-₀) y₁- ))) }
            
                h2 = λ { w (f₁ ,sp f₁~) → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                      (λ x₀ → let x₁ = coeEl-a a₁ Â₀₁ x₀ ; x₀₁ = cohEl-a a₁ Â₀₁ x₀ in coeEl⁻¹-b x₀ (b₁ x₁) (B̂₀₁ x₀₁) (f₁ x₁)) ,sp
                      (λ x₀₀ x₁₀ x-₀ →
                        let x₀₁ = coeEl-a a₁ Â₀₁ x₀₀ ; x₀- = cohEl-a a₁ Â₀₁ x₀₀ in
                        let x₁₁ = coeEl-a a₁ Â₀₁ x₁₀ ; x₁- = cohEl-a a₁ Â₀₁ x₁₀ in
                        let x-₁ = transEl⁻¹-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) (transEl⁻¹-a a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (symEl a₀ a₁ Â₀₁ x₀-) (toEl~ a₀~ (un↑ps x-₀))) x₁- in
                        let y₀₁ = f₁ x₀₁ ; y₀₀ = coeEl⁻¹-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ ; y₀- = cohEl⁻¹-b x₀₀ (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ in
                        let y₁₁ = f₁ x₁₁ ; y₁₀ = coeEl⁻¹-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ ; y₁- = cohEl⁻¹-b x₁₀ (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ in
                        let y-₁ = f₁~ x₀₁ x₁₁ (mk↑ps (fromEl~ a₁~ x-₁)) in
                      fromEl~ (b₀~ (un↑ps x-₀)) (transEl-b x₀₀ (b₁ x₁₁) (b₀ x₁₀) (B̂₀₁ (transEl-a a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- x-₁)) (symU _ _ (B̂₀₁ x₁-)) (transEl-b x₀₀ (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ b₁~ (fromEl~ a₁~ x-₁))) y₀- (toEl~ (b₁~ (fromEl~ a₁~ x-₁)) y-₁) ) (symEl (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁-))) }
            
                h3 = λ { w (f₀ ,sp f₀~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                        let x₂ = coeEl⁻¹-a a₁ Â₀₁ x₁ ; x₂₁ = cohEl⁻¹-a a₁ Â₀₁ x₁ ; x₀₂ = transEl-a a₁ a₀ Â₀₁ (symU _ _ Â₀₁) (un↑ps x₀₁) (symEl _ _ Â₀₁ x₂₁) in
                          transEl-b x₀ (b₀ x₂) (b₁ x₁) (tr (_ ,Σ b₀~ (fromEl~ a₀~ x₀₂))) (B̂₀₁ x₂₁) (toEl~ (b₀~ (fromEl~ a₀~ x₀₂))
                            (f₀~ _ _ (mk↑ps (fromEl~ a₀~ x₀₂)))) (cohEl-b x₂ (b₁ x₁) (B̂₀₁ x₂₁) (f₀ x₂)) }
                      
                h4 = λ { w (f₁ ,sp f₁~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
                       let x₂ = coeEl-a a₁ Â₀₁ x₀ ; x₀₂ = cohEl-a a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹-a a₁ a₁ Â₀₁ (tr (_ ,Σ a₁~))
                                  (symEl a₀ a₁ Â₀₁ (un↑ps x₀₁)) x₀₂ ; x₂₁ = fromEl~ a₁~ (symEl a₁ a₁ (tr (_ ,Σ a₁~)) x₁₂) in
                           transEl-b x₀ (b₁ x₂) (b₁ x₁) (B̂₀₁ x₀₂) (tr (_ ,Σ b₁~ x₂₁)) (cohEl⁻¹-b x₀ (b₁ x₂) (B̂₀₁ x₀₂) (f₁ x₂)) (toEl~ (b₁~ x₂₁) (f₁~ _ _ (mk↑ps x₂₁))) }
            
                h5 : transU-T (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (π a₂ a₂~ b₂ b₂~)
                h5 = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
                      transU-a a₁ a₂ Â₀₁ Â₁₂ ,π~
                      λ {x₀}{x₂} x₀₂ → let x₁ = coeEl-a a₁ Â₀₁ x₀ ; x₀₁ = cohEl-a a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹-a a₁ a₂ Â₀₁ Â₁₂ (symEl a₀ a₁ Â₀₁ x₀₁) x₀₂ in
                        transU-b x₀ (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂)
            
                h6 : transEl-T (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (π a₂ a₂~ b₂ b₂~) h5
                h6 = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
                       λ f₀₁ f₁₂ x₀ x₂ x₀₂ → let x₁ = coeEl-a a₁ Â₀₁ x₀ ; x₀₁ = cohEl-a a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹-a a₁ a₂ Â₀₁ Â₁₂ (symEl a₀ a₁ Â₀₁ x₀₁) (un↑ps x₀₂) in
                       transEl-b x₀ (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂) (f₀₁ x₀ x₁ (mk↑ps x₀₁)) (f₁₂ x₁ x₂ (mk↑ps x₁₂))
            
                h7 : transEl⁻¹-T (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (π a₂ a₂~ b₂ b₂~) h5
                h7 = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
                       λ f₁₀ f₀₂ x₁ x₂ x₁₂ → let x₀ = coeEl⁻¹-a a₁ Â₀₁ x₁ ; x₀₁ = cohEl⁻¹-a a₁ Â₀₁ x₁ ; x₁₀ = symEl a₀ a₁ Â₀₁ x₀₁ ; x₀₂ = transEl-a a₁ a₂ Â₀₁ Â₁₂ x₀₁ (un↑ps x₁₂) in
                       transEl⁻¹-b x₀ (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ (un↑ps x₁₂)) (f₁₀ x₁ x₀ (mk↑ps x₁₀)) (f₀₂ x₀ x₂ (mk↑ps x₀₂))
        in h1 ,Σ (h2 ,sp ((h3 ,p h4) ,p (h5 ,p (h6 ,p h7))))

coeEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
coeEl a₀ a₁ = proj₁ (combo-simple a₀ a₁ a₁)

coeEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
coeEl⁻¹ a₀ a₁ = proj₁sp (proj₂ (combo-simple a₀ a₁ a₁))

cohEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
cohEl a₀ a₁ = proj₁p (proj₁p (proj₂sp (proj₂ (combo-simple a₀ a₁ a₁))))

cohEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → _
cohEl⁻¹ a₀ a₁ = proj₂p (proj₁p (proj₂sp (proj₂ (combo-simple a₀ a₁ a₁))))

transU  : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → _
transU a₀ a₁ a₂ = proj₁p (proj₂p (proj₂sp (proj₂ (combo-simple a₀ a₁ a₂))))

transEl : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → _
transEl a₀ a₁ a₂ = proj₁p (proj₂p (proj₂p (proj₂sp (proj₂ (combo-simple a₀ a₁ a₂)))))

transEl⁻¹ : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂) → _
transEl⁻¹ a₀ a₁ a₂ = proj₂p (proj₂p (proj₂p (proj₂sp (proj₂ (combo-simple a₀ a₁ a₂)))))

-- the actual definition of the universe

U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
U = mkTy
  (λ _ → ∣U∣)
  (λ _ → _~U_)
  refU
  (symU _ _)
  (transU _ _ _ )
  (λ _ Â → Â)
  (λ _ → refU)

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
El Â = mkTy
  (λ γ → ∣El∣ (∣ Â ∣t γ))
  (λ γ₀₁ → El~ (~t Â γ₀₁))
  (λ {γ} → refEl {∣ Â ∣t γ})
  (λ {_}{_}{γ₀₁} → symEl _ _ (~t Â γ₀₁))
  (λ {_}{_}{_}{γ₀₁}{γ₁₂} → transEl _ _ _ (~t Â γ₀₁) (~t Â γ₁₂))
  (λ {_}{_} γ₀₁ → coeEl _ _ (~t Â γ₀₁))
  (λ {_}{_} γ₀₁ → cohEl _ _ (~t Â γ₀₁))

ΠS : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
ΠS {Γ = Γ} Â B̂ = record {
  ∣_∣t = λ γ → _ ,Σ π
    (proj₂ (∣ Â ∣t γ))
    (in-El~ _ _ (refU (∣ Â ∣t γ)))
    (λ x → proj₂ (∣ B̂ ∣t (γ ,Σ x)))
    {λ x₀₁ → El~ (~t B̂ (refC Γ γ ,p x₀₁))}
    (λ x₀₁ → in-El~ _ _ (~t B̂ (refC Γ γ ,p x₀₁))) ;
  ~t = λ {γ₀}{γ₁} γ₀₁ → tr (_ ,Σ π~
    (in-El~ _ _ (~t Â γ₀₁))
    {B₀₁ = λ x₀₁ → El~ (~t B̂ (γ₀₁ ,p x₀₁))}
     λ x₀₁ → in-El~ _ _ (~t B̂ (γ₀₁ ,p x₀₁))) }

BoolS : ∀{i}{Γ : Con i} → Tm Γ U
BoolS = record {
  ∣_∣t = λ _ → _ ,Σ bool ;
  ~t = λ _ → tr (_ ,Σ bool~) }

