{-# OPTIONS --without-K --prop --rewriting #-}

module Setoid.SetsII-from-Sets3 where

import Setoid.Sets3.mini-univ-encoding as M
open import Setoid.lib
open import lib
open import irrel-eq public
open import Function

module E where

  data in-U : M.U -> Set₁
  data in-U~ : (A₀ A₁ : M.U) (a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : M.El A₀ -> M.El A₁ -> M.P) → Set₁

  data in-U where
    bool : in-U M.𝟚-U

    π : {A : M.U}(a : in-U A){A~ : M.El A -> M.El A -> M.P}(a~ : in-U~ A A a a A~)
        {B : M.El A -> M.U}
        (b : (x : M.El A) → in-U (B x))
        {B~ : {x₀ x₁ : M.El A}(x₀₁ : M.ElP (A~ x₀ x₁)) → M.El (B x₀) → M.El (B x₁) → M.P}
        (b~ : {x₀ x₁ : M.El A}(x₀₁ : M.ElP (A~ x₀ x₁)) → in-U~ (B x₀) (B x₁) (b x₀) (b x₁) (B~ x₀₁))
       → in-U (M.Σsp-U A B A~ B~)

  data in-U~ where
    bool~ : in-U~ M.𝟚-U M.𝟚-U bool bool (λ x₀ x₁ → x₀ M.≟𝟚-P x₁)
    π~ : {A₀ : M.U}{a₀ : in-U A₀}{A₀~ : M.El A₀ → M.El A₀ → M.P}{a₀~ : in-U~ A₀ A₀ a₀ a₀ A₀~}
         {A₁ : M.U}{a₁ : in-U A₁}{A₁~ : M.El A₁ → M.El A₁ → M.P}{a₁~ : in-U~ A₁ A₁ a₁ a₁ A₁~}
         {A₀₁ : M.El A₀ → M.El A₁ → M.P}(a₀₁ : in-U~ A₀ A₁ a₀ a₁ A₀₁)
    
         {B₀ : M.El A₀ → M.U}{b₀ : (x₀ : M.El A₀) → in-U (B₀ x₀)}
           {B₀~ : {x₀ x₁ : M.El A₀}(x₀₁ : M.ElP (A₀~ x₀ x₁)) → M.El (B₀ x₀) → M.El (B₀ x₁) → M.P}
           {b₀~ : {x₀ x₁ : M.El A₀}(x₀₁ : M.ElP (A₀~ x₀ x₁)) → in-U~ (B₀ x₀) (B₀ x₁) (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
         {B₁ : M.El A₁ → M.U}{b₁ : (x₁ : M.El A₁) → in-U (B₁ x₁)}
           {B₁~ : {x₀ x₁ : M.El A₁}(x₀₁ : M.ElP (A₁~ x₀ x₁)) → M.El (B₁ x₀) → M.El (B₁ x₁) → M.P}
           {b₁~ : {x₀ x₁ : M.El A₁}(x₀₁ : M.ElP (A₁~ x₀ x₁)) → in-U~ (B₁ x₀) (B₁ x₁) (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
         {B₀₁ : {x₀ : M.El A₀}{x₁ : M.El A₁}(x₀₁ : M.ElP (A₀₁ x₀ x₁)) → M.El (B₀ x₀) → M.El (B₁ x₁) → M.P}
         (b₀₁ : {x₀ : M.El A₀}{x₁ : M.El A₁}(x₀₁ : M.ElP (A₀₁ x₀ x₁)) → in-U~ (B₀ x₀) (B₁ x₁) (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁))
     → in-U~ _ _ (π a₀ a₀~ b₀ {B₀~} b₀~) (π a₁ a₁~ b₁ {B₁~} b₁~)
         λ x y → M.fun-≡-P A₀ A₁ A₀₁ B₀ B₁ B₀₁ (proj₁sp x) (proj₁sp y)


in-U : Set → Set₁
in-U A = Σ _ λ inu → E.in-U (A ,Σ inu)

in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁
in-U~ a₀ a₁ A₀₁ =
  Σ (∀ x y → M.in-P (A₀₁ x y)) λ inp
    → E.in-U~ (_ ,Σ proj₁ a₀) (_ ,Σ proj₁ a₁) (proj₂ a₀) (proj₂ a₁)
        (λ x y → A₀₁ x y ,Σ inp x y)

bool : in-U 𝟚
bool = _ ,Σ E.bool

π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
    {B : A → Set}(b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
    in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))
π a a~ b b~ = _ ,Σ E.π (proj₂ a) (proj₂ a~) (λ x → proj₂ (b x)) λ x₀₁ → proj₂ (b~ x₀₁)

bool~ : in-U~ bool bool λ x₀ x₁ → x₀ ≟𝟚 x₁
bool~ = _ ,Σ E.bool~

π~ :
  {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
  {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)
  {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
    {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
    {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
  {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
    {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
    {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
  {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
  (b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)) → 
  in-U~ (π a₀ a₀~ b₀ {B₀~} b₀~)
        (π a₁ a₁~ b₁ {B₁~} b₁~)
        (λ {(f₀ ,sp f₀~) (f₁ ,sp f₁~) → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (A₀₁ x₀ x₁)) → B₀₁ (un↑ps x₀₁) (f₀ x₀) (f₁ x₁)})
π~ a₀₁ b₀₁ = _ ,Σ E.π~ (proj₂ a₀₁) λ x₀₁ → proj₂ (b₀₁ x₀₁)

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

  elim-U' : ∀{u} (a : E.in-U u) → in-Uᴰ (proj₂ u ,Σ a)
  elim-U~' : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : _}
          (a₀₁ : E.in-U~ _ _ (proj₂ a₀) (proj₂ a₁) A₀₁)
          → in-U~ᴰ (elim-U' (proj₂ a₀)) (elim-U' (proj₂ a₁)) (_ ,Σ a₀₁)

  elim-U' E.bool = boolᴰ
  elim-U' (E.π a a~ b b~) = πᴰ (elim-U' a) (elim-U~' a~) (λ x → elim-U' (b x)) (λ x₀₁ → elim-U~' (b~ x₀₁))

  elim-U~' E.bool~ = bool~ᴰ
  elim-U~' (E.π~ a₀₁ b₀₁) = π~ᴰ _ _ _ _ (elim-U~' a₀₁) _ _ _ _ λ x₀₁ → elim-U~' (b₀₁ x₀₁)

  elim-U : {A : Set} (a : in-U A) → in-Uᴰ a
  elim-U a = elim-U' (proj₂ a)
  
  elim-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}
           (a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (elim-U a₀) (elim-U a₁) a₀₁
  elim-U~ a₀₁ = elim-U~' (proj₂ a₀₁)

  bool-β : elim-U bool ≡ boolᴰ
  bool-β = refl

  π-β :
    {A : Set}(a : in-U A){A~ : A -> A -> Prop}(a~ : in-U~ a a A~)
    {B : A -> Set}
    (b : (x : A) → in-U (B x))
    {B~ : {x₀ x₁ : A}(x₀₁ :  (A~ x₀ x₁)) → (B x₀) → (B x₁) → Prop}
    (b~ : {x₀ x₁ : A}(x₀₁ :  (A~ x₀ x₁)) → in-U~ (b x₀) (b x₁) (B~ x₀₁))
    → elim-U (π a a~ b b~)
    ≡ πᴰ (elim-U a) (elim-U~ a~) (λ x → elim-U (b x)) (λ x₀₁ → elim-U~ (b~ x₀₁))
  π-β a a~ b b~ = refl


  bool~-β : elim-U~ bool~ ≡ bool~ᴰ
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
     → elim-U~ (π~ {a₀ = a₀} {a₀~ = a₀~} {a₁ = a₁} {a₁~ = a₁~} a₀₁
                     {b₀ = b₀} {b₀~ = b₀~} {b₁ = b₁} {b₁~ = b₁~} b₀₁)
     ≡ π~ᴰ (elim-U a₀) (elim-U~ a₀~) (elim-U a₁) (elim-U~ a₁~) (elim-U~ a₀₁)
           (λ x₀ → elim-U (b₀ x₀)) (λ x₀₁ → elim-U~ (b₀~ x₀₁)) (λ x₁ → elim-U (b₁ x₁)) (λ x₀₁ → elim-U~ (b₁~ x₀₁)) λ x₀₁ → elim-U~ (b₀₁ x₀₁)
  π~-β a₀₁ b₀₁ = refl

