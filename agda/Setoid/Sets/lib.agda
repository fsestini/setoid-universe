{-# OPTIONS --allow-unsolved-metas --without-K --prop #-}

module Setoid.Sets.lib where

-- it is not allowed to open this module outside of Setoid

open import Agda.Primitive
open import Setoid.lib

data in-U : Set → Set₁
data in-U~ : {A₀ A₁ : Set}(a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : A₀ → A₁ → Prop) → Set₁

data in-U where
  bool : in-U 𝟚
  π : {A : Set}(a : in-U A){A~ : A → A → Prop}(a~ : in-U~ a a A~)
      
      {B : A → Set}(b : (x : A) → in-U (B x))
      {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
      (b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)) →
      
      in-U (Σsp ((x : A) → B x) (λ f → (x₀ x₁ : A)(x₀₁ : ↑ps (A~ x₀ x₁)) → B~ (un↑ps x₀₁) (f x₀) (f x₁)))

data in-U~ where
  bool~ : in-U~ bool bool λ x₀ x₁ → x₀ ≟𝟚 x₁
  π~ : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
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

module simple
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Set j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ (b₀₁ x₀₁)) → 
    in-U~ᴰ (π~ {a₀~ = a₀~}{a₁~ = a₁~} a₀₁ {b₀~ = b₀~}{b₁~ = b₁~} b₀₁))
  where
    
  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ a₀₁
  ind-in-U bool = boolᴰ
  ind-in-U (π a {A~ = A~} a~ b b~) = πᴰ (ind-in-U a) (ind-in-U~ a~) (λ x → ind-in-U (b x)) (λ x₀₁ → ind-in-U~ (b~ x₀₁))
  ind-in-U~ bool~ = bool~ᴰ
  ind-in-U~ (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁) =
    π~ᴰ (ind-in-U a₀) (ind-in-U~ a₀~) (ind-in-U a₁) (ind-in-U~ a₁~) (ind-in-U~ a₀₁)
      (λ x → ind-in-U (b₀ x)) (λ x → ind-in-U~ (b₀~ x)) (λ x → ind-in-U (b₁ x)) (λ x → ind-in-U~ (b₁~ x)) (λ x₀₁ → ind-in-U~ (b₀₁ x₀₁))

module double
  {i}
  (in-Uᴰ : ∀{A⁰ A¹ : Set} → in-U A⁰ → in-U A¹ → Set i)
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
  {-
  ind-in-U bool bool = boolboolᴰ
  ind-in-U bool (π a a~ b b~) = boolπᴰ a a~ b b~
  ind-in-U (π a a~ b b~) bool = πboolᴰ a a~ b b~
  ind-in-U (π a⁰ a~⁰ b⁰ b~⁰) (π a¹ a~¹ b¹ b~¹) = ππᴰ (ind-in-U a⁰ a¹) a~⁰ a~¹ (λ x⁰ x¹ → ind-in-U (b⁰ x⁰) (b¹ x¹)) b~⁰ b~¹
  -}

module _
  {i}
  (theT : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → Set i)
  (b-b-b : theT bool bool bool)
  (b-b-p : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
         → theT bool bool (π a a~ b b~))
  (b-p-x : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
           {A' : Set} {x : in-U A'}
         → theT bool (π a a~ b b~) x)
  (p-b-x : {A : Set} {a : in-U A} {A~ : A -> A -> Prop} {a~ : in-U~ a a A~}
           {B : A -> Set} {b : (x : A) -> in-U (B x)}
           {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
           {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
           {A' : Set} {x : in-U A'}
         → theT (π a a~ b b~) bool x)
  (p-p-b : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
           {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
         → theT a₁ a₀ a₀
         → theT a₀ a₁ a₀
         → theT a₁ a₁ a₀
         → ((x₀ x₁ : A₀) (x₂ : A₁) → theT (b₀ x₀) (b₀ x₁) (b₁ x₂))
         → ((x₀ : A₁) (x₁ : A₀) (x₂ : A₁) → theT (b₁ x₀) (b₀ x₁) (b₁ x₂))
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₁) → theT (b₀ x₀) (b₁ x₁) (b₁ x₂))
         → theT (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) bool)
  (p-p-p : {A₀ : Set}{a₀ : in-U A₀}{A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}
           {A₁ : Set}{a₁ : in-U A₁}{A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}
           {A₂ : Set}{a₂ : in-U A₂}{A₂~ : A₂ → A₂ → Prop}{a₂~ : in-U~ a₂ a₂ A₂~}
           {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}
           {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
           {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
           {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}
           {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
           {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
           {B₂ : A₂ → Set}{b₂ : (x₁ : A₂) → in-U (B₂ x₁)}
           {B₂~ : {x₀ x₁ : A₂}(x₀₁ : A₂~ x₀ x₁) → B₂ x₀ → B₂ x₁ → Prop}
           {b₂~ : {x₀ x₁ : A₂}(x₀₁ : A₂~ x₀ x₁) → in-U~ (b₂ x₀) (b₂ x₁) (B₂~ x₀₁)}
         → theT a₁ a₀ a₀ -- a100
         → theT a₀ a₁ a₀ -- a010
         → theT a₁ a₁ a₀ -- a110
         → theT a₁ a₀ a₁ -- a101
         → theT a₀ a₁ a₂
         → theT a₀ a₂ a₁
         → theT a₀ a₁ a₁
         → theT a₂ a₁ a₁
         → ((x₀ x₁ : A₀) (x₂ : A₁) → theT (b₀ x₀) (b₀ x₁) (b₁ x₂))        -- b001
         → ((x₀ : A₁) (x₁ : A₀) (x₂ : A₁) → theT (b₁ x₀) (b₀ x₁) (b₁ x₂)) -- b101
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₁) → theT (b₀ x₀) (b₁ x₁) (b₁ x₂)) -- b011
         → ((x₀ : A₀) (x₁ : A₁) (x₂ : A₂) → theT (b₀ x₀) (b₁ x₁) (b₂ x₂))
         → ((x₀ : A₁) (x₁ : A₁) (x₂ : A₂) → theT (b₁ x₀) (b₁ x₁) (b₂ x₂))
         → theT (π a₀ a₀~ b₀ b₀~) (π a₁ a₁~ b₁ b₁~) (π a₂ a₂~ b₂ b₂~))
  where

  triple : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → theT a₀ a₁ a₂
  triple = {!!}

module simpleProp
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Prop i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Prop j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ (b₀₁ x₀₁)) → 
    in-U~ᴰ (π~ {a₀~ = a₀~}{a₁~ = a₁~} a₀₁ {b₀~ = b₀~}{b₁~ = b₁~} b₀₁))
  where
    
  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ a₀₁
  ind-in-U bool = boolᴰ
  ind-in-U (π a {A~ = A~} a~ b b~) = πᴰ (ind-in-U a) (ind-in-U~ a~) (λ x → ind-in-U (b x)) (λ x₀₁ → ind-in-U~ (b~ x₀₁))
  ind-in-U~ bool~ = bool~ᴰ
  ind-in-U~ (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁) =
    π~ᴰ (ind-in-U a₀) (ind-in-U~ a₀~) (ind-in-U a₁) (ind-in-U~ a₁~) (ind-in-U~ a₀₁)
      (λ x → ind-in-U (b₀ x)) (λ x → ind-in-U~ (b₀~ x)) (λ x → ind-in-U (b₁ x)) (λ x → ind-in-U~ (b₁~ x)) (λ x₀₁ → ind-in-U~ (b₀₁ x₀₁))

module general
  {i}
  {j}
  (in-Uᴰ : ∀{A : Set} → in-U A → Set i)
  (in-U~ᴰ : {A₀ A₁ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₀₁ : A₀ → A₁ → Prop} → in-U~ a₀ a₁ A₀₁ → Prop j)
  (boolᴰ : in-Uᴰ bool)
  (πᴰ : {A : Set}{a : in-U A}(aᴰ : in-Uᴰ a){A~ : A → A → Prop}{a~ : in-U~ a a A~}(a~ᴰ : in-U~ᴰ aᴰ aᴰ a~)
    {B : A → Set}{b : (x : A) → in-U (B x)}(bᴰ : (x : A) → in-Uᴰ (b x))
    {B~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → B x₀ → B x₁ → Prop}
    {b~ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ (b x₀) (b x₁) (B~ x₀₁)}
    (b~ᴰ : {x₀ x₁ : A}(x₀₁ : A~ x₀ x₁) → in-U~ᴰ (bᴰ x₀) (bᴰ x₁) (b~ x₀₁)) → 
    in-Uᴰ (π a a~ b b~))
  (bool~ᴰ : in-U~ᴰ boolᴰ boolᴰ bool~)
  (π~ᴰ : {A₀ : Set}{a₀ : in-U A₀}(a₀ᴰ : in-Uᴰ a₀){A₀~ : A₀ → A₀ → Prop}{a₀~ : in-U~ a₀ a₀ A₀~}(a₀~ᴰ : in-U~ᴰ a₀ᴰ a₀ᴰ a₀~)
    {A₁ : Set}{a₁ : in-U A₁}(a₁ᴰ : in-Uᴰ a₁){A₁~ : A₁ → A₁ → Prop}{a₁~ : in-U~ a₁ a₁ A₁~}(a₁~ᴰ : in-U~ᴰ a₁ᴰ a₁ᴰ a₁~)
    {A₀₁ : A₀ → A₁ → Prop}{a₀₁ : in-U~ a₀ a₁ A₀₁}(a₀₁ᴰ : in-U~ᴰ a₀ᴰ a₁ᴰ a₀₁)
    {B₀ : A₀ → Set}{b₀ : (x₀ : A₀) → in-U (B₀ x₀)}(b₀ᴰ : (x₀ : A₀) → in-Uᴰ (b₀ x₀))
      {B₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → B₀ x₀ → B₀ x₁ → Prop}
      {b₀~ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ (b₀ x₀) (b₀ x₁) (B₀~ x₀₁)}
      (b₀~ᴰ : {x₀ x₁ : A₀}(x₀₁ : A₀~ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₀ᴰ x₁) (b₀~ x₀₁))
    {B₁ : A₁ → Set}{b₁ : (x₁ : A₁) → in-U (B₁ x₁)}(b₁ᴰ : (x₁ : A₁) → in-Uᴰ (b₁ x₁))
      {B₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → B₁ x₀ → B₁ x₁ → Prop}
      {b₁~ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ (b₁ x₀) (b₁ x₁) (B₁~ x₀₁)}
      (b₁~ᴰ : {x₀ x₁ : A₁}(x₀₁ : A₁~ x₀ x₁) → in-U~ᴰ (b₁ᴰ x₀) (b₁ᴰ x₁) (b₁~ x₀₁))
    {B₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → B₀ x₀ → B₁ x₁ → Prop}
    {b₀₁ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ (b₀ x₀) (b₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ᴰ : {x₀ : A₀}{x₁ : A₁}(x₀₁ : A₀₁ x₀ x₁) → in-U~ᴰ (b₀ᴰ x₀) (b₁ᴰ x₁) (b₀₁ x₀₁)) → 
    in-U~ᴰ (πᴰ a₀ᴰ a₀~ᴰ b₀ᴰ b₀~ᴰ) (πᴰ a₁ᴰ a₁~ᴰ b₁ᴰ b₁~ᴰ) (π~ {a₀~ = a₀~}{a₁~ = a₁~} a₀₁ {b₀~ = b₀~}{b₁~ = b₁~} b₀₁))
  where

  ind-in-U : ∀{A : Set}(a : in-U A) → in-Uᴰ a
  ind-in-U~ : ∀{A₀ A₁ : Set}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → in-U~ᴰ (ind-in-U a₀) (ind-in-U a₁) a₀₁
  ind-in-U bool = boolᴰ
  ind-in-U (π a {A~ = A~} a~ b b~) = πᴰ (ind-in-U a) (ind-in-U~ a~) (λ x → ind-in-U (b x)) (λ x₀₁ → ind-in-U~ (b~ x₀₁))
  ind-in-U~ bool~ = bool~ᴰ
  ind-in-U~ (π~ {a₀ = a₀}{a₀~ = a₀~}{a₁ = a₁}{a₁~ = a₁~} a₀₁ {b₀ = b₀}{b₀~ = b₀~}{b₁ = b₁}{b₁~ = b₁~} b₀₁) =
    π~ᴰ (ind-in-U a₀) (ind-in-U~ a₀~) (ind-in-U a₁) (ind-in-U~ a₁~) (ind-in-U~ a₀₁)
      (λ x → ind-in-U (b₀ x)) (λ x → ind-in-U~ (b₀~ x)) (λ x → ind-in-U (b₁ x)) (λ x → ind-in-U~ (b₁~ x)) (λ x₀₁ → ind-in-U~ (b₀₁ x₀₁))
