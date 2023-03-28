{-# OPTIONS --prop --without-K #-}

module Setoid.Sets3.encoding where

open import Setoid.lib
open import Setoid.Sets3.mini-univ
open import Relation.Binary.PropositionalEquality

variable
  A : U
  B : El A → U
  A₀ A₁ : U
  A~ : El A -> El A -> P
  A₀~ : El A₀ → El A₀ → P
  A₁~ : El A₁ → El A₁ → P
  A₀₁ : El A₀ → El A₁ → P
  B₀ : El A₀ → U
  B₁ : El A₁ → U

data in-Uₚ : U → Set₁
data in-U~ₚ : (A₀ A₁ : U)(A₀₁ : El A₀ → El A₁ → P) → Set₁

data in-Uₚ where
  boolₚ : in-Uₚ 𝟚-U
  πₚ : (aₚ : in-Uₚ A) (a~ₚ : in-U~ₚ A A A~)
       (bₚ : (x : El A) → in-Uₚ (B x))
       {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
       (b~ₚ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ (B x₀) (B x₁)(B~ x₀₁))
     → in-Uₚ (Σsp-U A B A~ B~)

data in-U~ₚ where
  bool~ₚ : in-U~ₚ 𝟚-U 𝟚-U _≟𝟚-P_
  π~ₚ :
    (a₀ : in-Uₚ A₀)(a₀~ : in-U~ₚ A₀ A₀ A₀~)
    (a₁ : in-Uₚ A₁)(a₁~ : in-U~ₚ A₁ A₁ A₁~)
    (a₀₁ : in-U~ₚ A₀ A₁ A₀₁)
    (b₀ : (x : El A₀) → in-Uₚ (B₀ x))
      {B₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → El (B₀ x₀) → El (B₀ x₁) → P}
      (b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ₚ (B₀ x₀) (B₀ x₁) (B₀~ x₀₁))
    (b₁ : (x : El A₁) → in-Uₚ (B₁ x))
      {B₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → El (B₁ x₀) → El (B₁ x₁) → P}
      (b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ₚ (B₁ x₀) (B₁ x₁) (B₁~ x₀₁))
    {B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P}
    (b₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ₚ (B₀ x₀) (B₁ x₁) (B₀₁ x₀₁)) → 
    in-U~ₚ
      (Σsp-U A₀ B₀ A₀~ B₀~)
      (Σsp-U A₁ B₁ A₁~ B₁~)
      λ x y → fun-≡-P A₀ A₁ A₀₁ B₀ B₁ B₀₁ (proj₁sp x) (proj₁sp y)

invert-πₚ : {A : U} {aₚ aₚ' : in-Uₚ A} {A~ : El A → El A → P} {a~ₚ a~ₚ' : in-U~ₚ _ _ A~}
           {B : El A → U} {bₚ bₚ' : (x : El A) -> in-Uₚ (B x)}
           {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
           {b~ₚ b~ₚ' : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ _ _ (B~ x₀₁)}
          → πₚ aₚ a~ₚ bₚ b~ₚ ≡ πₚ aₚ' a~ₚ' bₚ' b~ₚ'
          → (aₚ ≡ aₚ')
          × (a~ₚ ≡ a~ₚ')
          × (bₚ ≡ bₚ')
          × (_≡_ {A = {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ _ _ (B~ x₀₁)} b~ₚ b~ₚ')
invert-πₚ refl = ((refl ,Σ refl) ,Σ refl) ,Σ refl

data in-Uₜ : {A : U} → in-Uₚ A → Prop₁
data in-U~ₜ : (A₀ A₁ : U) (a₀ : in-Uₚ A₀)(a₁ : in-Uₚ A₁){A₀₁ : El A₀ → El A₁ → P} → in-U~ₚ A₀ A₁ A₀₁ → Prop₁

data in-Uₜ where
  boolₜ : in-Uₜ boolₚ
  πₜ :
    {aₚ : in-Uₚ A}(a : in-Uₜ aₚ){a~ₚ : in-U~ₚ A A A~}(a~ : in-U~ₜ A A aₚ aₚ a~ₚ)
    {bₚ : (x : El A) → in-Uₚ (B x)}(b : (x : El A) → in-Uₜ (bₚ x))
    {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
    {b~ₚ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₚ (B x₀) (B x₁)(B~ x₀₁)} →
    (b~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ₜ (B x₀) (B x₁) (bₚ x₀) (bₚ x₁) (b~ₚ x₀₁)) →
    in-Uₜ (πₚ aₚ a~ₚ bₚ b~ₚ)

data in-U~ₜ where
  bool~ₜ : in-U~ₜ 𝟚-U 𝟚-U boolₚ boolₚ bool~ₚ
  π~ₜ :
    {a₀ₚ : in-Uₚ A₀}(a₀ : in-Uₜ a₀ₚ)
    {a₀~ₚ : in-U~ₚ A₀ A₀ A₀~}(a₀~ : in-U~ₜ A₀ A₀ a₀ₚ a₀ₚ a₀~ₚ)
    {a₁ₚ : in-Uₚ A₁}(a₁ : in-Uₜ a₁ₚ)
    {a₁~ₚ : in-U~ₚ A₁ A₁ A₁~}(a₁~ : in-U~ₜ A₁ A₁ a₁ₚ a₁ₚ a₁~ₚ)
    {a₀₁ₚ : in-U~ₚ A₀ A₁ A₀₁}(a₀₁ : in-U~ₜ A₀ A₁ a₀ₚ a₁ₚ a₀₁ₚ)
    {b₀ₚ : (x : El A₀) → in-Uₚ (B₀ x)}(b₀ : (x : El A₀) → in-Uₜ (b₀ₚ x))
    {B₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → El (B₀ x₀) → El (B₀ x₁) → P}
    {b₀~ₚ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ₚ (B₀ x₀) (B₀ x₁) (B₀~ x₀₁)}
    (b₀~ : {x₀ x₁ : El A₀}(x₀₁ : ElP (A₀~ x₀ x₁)) → in-U~ₜ (B₀ x₀) (B₀ x₁) (b₀ₚ x₀) (b₀ₚ x₁) (b₀~ₚ x₀₁))
    {b₁ₚ : (x : El A₁) → in-Uₚ (B₁ x)}(b₁ : (x : El A₁) → in-Uₜ (b₁ₚ x))
    {B₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → El (B₁ x₀) → El (B₁ x₁) → P}
    {b₁~ₚ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ₚ (B₁ x₀) (B₁ x₁) (B₁~ x₀₁)}
    (b₁~ : {x₀ x₁ : El A₁}(x₀₁ : ElP (A₁~ x₀ x₁)) → in-U~ₜ (B₁ x₀) (B₁ x₁) (b₁ₚ x₀) (b₁ₚ x₁) (b₁~ₚ x₀₁))
    {B₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → El (B₀ x₀) → El (B₁ x₁) → P}
    {b₀₁ₚ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ₚ (B₀ x₀) (B₁ x₁) (B₀₁ x₀₁)}
    (b₀₁ : {x₀ : El A₀}{x₁ : El A₁}(x₀₁ : ElP (A₀₁ x₀ x₁)) → in-U~ₜ (B₀ x₀) (B₁ x₁) (b₀ₚ x₀) (b₁ₚ x₁) (b₀₁ₚ x₀₁)) →
    in-U~ₜ
      (Σsp-U A₀ B₀ A₀~ B₀~)
      (Σsp-U A₁ B₁ A₁~ B₁~)
      (πₚ a₀ₚ a₀~ₚ b₀ₚ b₀~ₚ) (πₚ a₁ₚ a₁~ₚ b₁ₚ b₁~ₚ)
      (π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ b₀₁ₚ)

in-U : U -> Set₁
in-U x = Σsp (in-Uₚ x) in-Uₜ

in-U~ : (A₀ A₁ : U) (a₀ : in-U A₀)(a₁ : in-U A₁)(A₀₁ : El A₀ -> El A₁ -> P) → Set₁
in-U~ A₀ A₁ a₀ a₁ A₀₁ = Σsp (in-U~ₚ A₀ A₁ A₀₁) (in-U~ₜ A₀ A₁ (proj₁sp a₀) (proj₁sp a₁))

bool : in-U 𝟚-U
bool = boolₚ ,sp boolₜ

π : {A : U}(a : in-U A){A~ : El A -> El A -> P}(a~ : in-U~ A A a a A~)
    {B : El A -> U}
    (b : (x : El A) → in-U (B x))
    {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
    (b~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ (B x₀) (B x₁) (b x₀) (b x₁) (B~ x₀₁))
   → in-U (Σsp-U A B A~ B~)
π (aₚ ,sp a) (a~ₚ ,sp a~) b b~ =
  πₚ aₚ a~ₚ (λ x → proj₁sp (b x)) (λ x₀₁ → proj₁sp (b~ x₀₁)) ,sp
  πₜ a a~ (λ x → proj₂sp (b x)) (λ x₀₁ → proj₂sp (b~ x₀₁))

bool~ : in-U~ 𝟚-U 𝟚-U bool bool (λ x₀ x₁ → x₀ ≟𝟚-P x₁)
bool~ = bool~ₚ ,sp bool~ₜ

π~ : {A₀ : U}{a₀ : in-U A₀}{A₀~ : El A₀ → El A₀ → P}{a₀~ : in-U~ A₀ A₀ a₀ a₀ A₀~}
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
      
     → in-U~ _ _ (π a₀ a₀~ b₀ {B₀~} b₀~) (π a₁ a₁~ b₁ {B₁~} b₁~) _
π~ {A₀}{a₀ₚ ,sp a₀}{A₀~}{a₀~ₚ ,sp a₀~}{A₁}{a₁ₚ ,sp a₁}{A₁~}{a₁~ₚ ,sp a₁~}{A₀₁}(a₀₁ₚ ,sp a₀₁){B₀}{b₀}{B₀~}{b₀~}{B₁}{b₁}{B₁~}{b₁~}{B₀₁} b₀₁ =
  π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ a₀₁ₚ (λ x → proj₁sp (b₀ x)) (λ x₀₁ → proj₁sp (b₀~ x₀₁)) (λ x → proj₁sp (b₁ x)) (λ x₀₁ → proj₁sp (b₁~ x₀₁)) (λ x₀₁ → proj₁sp (b₀₁ x₀₁)) ,sp
  π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ (λ x → proj₂sp (b₀ x)) (λ x₀₁ → proj₂sp (b₀~ x₀₁)) (λ x → proj₂sp (b₁ x)) (λ x₀₁ → proj₂sp (b₁~ x₀₁)) (λ x₀₁ → proj₂sp (b₀₁ x₀₁))

-- invert-π : {A : U} {a a' : in-U A} {A~ : El A → El A → P} {a~ : in-U~ _ _ a a A~} {a~' : in-U~ _ _ a' a' A~}
--            {B : El A → U} {b b' : (x : El A) -> in-U (B x)}
--            {B~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → El (B x₀) → El (B x₁) → P}
--            {b~ : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ _ _ (b x₀) (b x₁) (B~ x₀₁)}
--            {b~' : {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ _ _ (b' x₀) (b' x₁) (B~ x₀₁)}
--           → π a a~ b b~ ≡ π a' a~' b' b~'
--           → Σ (a ≡ a') λ e → Σ (b ≡ b') λ e'
--           → (subst (λ x → in-U~ A A x x A~) e a~ ≡ a~')
--           × (_≡_ {A = {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ _ _ (b' x₀) (b' x₁) (B~ x₀₁)}
--                  (subst (λ x → {x₀ x₁ : El A}(x₀₁ : ElP (A~ x₀ x₁)) → in-U~ _ _ (x x₀) (x x₁) (B~ x₀₁)) e' b~) b~')
-- invert-π {A} {aₚ ,sp aₜ} {aₚ' ,sp aₜ'}
--          {A~} {a~ₚ ,sp a~ₜ} {a~ₚ' ,sp a~ₜ'}
--              eq = goal {!proj₂ (invert-πₚ (cong proj₁sp eq))!} {!!}
--   where
--     goal : aₚ ≡ aₚ' -> a~ₚ ≡ a~ₚ' -> _
--     goal refl refl = refl ,Σ ({!!} ,Σ (refl ,Σ {!!}))
-- -- rewrite proj₁ (proj₁ (proj₁ (invert-πₚ (cong proj₁sp eq)))) = {!!} ,Σ {!!}
