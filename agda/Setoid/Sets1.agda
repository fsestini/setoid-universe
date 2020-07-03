{-# OPTIONS --without-K --prop #-}

module Setoid.Sets1 where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF
open import Setoid.Sets1.lib

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ Set in-U

∣El∣ : ∣U∣ → Set
∣El∣ (A ,Σ a) = A

_~U_ : ∣U∣ → ∣U∣ → Prop₁
(A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) = Tr (Σ (A₀ → A₁ → Prop) (λ A₀₁ → in-U~ a₀ a₁ A₀₁))

El~  : ∀{A₀ A₁}{a₀ₚ : in-Uₚ A₀}(a₀ : in-Uₜ a₀ₚ){a₁ₚ : in-Uₚ A₁}(a₁ : in-Uₜ a₁ₚ)(a₀₁ : (A₀ ,Σ (a₀ₚ ,sp a₀)) ~U (A₁ ,Σ (a₁ₚ ,sp a₁))) → A₀ → A₁ → Prop
El~↔ : ∀{A₀ A₁}{a₀ₚ : in-Uₚ A₀}{a₀ : in-Uₜ a₀ₚ}{a₁ₚ : in-Uₚ A₁}{a₁ : in-Uₜ a₁ₚ}{A₀₁ : A₀ → A₁ → Prop}{a₀₁ₚ : in-U~ₚ A₀₁}(a₀₁ : in-U~ₜ a₀ₚ a₁ₚ a₀₁ₚ){x₀ : A₀}{x₁ : A₁} →
  (El~ {_}{_}{a₀ₚ} a₀ {a₁ₚ} a₁ (tr (A₀₁ ,Σ (a₀₁ₚ ,sp a₀₁))) x₀ x₁ ↔ A₀₁ x₀ x₁)

El~ {a₀ₚ = boolₚ} _ {boolₚ} _  _ x₀ x₁ = x₀ ≟𝟚 x₁
El~ {a₀ₚ = boolₚ} _ {πₚ a A~ b B~} _  w _ _ = ⊥pelim (withTrunc w λ ())
El~ {a₀ₚ = πₚ a A~ b b~} _ {boolₚ} _  w _ _ = ⊥pelim (withTrunc w λ ())
El~ {a₀ₚ = πₚ {A₀} a₀ₚ A₀~ b₀ₚ B₀~} π₀ₜ {πₚ {A₁} a₁ₚ A₁~ b₁ₚ B₁~} π₁ₜ w f₀ f₁ =
  (x₀ : A₀)
  (x₁ : A₁)
  (x₀₁ : El~
    {a₀ₚ = a₀ₚ}
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ _ _ _ _ _ _ _ _ _)) → a₀ })
    {a₁ₚ}
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ _ _ a₁ _ _ _ _ _ _ _)) → a₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ _ _ _ _ a₀₁ _ _ _ _ _)) → tr (_ ,Σ (_ ,sp a₀₁)) })
    x₀
    x₁) →
  El~
    {a₀ₚ = b₀ₚ x₀}
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ _ _ _ _ _ b₀ _ _ _ _)) → b₀ x₀ })
    {b₁ₚ x₁}
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ _ _ _ _ _ _ _ b₁ _ _)) → b₁ x₁ })
    (withTrunc w (λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → tr (_ ,Σ ((_ ,sp b₀₁ (proj₁p (El~↔ a₀₁) x₀₁)))) }))
    (proj₁sp f₀ x₀)
    (proj₁sp f₁ x₁)

El~↔ {a₀ₚ = boolₚ}{_}{boolₚ}{_} bool~ₜ = (λ x₀₁ → x₀₁) ,p (λ x₀₁ → x₀₁)
El~↔ {a₀ₚ = boolₚ}{_}{πₚ a A~ b B~}{_} ()
El~↔ {a₀ₚ = πₚ a A~ b b~}{_}{boolₚ}{_} ()
El~↔ {a₀ₚ = πₚ {A₀} a₀ₚ A₀~ b₀ₚ B₀~}{_}{πₚ {A₁} a₁ₚ A₁~ b₁ₚ B₁~}{_}(π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁) =
  (λ f₀₁ _ _ x₀₁ → proj₁p (El~↔ (b₀₁ x₀₁)) (f₀₁ _ _ (proj₂p (El~↔ a₀₁) x₀₁))) ,p
  (λ f₀₁ _ _ x₀₁ → proj₂p (El~↔ (b₀₁ (proj₁p (El~↔ a₀₁) x₀₁))) (f₀₁ _ _ (proj₁p (El~↔ a₀₁) x₀₁)))
{-
in-El~ : ∀{A₀ A₁}{a₀ₚ : in-Uₚ A₀}(a₀ : in-Uₜ a₀ₚ){a₁ₚ : in-Uₚ A₁}(a₁ : in-Uₜ a₁ₚ)
  (w : (A₀ ,Σ (a₀ₚ ,sp a₀)) ~U (A₁ ,Σ (a₁ₚ ,sp a₁))) →
  in-U~ (a₀ₚ ,sp a₀) (a₁ₚ ,sp a₁) (El~ a₀ a₁ w)
in-El~ {a₀ₚ = boolₚ} _ {boolₚ} _  w = bool~
in-El~ {a₀ₚ = boolₚ} _ {πₚ a A~ b B~} _ w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ₚ = πₚ a A~ b b~} _ {boolₚ} _ w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ₚ = πₚ {A₀} a₀ₚ {A₀~} a₀~ₚ {B₀} b₀ₚ {B₀~} b₀~ₚ} π₀ₜ {πₚ {A₁} a₁ₚ {A₁~} a₁~ₚ {B₁} b₁ₚ {B₁~} b₁~ₚ} π₁ₜ w =
  π~ₚ a₀ₚ a₀~ₚ a₁ₚ a₁~ₚ
    {El~
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ {A₀₁}{a₀₁ₚ} a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → tr (A₀₁ ,Σ (a₀₁ₚ ,sp a₀₁)) })}
    (proj₁sp (in-El~
    {a₀ₚ = a₀ₚ}(withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀ })
    {a₁ₚ}(withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → tr (_ ,Σ (_ ,sp a₀₁))})))
    b₀ₚ b₀~ₚ b₁ₚ b₁~ₚ
    {λ {x₀}{x₁} x₀₁ → El~
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀ x₀ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁ x₁ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ {B₀₁}{b₀₁ₚ} b₀₁)) → tr (B₀₁ x₀₁ ,Σ (b₀₁ₚ x₀₁ ,sp b₀₁ (proj₁p (El~↔ {a₀ = a₀}{_}{a₁} a₀₁) x₀₁))) })}
    (λ {x₀}{x₁} x₀₁ → proj₁sp (in-El~
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀ x₀ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁ x₁ })
      (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ {B₀₁}{b₀₁ₚ} b₀₁)) → tr (B₀₁ x₀₁ ,Σ (b₀₁ₚ x₀₁ ,sp b₀₁ (proj₁p (El~↔ {a₀ = a₀}{a₁ = a₁} a₀₁) x₀₁)))}))) ,sp
  {!!}
-}
{-
  π~
  {A₀}
  {a₀ₚ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀ }}
  {A₀~}
  {a₀~ₚ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀~ }}
  {A₁}
  {a₁ₚ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁ }}
  {A₁~}
  {a₁~ₚ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁~ }}
  {El~
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ {A₀₁}{a₀₁ₚ} a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → tr (A₀₁ ,Σ (a₀₁ₚ ,sp a₀₁)) })}
  (in-El~
    {a₀ₚ = a₀ₚ}(withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₀ })
    {a₁ₚ}(withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → a₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → tr (_ ,Σ (_ ,sp a₀₁))}))
  {B₀}
  {λ x → b₀ₚ x ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀ x }}
  {B₀~}
  {λ x₀₁ → b₀~ₚ x₀₁ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀~ x₀₁ }}
  {B₁}
  {λ x → b₁ₚ x ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁ x }}
  {B₁~}
  {λ x₀₁ → b₁~ₚ x₀₁ ,sp withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁~ x₀₁ }}
  {λ {x₀}{x₁} x₀₁ → El~
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀ x₀ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁ x₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ {B₀₁}{b₀₁ₚ} b₀₁)) → tr (B₀₁ x₀₁ ,Σ (b₀₁ₚ x₀₁ ,sp b₀₁ (proj₁p (El~↔ {a₀ = a₀}{_}{a₁} a₀₁) x₀₁))) })}
  (λ {x₀}{x₁} x₀₁ → in-El~
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₀ x₀ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)) → b₁ x₁ })
    (withTrunc w λ { (_ ,Σ (_ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ {B₀₁}{b₀₁ₚ} b₀₁)) → tr (B₀₁ x₀₁ ,Σ (b₀₁ₚ x₀₁ ,sp b₀₁ (proj₁p (El~↔ {a₀ = a₀}{a₁ = a₁} a₀₁) x₀₁)))}))
-}
refU : (Â : ∣U∣) → Â ~U Â
refU (_ ,Σ (boolₚ ,sp _)) = tr (_ ,Σ bool~)
refU (_ ,Σ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp πₜ a a~ b b~)) = tr (_ ,Σ (π~ₚ aₚ a~ₚ aₚ a~ₚ a~ₚ bₚ b~ₚ bₚ b~ₚ b~ₚ ,sp π~ₜ a a~ a a~ a~ b b~ b b~ b~))

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → El~ (proj₂sp (proj₂ Â)) (proj₂sp (proj₂ Â)) (refU Â) x x
refEl {Â = _ ,Σ (boolₚ ,sp _)} tt = ttp
refEl {Â = _ ,Σ (boolₚ ,sp _)} ff = ttp
refEl {Â = _ ,Σ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp πₜ a a~ b b~)} (f ,sp f~) x₀ x₁ x₀₁ =
  proj₂p (El~↔ {a₀ = b x₀}{a₁ = b x₁} (b~ (proj₁p (El~↔ {a₀ = a}{a₁ = a} a~) x₀₁))) (f~ _ _ (proj₁p (El~↔ {a₀ = a}{a₁ = a} a~) x₀₁))

symU : {Â₀ Â₁ : ∣U∣} → Â₀ ~U Â₁ → Â₁ ~U Â₀
symU {Â₀ = _ ,Σ (boolₚ ,sp _)}{Â₁ = _ ,Σ (boolₚ ,sp _)} bool~ = bool~
symU {Â₀ = _ ,Σ (boolₚ ,sp _)}{Â₁ = _ ,Σ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp πₜ a a~ b b~)} (tr ())
symU {Â₀ = _ ,Σ (πₚ {A} aₚ {A~} a~ₚ {B} bₚ {B~} b~ₚ ,sp πₜ a a~ b b~)}{Â₁ = _ ,Σ (boolₚ ,sp _)} (tr ())
symU
  {Â₀ = _ ,Σ (πₚ {A₀} aₚ₀ {A~₀} a~ₚ₀ {B₀} bₚ₀ {B~₀} b~ₚ₀ ,sp πₜ a₀ a~₀ b₀ b~y)}
  {Â₁ = _ ,Σ (πₚ {A₁} aₚ₁ {A~₁} a~ₚ₁ {B₁} bₚ₁ {B~₁} b~ₚ₁ ,sp πₜ a₁ a~₁ b₁ b~₁)} (tr (_ ,Σ w)) =
  {! ind-in-U~ (λ _ → ⊤p) {!!} {!!} {!!} {!!} {!!} w !}
--  tr (_ ,Σ {!π~!})
  -- instead of w: (π~ₚ aₚ₀ a~ₚ₀ aₚ₁ a~ₚ₁ a₀₁ₚ bₚ₀ b~ₚ₀ bₚ₁ b~ₚ₁ b₀₁ₚ ,sp π~ₜ a₀ a₀~ a₁ a₁~ a₀₁ b₀ b₀~ b₁ b₁~ b₀₁)

{-
symU  : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)
symEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} →
  El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr (symU a₀₁)) x₁ x₀

symU {a₀ = boolₚ ,sp _} {boolₚ ,sp _} bool~ = ? -- _ ,Σ bool~
symU {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) = ?
  _ ,Σ
  π~ (proj₂ (symU a₀₁))
     {B₀₁ = λ x₀₁ → proj₁ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (toEl~ (proj₂ (symU a₀₁)) x₀₁)))))}
     (λ x₀₁ →  proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (toEl~ (proj₂ (symU a₀₁)) x₀₁))))))

symEl = ?

symEl {a₀ = bool}           {bool}            bool~                               {tt}{tt} _ = ttp
symEl {a₀ = bool}           {bool}            bool~                               {ff}{ff} _ = ttp
symEl {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ =
  symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) x₀₁))) (f₀₁ _ _ (symEl (proj₂ (symU a₀₁)) x₀₁))
-}
{-
coeEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} →     (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) →     A₀  → A₁
cohEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → El~ Â₀₁ x₀ (coeEl Â₀₁ x₀)
transU : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂) →
  Σ (A₀ → A₂ → Prop) (in-U~ a₀ a₂)
transEl : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂){x₀ : A₀}{x₁ : A₁}{x₂ : A₂} →
  El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → El~ (tr (A₁₂ ,Σ a₁₂)) x₁ x₂ → El~ (tr (transU a₀₁ a₁₂)) x₀ x₂


coeEl {a₀ = bool}                {bool}                 _ x = x
coeEl {a₀ = bool}                {π a a~ b b~}          w _ = ⊥pelim (withTrunc w λ ())
coeEl {a₀ = π a a~ b b~}         {bool}                 w _ = ⊥pelim (withTrunc w λ ())
coeEl {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{π {A₁} a₁ a₁~ b₁ b₁~} w (f₀ ,sp f₀~) =
  (λ x₁ → coeEl {a₀ = b₀ (coeEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁)}
                (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁)))) })
                (f₀ (coeEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))) ,sp
  λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ x₀₁) (transEl
      (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀))))))
      (proj₂ (transU (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀)) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ x₀₁) (cohEl (tr (symU a₀₁)) x₁))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁))))))
      (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀))))
           (cohEl {a₀ = b₀ (coeEl (tr (symU a₀₁)) x₀)}
                  (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀)))))
                  (f₀ (coeEl (tr (symU a₀₁)) x₀))))
      (transEl
        (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀)) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ x₀₁) (cohEl (tr (symU a₀₁)) x₁)))))
        (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁))))
        (toEl~ (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀)) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ x₀₁) (cohEl (tr (symU a₀₁)) x₁)))))
               (f₀~ _ _ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₀)) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ x₀₁) (cohEl (tr (symU a₀₁)) x₁))))))
        (cohEl {a₀ = b₀ (coeEl (tr (symU a₀₁)) x₁)}
                  (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁)))))
                  (f₀ (coeEl (tr (symU a₀₁)) x₁)))))
 }

cohEl {a₀ = bool}                {bool}                 _ tt = ttp
cohEl {a₀ = bool}                {bool}                 _ ff = ttp
cohEl {a₀ = bool}                {π a a~ b b~}          w _ = ⊥pelimp (withTrunc w λ ())
cohEl {a₀ = π a a~ b b~}         {bool}                 w _ = ⊥pelimp (withTrunc w λ ())
cohEl {a₀ = π {A₀} a₀ a₀~ b₀ b₀~} {π {A₁} a₁ a₁~ b₁ b₁~} (tr (_ ,Σ π~ a₀₁ b₀₁)) (f₀ ,sp f₀~) x₀ x₁ x₀₁ = transEl
  (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) x₀₁ (cohEl (tr (symU a₀₁)) x₁))))
  (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁))))
  (toEl~ (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) x₀₁ (cohEl (tr (symU a₀₁)) x₁))))
         (f₀~ _ _ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) x₀₁ (cohEl (tr (symU a₀₁)) x₁)))))
  (cohEl (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (cohEl (tr (symU a₀₁)) x₁))))) (f₀ _))

transU {a₀ = bool}{bool}{bool} bool~ bool~ = _ ,Σ bool~
transU {a₀ = π {A₀} a₀ a₀~ {B₀} b₀ b₀~}{π {A₁} a₁ a₁~ {B₁} b₁ b₁~}{π {A₂} a₂ a₂~ {B₂} b₂ b₂~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)(π~ {A₀₁ = A₁₂} a₁₂ {B₀₁ = B₁₂} b₁₂) = _ ,Σ
  π~ (proj₂ (transU a₀₁ a₁₂))
     {B₀₁ = λ {x₀}{x₂} x₀₂ → proj₁ (transU
       (b₀₁ (fromEl~ a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀)))
       (proj₂ (transU 
       (b₁~ (fromEl~ a₁~ (transEl
          (proj₂ (symU a₀₁))
          a₀₁
          (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
          (transEl
            (proj₂ (transU a₀₁ a₁₂))
            (proj₂ (symU a₁₂))
            (toEl~ (proj₂ (transU a₀₁ a₁₂)) x₀₂)
            (cohEl (tr (symU a₁₂)) x₂))))) (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂)))))))}
     λ {x₀}{x₂} x₀₂ → proj₂ (transU
       (b₀₁ (fromEl~ a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀)))
       (proj₂ (transU 
       (b₁~ (fromEl~ a₁~ (transEl
          (proj₂ (symU a₀₁))
          a₀₁
          (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
          (transEl
            (proj₂ (transU a₀₁ a₁₂))
            (proj₂ (symU a₁₂))
            (toEl~ (proj₂ (transU a₀₁ a₁₂)) x₀₂)
            (cohEl (tr (symU a₁₂)) x₂))))) (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂)))))))

transEl {a₀ = bool}{bool}{bool} bool~ bool~ {tt}{tt}{tt} _ _ = ttp
transEl {a₀ = bool}{bool}{bool} bool~ bool~ {ff}{ff}{ff} _ _ = ttp
transEl {a₀ = π {A₀} a₀ a₀~ {B₀} b₀ b₀~}{π {A₁} a₁ a₁~ {B₁} b₁ b₁~}{π {A₂} a₂ a₂~ {B₂} b₂ b₂~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)(π~ {A₀₁ = A₁₂} a₁₂ {B₀₁ = B₁₂} b₁₂){f₀ ,sp f₀~}{f₁ ,sp f₁~}{f₂ ,sp f₂~} f₀₁ f₁₂ x₀ x₂ x₀₂ =
  transEl
    (b₀₁ (fromEl~ a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀)))
    (proj₂ (transU
      (b₁~ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          x₀₂
          (cohEl (tr (symU a₁₂)) x₂)))))
      (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂))))))
    (f₀₁ _ _ (cohEl (tr (_ ,Σ a₀₁)) x₀))
    (transEl
      (b₁~ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          x₀₂
          (cohEl (tr (symU a₁₂)) x₂)))))
      (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂))))
      (toEl~ (b₁~ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          x₀₂
          (cohEl (tr (symU a₁₂)) x₂))))) (f₁~ _ _ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          x₀₂
          (cohEl (tr (symU a₁₂)) x₂))))))
      (f₁₂ _ _ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂))))

-- the actual definition of the universe
-}

{-
U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
U = mkTy
  (λ _ → ∣U∣)
  (λ _ → _~U_)
  refU
  {!!} -- (λ Â₀₁ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → tr (symU a₀₁) } )
  {!!} -- (λ Â₀₁ Â₁₂ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → withTrunc Â₁₂ λ { (_ ,Σ a₁₂) → tr (transU a₀₁ a₁₂) } })
  (λ _ Â → Â)
  (λ _ → refU)

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
El Â = mkTy
  (λ γ → ∣El∣ (∣ Â ∣t γ))
  (λ {γ}{γ'} γ₀₁ → El~ (proj₂sp (proj₂ (∣ Â ∣t γ))) (proj₂sp (proj₂ (∣ Â ∣t γ'))) (~t Â γ₀₁))
  (λ {γ} → refEl {∣ Â ∣t γ})
  {!!} -- (λ {_}{_}{γ₀₁} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → symEl a₀₁ })
  {!!} -- (λ {_}{_}{_}{γ₀₁}{γ₁₂} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → withTrunc (~t Â γ₁₂) λ { (_ ,Σ a₁₂) → transEl a₀₁ a₁₂ } })
  {!!} -- (λ {_}{_} γ₀₁ → coeEl (~t Â γ₀₁))
  {!!} -- (λ {_}{_} γ₀₁ → cohEl (~t Â γ₀₁))

ΠS : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
ΠS {Γ = Γ} Â B̂ = record {
  ∣_∣t = λ γ → _ ,Σ π
    (proj₂ (∣ Â ∣t γ))
    {!!} -- (in-El~ (refU (∣ Â ∣t γ)))
    (λ x → proj₂ (∣ B̂ ∣t (γ ,Σ x)))
    {λ x₀₁ → El~ {!!} {!!} (~t B̂ (refC Γ γ ,p x₀₁))}
    {!!} -- (λ x₀₁ → in-El~ (~t B̂ (refC Γ γ ,p x₀₁)))
    ;
  ~t = λ {γ₀}{γ₁} γ₀₁ → tr (_ ,Σ π~
    {!!} -- (in-El~ (~t Â γ₀₁))
    {B₀₁ = λ x₀₁ → El~ {!!} {!!} (~t B̂ (γ₀₁ ,p x₀₁))}
     λ x₀₁ → {!!} -- in-El~ (~t B̂ (γ₀₁ ,p x₀₁))
     ) }

BoolS : ∀{i}{Γ : Con i} → Tm Γ U
BoolS = record {
  ∣_∣t = λ _ → _ ,Σ bool ;
  ~t = λ _ → tr (_ ,Σ bool~) }
-}
