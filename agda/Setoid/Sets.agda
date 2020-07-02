{-# OPTIONS --without-K --prop #-}

module Setoid.Sets where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.Sets.lib
open import Setoid.CwF

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ Set in-U

∣El∣ : ∣U∣ → Set
∣El∣ (A ,Σ a) = A

_~U_ : ∣U∣ → ∣U∣ → Prop₁
(A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) = Tr (Σ (A₀ → A₁ → Prop) (λ A₀₁ → in-U~ a₀ a₁ A₀₁))

El~' : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → Σsp
  ((A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop) λ A₀₁' →
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁' (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ ↔ A₀₁ x₀ x₁
El~' {a₀ = bool}                {bool}                 =
  (λ _ x₀ x₁ → if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)) ,sp
  λ { bool~ {x₀}{x₁} → (λ x₀₁ → x₀₁) ,p (λ x₀₁ → x₀₁) }
El~' {a₀ = bool}                {π a a~ b b~}          = (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ()
El~' {a₀ = π a a~ b b~}         {bool}                 = (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ()
El~' {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{π {A₁} a₁ a₁~ b₁ b₁~} =
  (λ w f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (proj₁sp (El~' {a₀ = a₀}{a₁}) (withTrunc w λ { (_ ,Σ π~ a₀₁ _) → tr (_ ,Σ a₀₁) }) x₀ x₁)) →
    proj₁sp El~' (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ ((proj₁p (proj₂sp El~' a₀₁)) (un↑ps x₀₁))) }) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁)) ,sp
  λ { (π~ {A₀₁ = A₀₁} a₀₁ b₀₁) →
    (λ f₀₁ _ _ x₀₁ → proj₁p (proj₂sp El~' (b₀₁ (un↑ps x₀₁))) (f₀₁ _ _ (mk↑ps (proj₂p (proj₂sp El~' a₀₁) (un↑ps x₀₁))))) ,p
    (λ f₀₁ _ _ x₀₁ → proj₂p (proj₂sp El~' (b₀₁ (proj₁p (proj₂sp El~' a₀₁) (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps (proj₁p (proj₂sp El~' a₀₁) (un↑ps x₀₁))))) }

El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop
El~ = proj₁sp El~'
fromEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → A₀₁ x₀ x₁
toEl~   : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁ x₀ x₁ → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁
fromEl~ a~ = proj₁p (proj₂sp El~' a~)
toEl~   a~ = proj₂p (proj₂sp El~' a~)

in-El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ {a₀ = bool} {bool} w = bool~
in-El~ {a₀ = bool} {π a a~ b b~} w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ = π a a~ b b~} {bool} w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ = π a₀ a₀~ b₀ b₀~} {π a₁ a₁~ b₁ b₁~} w =  π~ 
  (in-El~ {a₀ = a₀}{a₁} (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ a₀₁) })))
  {B₀₁ = λ x₀₁ → El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }))}
  (λ x₀₁ → in-El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) })))

refU : (Â : ∣U∣) → Â ~U Â
refU (_ ,Σ bool) = tr (_ ,Σ bool~)
refU (_ ,Σ π a a~ b {B~} b~) = tr (_ ,Σ π~ a~ {B₀₁ = B~} b~)

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → El~ (refU Â) x x
refEl {Â = _ ,Σ bool}        tt = ttp
refEl {Â = _ ,Σ bool}        ff = ttp
refEl {Â = _ ,Σ π a a~ b b~} (f ,sp f~) _ _ x₀₁ = toEl~ (b~ (fromEl~ a~ (un↑ps x₀₁))) (f~ _ _ (mk↑ps (fromEl~ a~ (un↑ps x₀₁))))

symUEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → Σsp
  (Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)) λ a₁₀' →
  {x₀ : A₀}{x₁ : A₁} → El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr a₁₀') x₁ x₀
symUEl {a₀ = bool}           {bool}            bool~                   =
  (_ ,Σ bool~) ,sp λ { {tt}{tt} _ → ttp ; {ff}{ff} _ → ttp }
symUEl {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) = (_ ,Σ
  π~ (proj₂ (proj₁sp (symUEl a₀₁)))
     {B₀₁ = λ x₀₁ → proj₁ (proj₁sp (symUEl (b₀₁ (fromEl~ a₀₁ (proj₂sp (symUEl (proj₂ (proj₁sp (symUEl a₀₁)))) (toEl~ (proj₂ (proj₁sp (symUEl a₀₁))) x₀₁))))))}
     (λ x₀₁ →  proj₂ (proj₁sp (symUEl (b₀₁ (fromEl~ a₀₁ (proj₂sp (symUEl (proj₂ (proj₁sp (symUEl a₀₁)))) (toEl~ (proj₂ (proj₁sp (symUEl a₀₁))) x₀₁)))))))) ,sp
  λ {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
    proj₂sp (symUEl (b₀₁ (fromEl~ a₀₁ (proj₂sp (symUEl (proj₂ (proj₁sp (symUEl a₀₁)))) (un↑ps x₀₁)))))
      (f₀₁ _ _ (mk↑ps (proj₂sp (symUEl (proj₂ (proj₁sp (symUEl a₀₁)))) (un↑ps x₀₁))))

symU  : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)
symEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} →
  El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr (symU a₀₁)) x₁ x₀
symU a₀₁ = proj₁sp (symUEl a₀₁)
symEl a₀₁ = proj₂sp (symUEl a₀₁)

coEl    : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → Σsp A₁ (El~ Â₀₁ x₀)

transU  : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂) → Σ (A₀ → A₂ → Prop) (in-U~ a₀ a₂)
transEl : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂){x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → El~ (tr (A₁₂ ,Σ a₁₂)) x₁ x₂ → El~ (tr (transU a₀₁ a₁₂)) x₀ x₂

coEl {a₀ = bool}                {bool}                 _ x = x ,sp  refEl {_ ,Σ bool} x 
coEl {a₀ = bool}                {π a a~ b b~}          w _ = ⊥pelim (withTrunc w λ ())
coEl {a₀ = π a a~ b b~}         {bool}                 w _ = ⊥pelim (withTrunc w λ ())
coEl {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{π {A₁} a₁ a₁~ b₁ b₁~} w (f₀ ,sp f₀~) =
  ((λ x₁ → proj₁sp (coEl {a₀ = b₀ (proj₁sp (coEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))}
                (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁))))) })
                (f₀ (proj₁sp (coEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))))) ,sp
    λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ (un↑ps x₀₁)) (transEl
      (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀)))))))
      (proj₂ (transU (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀))) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))))
      (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀)))))
           (proj₂sp (coEl {a₀ = b₀ (proj₁sp (coEl (tr (symU a₀₁)) x₀))}
                  (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀))))))
                  (f₀ (proj₁sp (coEl (tr (symU a₀₁)) x₀))))))
      (transEl
        (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀))) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁))))))
        (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))
        (toEl~ (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀))) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁))))))
               (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₀))) (transEl a₁~ (proj₂ (symU a₀₁)) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁))))))))
        (proj₂sp (coEl {a₀ = b₀ (proj₁sp (coEl (tr (symU a₀₁)) x₁))}
                  (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁))))))
                  (f₀ (proj₁sp (coEl (tr (symU a₀₁)) x₁))))))) }) ,sp
  withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) x₀ x₁ x₀₁ → transEl
    (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (un↑ps x₀₁) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))
    (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))
    (toEl~ (b₀~ (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (un↑ps x₀₁) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))
           (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (transEl a₀₁ (proj₂ (symU a₀₁)) (un↑ps x₀₁) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))))
    (proj₂sp (coEl (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))) (f₀ _))) }

coeEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → A₁
cohEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → El~ Â₀₁ x₀ (coeEl Â₀₁ x₀)
coeEl Â₀₁ x₀ = proj₁sp (coEl Â₀₁ x₀)
cohEl Â₀₁ x₀ = proj₂sp (coEl Â₀₁ x₀)

transU = {!!}
transEl = {!!}
{-
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
          (un↑ps x₀₂)
          (cohEl (tr (symU a₁₂)) x₂)))))
      (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂))))))
    (f₀₁ _ _ (mk↑ps (cohEl (tr (_ ,Σ a₀₁)) x₀)))
    (transEl
      (b₁~ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          (un↑ps x₀₂)
          (cohEl (tr (symU a₁₂)) x₂)))))
      (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂))))
      (toEl~ (b₁~ (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          (un↑ps x₀₂)
          (cohEl (tr (symU a₁₂)) x₂))))) (f₁~ _ _ (mk↑ps (fromEl~ a₁~ (transEl
        (proj₂ (symU a₀₁))
        a₀₁
        (symEl a₀₁ (cohEl (tr (_ ,Σ a₀₁)) x₀))
        (transEl
          (proj₂ (transU a₀₁ a₁₂))
          (proj₂ (symU a₁₂))
          (un↑ps x₀₂)
          (cohEl (tr (symU a₁₂)) x₂)))))))
      (f₁₂ _ _ (mk↑ps (symEl (proj₂ (symU a₁₂)) (cohEl (tr (symU a₁₂)) x₂)))))

-- the actual definition of the universe

U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
U = mkTy
  (λ _ → ∣U∣)
  (λ _ → _~U_)
  refU
  (λ Â₀₁ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → tr (symU a₀₁) } )
  (λ Â₀₁ Â₁₂ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → withTrunc Â₁₂ λ { (_ ,Σ a₁₂) → tr (transU a₀₁ a₁₂) } })
  (λ _ Â → Â)
  (λ _ → refU)

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
El Â = mkTy
  (λ γ → ∣El∣ (∣ Â ∣t γ))
  (λ γ₀₁ → El~ (~t Â γ₀₁))
  (λ {γ} → refEl {∣ Â ∣t γ})
  (λ {_}{_}{γ₀₁} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → symEl a₀₁ })
  (λ {_}{_}{_}{γ₀₁}{γ₁₂} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → withTrunc (~t Â γ₁₂) λ { (_ ,Σ a₁₂) → transEl a₀₁ a₁₂ } })
  (λ {_}{_} γ₀₁ → coeEl (~t Â γ₀₁))
  (λ {_}{_} γ₀₁ → cohEl (~t Â γ₀₁))

ΠS : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
ΠS {Γ = Γ} Â B̂ = record {
  ∣_∣t = λ γ → _ ,Σ π
    (proj₂ (∣ Â ∣t γ))
    (in-El~ (refU (∣ Â ∣t γ)))
    (λ x → proj₂ (∣ B̂ ∣t (γ ,Σ x)))
    {λ x₀₁ → El~ (~t B̂ (refC Γ γ ,p x₀₁))}
    (λ x₀₁ → in-El~ (~t B̂ (refC Γ γ ,p x₀₁))) ;
  ~t = λ {γ₀}{γ₁} γ₀₁ → tr (_ ,Σ π~
    (in-El~ (~t Â γ₀₁))
    {B₀₁ = λ x₀₁ → El~ (~t B̂ (γ₀₁ ,p x₀₁))}
     λ x₀₁ → in-El~ (~t B̂ (γ₀₁ ,p x₀₁))) }

BoolS : ∀{i}{Γ : Con i} → Tm Γ U
BoolS = record {
  ∣_∣t = λ _ → _ ,Σ bool ;
  ~t = λ _ → tr (_ ,Σ bool~) }
-}
