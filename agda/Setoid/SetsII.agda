{-# OPTIONS --without-K --prop #-}

module Setoid.SetsII where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.SetsII.lib
open import Setoid.CwF

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ Set in-U

∣El∣ : ∣U∣ → Set
∣El∣ (A ,Σ a) = A

_~U_ : ∣U∣ → ∣U∣ → Prop₁
Â₀ ~U Â₁ = Tr (Σ (proj₁ Â₀ → proj₁ Â₁ → Prop) (λ A₀₁ → in-U~ (proj₂ Â₀) (proj₂ Â₁) A₀₁))

El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop
fromEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → A₀₁ x₀ x₁
toEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁ x₀ x₁ → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁
-- these say that El~ reconstructs the relation that is already there in "(A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)"

El~ {a₀ = bool}                {bool}                 _ x₀ x₁ = if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
El~ {a₀ = bool}                {π a a~ b b~}          w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π a a~ b b~}         {bool}                 w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{π {A₁} a₁ a₁~ b₁ b₁~} w f₀ f₁ =
  (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ _) → tr (_ ,Σ a₀₁) }) x₀ x₁)) →
  El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (un↑ps x₀₁))) }) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁)

fromEl~ {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁
fromEl~ {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ b₀₁) f₀₁ _ _ x₀₁ = fromEl~ (b₀₁ (un↑ps x₀₁)) (f₀₁ _ _ (mk↑ps (toEl~ a₀₁ (un↑ps x₀₁))))

toEl~   {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁
toEl~   {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ b₀₁) f₀₁ _ _ x₀₁ = toEl~ (b₀₁ (fromEl~ a₀₁ (un↑ps x₀₁))) (f₀₁ _ _ (mk↑ps (fromEl~ a₀₁ (un↑ps x₀₁))))

in-El~ : ∀{A₀}(a₀ : in-U A₀){A₁}(a₁ : in-U A₁)(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ bool bool w = bool~
in-El~ bool (π a a~ b b~) w = ⊥pelim (withTrunc w λ ())
in-El~ (π a a~ b b~) bool w = ⊥pelim (withTrunc w λ ())
in-El~ (π a₀ a₀~ b₀ b₀~)(π a₁ a₁~ b₁ b₁~) w = π~ 
  (in-El~ a₀ a₁ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ a₀₁) })))
  {B₀₁ = λ x₀₁ → El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }))}
  (λ x₀₁ → in-El~ _ _ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) })))

_,π~_ : 
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} → 
  (Â₀₁ : (_ ,Σ a⁰) ~U (_ ,Σ a¹))(B̂₀₁ : {x⁰ : A⁰}{x¹ : A¹}(x⁰¹ : El~ Â₀₁ x⁰ x¹) → (_ ,Σ b⁰ x⁰) ~U (_ ,Σ b¹ x¹)) →
  (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹)
(tr (_ ,Σ a⁰¹)) ,π~ w = tr (_ ,Σ (π~ a⁰¹ (λ {x₀}{x₁} x₀₁ → in-El~ _ _ (w (toEl~ a⁰¹ x₀₁)))))

projπ~₁ :
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} → 
  (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹) → (_ ,Σ a⁰) ~U (_ ,Σ a¹)
projπ~₁ (tr (_ ,Σ π~ a₀₁ b₀₁)) = tr (_ ,Σ a₀₁)

projπ~₂ :
  {A⁰ : Set}{A¹ : Set}{a⁰ : in-U A⁰}{a¹ : in-U A¹}
  {A~⁰ : A⁰ → A⁰ → Prop}{A~¹ : A¹ → A¹ → Prop}{a~⁰ : in-U~ a⁰ a⁰ A~⁰}{a~¹ : in-U~ a¹ a¹ A~¹}
  {B⁰ : A⁰ → Set}{B¹ : A¹ → Set}{b⁰ : (x : A⁰) → in-U (B⁰ x)}{b¹ : (x : A¹) → in-U (B¹ x)}
  {B~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → B⁰ x₀ → B⁰ x₁ → Prop}{B~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → B¹ x₀ → B¹ x₁ → Prop}
  {b~⁰ : {x₀ x₁ : A⁰}(x₀₁ : A~⁰ x₀ x₁) → in-U~ (b⁰ x₀) (b⁰ x₁) (B~⁰ x₀₁)}{b~¹ : {x₀ x₁ : A¹}(x₀₁ : A~¹ x₀ x₁) → in-U~ (b¹ x₀) (b¹ x₁) (B~¹ x₀₁)} → 
  (w : (_ ,Σ π a⁰ a~⁰ b⁰ b~⁰) ~U (_ ,Σ π a¹ a~¹ b¹ b~¹)) → {x⁰ : A⁰}{x¹ : A¹}(x⁰¹ : El~ (projπ~₁ w) x⁰ x¹) → (_ ,Σ b⁰ x⁰) ~U (_ ,Σ b¹ x¹)
projπ~₂ {a⁰ = a⁰}{a¹ = a¹} (tr (_ ,Σ π~ a⁰¹ b⁰¹)) = λ x⁰¹ → tr (_ ,Σ b⁰¹ (fromEl~ a⁰¹ x⁰¹))

refU : (Â : ∣U∣) → Â ~U Â
refU (_ ,Σ bool) = tr (_ ,Σ bool~)
refU (_ ,Σ π a a~ b {B~} b~) = tr (_ ,Σ π~ a~ {B₀₁ = B~} b~)

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → El~ (refU Â) x x
refEl {Â = _ ,Σ bool}        tt = ttp
refEl {Â = _ ,Σ bool}        ff = ttp
refEl {Â = _ ,Σ π a a~ b b~} (f ,sp f~) _ _ x₀₁ = toEl~ (b~ (fromEl~ a~ (un↑ps x₀₁))) (f~ _ _ (mk↑ps (fromEl~ a~ (un↑ps x₀₁))))

symU    : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → (A₁ ,Σ a₁) ~U (A₀ ,Σ a₀)
symEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)){x₀ : A₀}{x₁ : A₁} → El~ Â₀₁ x₀ x₁ → El~ (symU a₀ a₁ Â₀₁) x₁ x₀
-- symEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)){x₀ : A₀}{x₁ : A₁} → El~ (symU a₀ a₁ Â₀₁) x₁ x₀ → El~ Â₀₁ x₀ x₁

symU bool bool = λ _ → tr (_ ,Σ bool~)
symU bool (π a a~ b b~) = λ w → withTrunc w λ ()
symU (π a a~ b b~) bool = λ w → withTrunc w λ ()
symU (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) = λ w →
  withTrunc w λ { (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) →
    symU a₀ a₁ (tr (_ ,Σ a₀₁)) ,π~ λ {x₀}{x₁} x₀₁ →
      symU (b₀ x₁) (b₁ x₀)
        (tr (_ ,Σ (b₀₁ (fromEl~ a₀₁ (symEl a₁ a₀ (symU a₀ a₁ (tr (_ ,Σ a₀₁))) x₀₁)))))
       -- symU (b₀ x₁) (b₁ x₀)
       --  (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl⁻¹ a₀ a₁ (tr (_ ,Σ a₀₁)) x₀₁))))
        }

symEl bool bool = λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }
symEl bool (π a a~ b b~) = λ { (tr (_ ,Σ ())) }
symEl (π a a~ b b~) bool = λ { (tr (_ ,Σ ())) }
symEl (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) =
  λ { (tr (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)) {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
  let x₁₀ = symEl a₁ a₀ (symU _ _ (tr (_ ,Σ a₀₁))) (un↑ps x₀₁)
  -- symEl⁻¹ a₀ a₁ (tr (_ ,Σ a₀₁)) (un↑ps x₀₁)
  in symEl (b₀ x₁) (b₁ x₀) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₁₀))) (f₀₁ _ _ (mk↑ps x₁₀))  }

{-
symEl⁻¹ bool bool = λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }
symEl⁻¹ bool (π a a~ b b~) = λ { (tr (_ ,Σ ())) }
symEl⁻¹ (π a a~ b b~) bool = λ { (tr (_ ,Σ ())) }
symEl⁻¹ (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) = λ { (tr (_ ,Σ π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)){f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
  let x₁₀ = symEl a₀ a₁ (tr (_ ,Σ a₀₁)) (un↑ps x₀₁) in
  symEl⁻¹ (b₀ x₀) (b₁ x₁) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps x₁₀)) }
-}

coeEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → A₁
coeEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₁ : A₁) → A₀
cohEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → El~ Â₀₁ x₀ (coeEl _ _ Â₀₁ x₀)
cohEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₁ : A₁) → El~ Â₀₁ (coeEl⁻¹ _ _ Â₀₁ x₁) x₁
transU  : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂)) → (A₀ ,Σ a₀) ~U (A₂ ,Σ a₂)
transEl : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ Â₀₁ x₀ x₁ → El~ Â₁₂ x₁ x₂ → El~ (transU a₀ a₁ a₂ Â₀₁ Â₁₂) x₀ x₂
transEl⁻¹ : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ (symU a₀ a₁ Â₀₁) x₁ x₀ → El~ (transU a₀ a₁ a₂ Â₀₁ Â₁₂) x₀ x₂ → El~ Â₁₂ x₁ x₂

coeEl⁻¹ a₀ a₁ p x = coeEl _ _ (symU _ _ p) x
cohEl⁻¹ a₀ a₁ p x = symEl _ _ (symU _ _ p) (cohEl _ _ (symU _ _ p) x)
transEl⁻¹ a₀ a₁ a₂ p q x y = transEl a₁ a₀ a₂ (symU _ _ p) (transU _ _ _ p q) x y

coeEl bool bool = λ _ x → x
coeEl bool (π a a~ b b~) = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl (π a a~ b b~) bool = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl (π {A₀} a₀ a₀~ {B₀} b₀ b₀~) (π {A₁} a₁ a₁~ {B₁} b₁ b₁~) = λ { w (f₀ ,sp f₀~) →
  let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w
      B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w
  in
  (λ x₁ → let x₀ = -- coeEl a₁ a₀ (symU _ _ Â₀₁) x₁
                   coeEl⁻¹ a₀ a₁ Â₀₁ x₁
              x₀₁ = -- symEl _ _ (symU _ _ Â₀₁) (cohEl _ _ (symU _ _ Â₀₁) x₁)
                    cohEl⁻¹ a₀ a₁ Â₀₁ x₁
          in coeEl (b₀ x₀) (b₁ x₁) (B̂₀₁ x₀₁) (f₀ x₀)) ,sp
  (λ x₀₁ x₁₁ x-₁ →
    let x₀₀ = -- coeEl a₁ a₀ (symU _ _ Â₀₁) x₀₁
              coeEl⁻¹ a₀ a₁ Â₀₁ x₀₁
        x₀- = -- symEl _ _ (symU _ _ Â₀₁) (cohEl _ _ (symU _ _ Â₀₁) x₀₁)
              cohEl⁻¹ a₀ a₁ Â₀₁ x₀₁
    in let x₁₀ = -- coeEl a₁ a₀ (symU _ _ Â₀₁) x₁₁
                 coeEl⁻¹ a₀ a₁ Â₀₁ x₁₁
           x₁- = -- symEl _ _ (symU _ _ Â₀₁) (cohEl _ _ (symU _ _ Â₀₁) x₁₁)
                 cohEl⁻¹ a₀ a₁ Â₀₁ x₁₁
    in let x-₀ = transEl a₀ a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (transEl a₀ a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- (toEl~ a₁~ (un↑ps x-₁))) (symEl a₀ a₁ Â₀₁ x₁-) in
    let y₀₀ = f₀ x₀₀ ; y₀₁ = coeEl (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ ; y₀- = cohEl (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀₀ in
    let y₁₀ = f₀ x₁₀ ; y₁₁ = coeEl (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ ; y₁- = cohEl (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁₀ in
    let y-₀ = f₀~ x₀₀ x₁₀ (mk↑ps (fromEl~ a₀~ x-₀)) in
    fromEl~ (b₁~ (un↑ps x-₁))
            (transEl⁻¹ (b₀ x₀₀) (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-)
              (tr (_ ,Σ b₁~ (un↑ps x-₁)))
              (symEl (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀-)
              (transEl (b₀ x₀₀) (b₀ x₁₀) (b₁ x₁₁)
                (tr (_ ,Σ b₀~ (fromEl~ a₀~ x-₀)))
                (B̂₀₁ x₁-)
                (toEl~ (b₀~ (fromEl~ a₀~ x-₀)) y-₀) y₁- ))
              ) }
  {-       x-₁                 y-₁          
  A₁   x₀₁-----x₁₁         y₀₁-----y₁₁       B₁ x₀₁     B₁ x₁₁
     x₀-|       |x₁-     y₀-|       |y₁-    
  A₀   x₀₀-----x₁₀         y₀₀-----y₁₀       B₀ x₀₀     B₀ x₁₀
           x-₀                                                 -}

{-
coeEl⁻¹ bool bool = λ _ x → x
coeEl⁻¹ bool (π a a~ b b~) = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl⁻¹ (π a a~ b b~) bool = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl⁻¹ (π {A₀} a₀ a₀~ {B₀} b₀ b₀~) (π {A₁} a₁ a₁~ {B₁} b₁ b₁~) = λ { w (f₁ ,sp f₁~) → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
  (λ x₀ → let x₁ = coeEl a₀ a₁ Â₀₁ x₀ ; x₀₁ = cohEl a₀ a₁ Â₀₁ x₀ in coeEl⁻¹ (b₀ x₀) (b₁ x₁) (B̂₀₁ x₀₁) (f₁ x₁)) ,sp
  (λ x₀₀ x₁₀ x-₀ →
    let x₀₁ = coeEl a₀ a₁ Â₀₁ x₀₀ ; x₀- = cohEl a₀ a₁ Â₀₁ x₀₀ in
    let x₁₁ = coeEl a₀ a₁ Â₀₁ x₁₀ ; x₁- = cohEl a₀ a₁ Â₀₁ x₁₀ in
    let x-₁ = transEl⁻¹ a₀ a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) (transEl⁻¹ a₀ a₁ a₀ Â₀₁ (symU a₀ a₁ Â₀₁) (symEl a₀ a₁ Â₀₁ x₀-) (toEl~ a₀~ (un↑ps x-₀))) x₁- in
    let y₀₁ = f₁ x₀₁ ; y₀₀ = coeEl⁻¹ (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ ; y₀- = cohEl⁻¹ (b₀ x₀₀) (b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ in
    let y₁₁ = f₁ x₁₁ ; y₁₀ = coeEl⁻¹ (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ ; y₁- = cohEl⁻¹ (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ in
    let y-₁ = f₁~ x₀₁ x₁₁ (mk↑ps (fromEl~ a₁~ x-₁)) in
  fromEl~ (b₀~ (un↑ps x-₀)) (transEl (b₀ x₀₀) (b₁ x₁₁) (b₀ x₁₀) (B̂₀₁ (transEl a₀ a₁ a₁ Â₀₁ (refU (_ ,Σ a₁)) x₀- x-₁)) (symU _ _ (B̂₀₁ x₁-)) (transEl (b₀ x₀₀) (b₁ x₀₁) (b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ b₁~ (fromEl~ a₁~ x-₁))) y₀- (toEl~ (b₁~ (fromEl~ a₁~ x-₁)) y-₁) ) (symEl (b₀ x₁₀) (b₁ x₁₁) (B̂₀₁ x₁-) y₁-))) }
-}

cohEl bool bool = λ _ → λ { ff → ttp ; tt → ttp }
cohEl bool (π a a~ b b~) = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl (π a a~ b b~) bool = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl (π {A₀} a₀ a₀~ {B₀} b₀ b₀~) (π {A₁} a₁ a₁~ {B₁} b₁ b₁~) = λ { w (f₀ ,sp f₀~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
  let x₂ = coeEl⁻¹ a₀ a₁ Â₀₁ x₁ ; x₂₁ = cohEl⁻¹ a₀ a₁ Â₀₁ x₁ ; x₀₂ = transEl a₀ a₁ a₀ Â₀₁ (symU _ _ Â₀₁) (un↑ps x₀₁) (symEl _ _ Â₀₁ x₂₁) in
  transEl (b₀ x₀) (b₀ x₂) (b₁ x₁) (tr (_ ,Σ b₀~ (fromEl~ a₀~ x₀₂))) (B̂₀₁ x₂₁) (toEl~ (b₀~ (fromEl~ a₀~ x₀₂)) (f₀~ _ _ (mk↑ps (fromEl~ a₀~ x₀₂)))) (cohEl (b₀ x₂) (b₁ x₁) (B̂₀₁ x₂₁) (f₀ x₂)) }

{-
cohEl⁻¹ bool bool = λ _ → λ { ff → ttp ; tt → ttp }
cohEl⁻¹ bool (π a a~ b b~) = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl⁻¹ (π a a~ b b~) bool = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl⁻¹ (π {A₀} a₀ a₀~ {B₀} b₀ b₀~) (π {A₁} a₁ a₁~ {B₁} b₁ b₁~) = λ { w (f₁ ,sp f₁~) x₀ x₁ x₀₁ → let Â₀₁ = projπ~₁ {b~⁰ = b₀~}{b~¹ = b₁~} w ; B̂₀₁ = projπ~₂ {b~⁰ = b₀~}{b~¹ = b₁~} w in
  let x₂ = coeEl a₀ a₁ Â₀₁ x₀ ; x₀₂ = cohEl a₀ a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹ a₀ a₁ a₁ Â₀₁ (tr (_ ,Σ a₁~)) (symEl a₀ a₁ Â₀₁ (un↑ps x₀₁)) x₀₂ ; x₂₁ = fromEl~ a₁~ (symEl a₁ a₁ (tr (_ ,Σ a₁~)) x₁₂) in
  transEl (b₀ x₀) (b₁ x₂) (b₁ x₁) (B̂₀₁ x₀₂) (tr (_ ,Σ b₁~ x₂₁)) (cohEl⁻¹ (b₀ x₀) (b₁ x₂) (B̂₀₁ x₀₂) (f₁ x₂)) (toEl~ (b₁~ x₂₁) (f₁~ _ _ (mk↑ps x₂₁))) }
-}

transU bool bool bool = λ _ _ → tr (_ ,Σ bool~)
transU bool bool (π a a~ b b~) = λ { w (tr ()) }
transU bool (π a a~ b b~) _ = λ { (tr ()) }
transU (π a₀ a~ b b~) bool _ = λ { (tr ()) }
transU (π _ _ _ _) (π a a~ b b~) bool = λ { w (tr ()) }
transU (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) (π a₂ a~₂ b₂ b~₂) = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
  transU a₀ a₁ a₂ Â₀₁ Â₁₂ ,π~
  λ {x₀}{x₂} x₀₂ → let x₁ = coeEl a₀ a₁ Â₀₁ x₀ ; x₀₁ = cohEl a₀ a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹ a₀ a₁ a₂ Â₀₁ Â₁₂ (symEl a₀ a₁ Â₀₁ x₀₁) x₀₂ in
    transU (b₀ x₀) (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂)

transEl bool bool bool = λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }
transEl bool bool (π a a~ b b~) = λ { w (tr ()) }
transEl bool (π a a~ b b~) _ = λ { (tr ()) }
transEl (π a₀ a~ b b~) bool _ = λ { (tr ()) }
transEl (π _ _ _ _) (π a a~ b b~) bool = λ { w (tr ()) }
transEl (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) (π a₂ a~₂ b₂ b~₂) = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
  λ f₀₁ f₁₂ x₀ x₂ x₀₂ → let x₁ = coeEl a₀ a₁ Â₀₁ x₀ ; x₀₁ = cohEl a₀ a₁ Â₀₁ x₀ ; x₁₂ = transEl⁻¹ a₀ a₁ a₂ Â₀₁ Â₁₂ (symEl a₀ a₁ Â₀₁ x₀₁) (un↑ps x₀₂) in
  transEl (b₀ x₀) (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂) (f₀₁ x₀ x₁ (mk↑ps x₀₁)) (f₁₂ x₁ x₂ (mk↑ps x₁₂))

{-
transEl⁻¹ bool bool bool = λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }
transEl⁻¹ bool bool (π a a~ b b~) = λ { w (tr ()) }
transEl⁻¹ bool (π a a~ b b~) _ = λ { (tr ()) }
transEl⁻¹ (π a₀ a~ b b~) bool _ = λ { (tr ()) }
transEl⁻¹ (π _ _ _ _) (π a a~ b b~) bool = λ { w (tr ()) }
transEl⁻¹ (π a₀ a~₀ b₀ b~₀) (π a₁ a~₁ b₁ b~₁) (π a₂ a~₂ b₂ b~₂) = λ w₀₁ w₁₂ → let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
  λ f₁₀ f₀₂ x₁ x₂ x₁₂ → let x₀ = coeEl⁻¹ a₀ a₁ Â₀₁ x₁ ; x₀₁ = cohEl⁻¹ a₀ a₁ Â₀₁ x₁ ; x₁₀ = symEl a₀ a₁ Â₀₁ x₀₁ ; x₀₂ = transEl a₀ a₁ a₂ Â₀₁ Â₁₂ x₀₁ (un↑ps x₁₂) in
  transEl⁻¹ (b₀ x₀) (b₁ x₁) (b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ (un↑ps x₁₂)) (f₁₀ x₁ x₀ (mk↑ps x₁₀)) (f₀₂ x₀ x₂ (mk↑ps x₀₂)) 
-}

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

