{-# OPTIONS --without-K --prop #-}

module Setoid.Sets3 where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.Sets3.lib-abbrev
open import Setoid.Sets3.mini-univ
open import Setoid.CwF as CwF

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ U in-U

∣El∣ : ∣U∣ → Set
∣El∣ (A ,Σ a) = El A

_~U_ : ∣U∣ → ∣U∣ → Prop₁
Â₀ ~U Â₁ = Tr (Σ _ (λ A₀₁ → in-U~ (proj₂ Â₀) (proj₂ Â₁) A₀₁))

El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → El A₀ → El A₁ → P
fromEl~ : ∀{A₀ A₁ A₀₁}{a₀ : in-U A₀}{a₁ : in-U A₁} (a₀₁ : in-U~ a₀ a₁ A₀₁) → ∀{x₀ x₁} → ElP (El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁) → ElP (A₀₁ x₀ x₁)
toEl~ : ∀{A₀ A₁ A₀₁}{a₀ : in-U A₀}{a₁ : in-U A₁} (a₀₁ : in-U~ a₀ a₁ A₀₁) → ∀{x₀ x₁} → ElP (A₀₁ x₀ x₁) → ElP (El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁)

El~ {a₀ = bool} {bool}  _ x₀ x₁ = x₀ ≟𝟚-P x₁
El~ {a₀ = bool} {π _ _} w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π _ _} {bool} w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π a₀ b₀} {π a₁ b₁} w (f₀ ,sp _) (f₁ ,sp _) =
  fun-≡-P ∣ a₀ ∣ ∣ a₁ ∣ (El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ (pf a₀₁))})) (∣ b₀ ∣) (∣ b₁ ∣)
    (λ x₀₁ → El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ (pf b₀₁ ((fromEl~ (pf a₀₁) x₀₁))))})) f₀ f₁

fromEl~ {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁ -- x₀₁
fromEl~ {a₀ = π a₀ b₀}{π a₁ b₁}(π~ a₀₁ b₀₁) f₀₁ _ _ x₀₁ = fromEl~ (pf b₀₁ (un↑ps x₀₁)) (f₀₁ _ _ (mk↑ps (toEl~ (pf a₀₁) (un↑ps x₀₁))))

toEl~   {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁
toEl~   {a₀ = π a₀ b₀}{π a₁ b₁}(π~ a₀₁ b₀₁) f₀₁ _ _ x₀₁ = toEl~ (pf b₀₁ (fromEl~ (pf a₀₁) (un↑ps x₀₁))) (f₀₁ _ _ (mk↑ps (fromEl~ (pf a₀₁) (un↑ps x₀₁))))

in-El~ : ∀{A₀}(a₀ : in-U A₀){A₁}(a₁ : in-U A₁)(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ bool bool w = bool~ -- bool~
in-El~ bool (π a b) w = ⊥pelim (withTrunc w λ ())
in-El~ (π a b) bool w = ⊥pelim (withTrunc w λ ())
in-El~ (π a₀ b₀ )(π a₁ b₁) w =
  π~ (rel (in-El~ (pf a₀) (pf a₁) (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ pf a₀₁)})))
     (ixrel (λ x₀₁ → in-El~ _ _ (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ pf b₀₁ (fromEl~ (pf a₀₁) x₀₁))})))

-- ref-U~ : ∀{A} (a : in-U A) → Σ _ (in-U~ a a)
-- ref-U~ bool = _ ,Σ bool~
-- ref-U~ (π a b) = _ ,Σ π~ (rel (pf~ a)) (ixrel (pf~ b))

refU : (Â : ∣U∣) → Â ~U Â
-- refU a = tr (ref-U~ (proj₂ a))
refU (_ ,Σ bool) = tr (_ ,Σ bool~)
refU (_ ,Σ π a b ) = tr (_ ,Σ π~ (rel (pf~ a)) (ixrel (pf~ b)))

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → ElP (El~ (refU Â) x x)
refEl {Â = _ ,Σ bool}        tt = ttp
refEl {Â = _ ,Σ bool}        ff = ttp
refEl {Â = _ ,Σ π a b } (f ,sp f~) _ _ x₀₁ =
  toEl~ (pf~ b (fromEl~ (pf~ a) (un↑ps x₀₁))) (f~ _ _ (mk↑ps (fromEl~ (pf~ a) (un↑ps x₀₁))))

_,π~_ : 
  ∀ {a₀ a₁ b₀ b₁}
  → (a~ : (_ ,Σ pf a₀) ~U (_ ,Σ pf a₁))
  → (∀{x₀ x₁} → (x₀₁ : ElP (El~ a~ x₀ x₁)) → (_ ,Σ pf b₀ x₀) ~U (_ ,Σ pf b₁ x₁))
  → (_ ,Σ π a₀ b₀) ~U (_ ,Σ π a₁ b₁)
tr (_ ,Σ a~) ,π~ b~ = tr (_ ,Σ π~ (rel a~) (ixrel (λ x₀₁ → in-El~ _ _ (b~ (toEl~ a~ x₀₁)))))

projπ~₁ : ∀{a₀ a₁ b₀ b₁} → (_ ,Σ π a₀ b₀) ~U (_ ,Σ π a₁ b₁) → (_ ,Σ pf a₀) ~U (_ ,Σ pf a₁)
projπ~₁ (tr (_ ,Σ π~ a₀₁ b₀₁)) = tr (_ ,Σ pf a₀₁)

projπ~₂ : ∀{a₀ a₁ b₀ b₁} (p : (_ ,Σ π a₀ b₀) ~U (_ ,Σ π a₁ b₁))
        → (∀{x₀ x₁} (x₀₁ : ElP (El~ (projπ~₁ p) x₀ x₁)) → (_ ,Σ pf b₀ x₀) ~U (_ ,Σ pf b₁ x₁))
projπ~₂ (tr (_ ,Σ π~ a₀₁ b₀₁)) = λ x₀₁ → tr (_ ,Σ (pf b₀₁ (fromEl~ (pf a₀₁) x₀₁)))

symU    : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → (A₁ ,Σ a₁) ~U (A₀ ,Σ a₀)
symEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → ∀{x₀ x₁} → ElP (El~ Â₀₁ x₀ x₁) → ElP (El~ (symU a₀ a₁ Â₀₁) x₁ x₀)
symEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → ∀{x₀ x₁} → ElP (El~ (symU a₀ a₁ Â₀₁) x₁ x₀) → ElP (El~ Â₀₁ x₀ x₁)


symU bool bool x = tr (_ ,Σ bool~)
symU bool (π A B) w = withTrunc w λ ()
symU (π _ _) bool w = withTrunc w λ ()
symU (π a₀ b₀) (π a₁ b₁) w = withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) →
      symU (pf a₀) (pf a₁) (tr (_ ,Σ (pf a₀₁)))
  ,π~ λ {x₀} {x₁} x₀₁ → symU (pf b₀ x₁) (pf b₁ x₀) (tr (_ ,Σ (pf b₀₁ (fromEl~ (pf a₀₁) (symEl⁻¹ (pf a₀) (pf a₁) (tr (_ ,Σ pf a₀₁)) x₀₁))))) }

symEl bool bool = λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }
symEl bool (π _ _) = λ { (tr (_ ,Σ ())) }
symEl (π _ _) bool = λ { (tr (_ ,Σ ())) }
symEl (π a₀ b₀) (π a₁ b₁) (tr (_ ,Σ π~ a₀₁ b₀₁)) f~ x₀ x₁ x₀₁ =
  let x₁₀ = symEl⁻¹ (pf a₀) (pf a₁) (tr (_ ,Σ pf a₀₁)) (un↑ps x₀₁)
  in symEl (pf b₀ x₁) (pf b₁ x₀) (tr (_ ,Σ pf b₀₁ (fromEl~ (pf a₀₁) x₁₀))) (f~ _ _ (mk↑ps x₁₀))

symEl⁻¹ bool bool = λ { _ {tt}{tt} _ → ttp ; _ {ff}{ff} _ → ttp }
symEl⁻¹ bool (π _ _) = λ { (tr (_ ,Σ ())) }
symEl⁻¹ (π _ _) bool = λ { (tr (_ ,Σ ())) }
symEl⁻¹ (π a₀ b₀) (π a₁ b₁) = λ { (tr (_ ,Σ π~ a₀₁ b₀₁)){f₀}{f₁} f₀₁ x₀ x₁ x₀₁ →
  let x₁₀ = symEl (pf a₀) (pf a₁) (tr (_ ,Σ pf a₀₁)) (un↑ps x₀₁) in
  symEl⁻¹ (pf b₀ x₀) (pf b₁ x₁) (tr (_ ,Σ pf b₀₁ (fromEl~ (pf a₀₁) (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps x₁₀)) }

coeEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → El A₀ → El A₁
coeEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → El A₁ → El A₀
cohEl   : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : El A₀) → ElP (El~ Â₀₁ x₀ (coeEl _ _ Â₀₁ x₀))
cohEl⁻¹ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₁ : El A₁) → ElP (El~ Â₀₁ (coeEl⁻¹ _ _ Â₀₁ x₁) x₁)
transU  : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂)) → (A₀ ,Σ a₀) ~U (A₂ ,Σ a₂)
transEl : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  → ∀{x₀ x₁ x₂} → ElP (El~ Â₀₁ x₀ x₁) → ElP (El~ Â₁₂ x₁ x₂) → ElP (El~ (transU a₀ a₁ a₂ Â₀₁ Â₁₂) x₀ x₂)
transEl⁻¹ : ∀{A₀ A₁ A₂}(a₀ : in-U A₀)(a₁ : in-U A₁)(a₂ : in-U A₂)(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(Â₁₂ : (A₁ ,Σ a₁) ~U (A₂ ,Σ a₂))
  → ∀{x₀ x₁ x₂} → ElP (El~ (symU a₀ a₁ Â₀₁) x₁ x₀) → ElP (El~ (transU a₀ a₁ a₂ Â₀₁ Â₁₂) x₀ x₂) → ElP (El~ Â₁₂ x₁ x₂)

coeEl bool bool = λ _ x → x
coeEl bool (π _ _) = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl (π _ _) bool = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl (π a₀ b₀) (π a₁ b₁) w (f₀ ,sp f₀~) =
  (λ x₁ → let x₀ = coeEl⁻¹ (pf a₀) (pf a₁) a~ x₁ ; x₀₁ = cohEl⁻¹ (pf a₀) (pf a₁) a~ x₁
          in coeEl (pf b₀ x₀) (pf b₁ x₁) (b~ x₀₁) (f₀ x₀)) ,sp
  λ x₀₁ x₁₁ x-₁ →
    let x₀₀ = coeEl⁻¹ (pf a₀) (pf a₁) a~ x₀₁ ; x₀- = cohEl⁻¹ (pf a₀) (pf a₁) a~ x₀₁ 
        x₁₀ = coeEl⁻¹ (pf a₀) (pf a₁) a~ x₁₁ ; x₁- = cohEl⁻¹ (pf a₀) (pf a₁) a~ x₁₁
        x-₀ = transEl (pf a₀) (pf a₁) (pf a₀) a~ (symU (pf a₀) (pf a₁) a~) (transEl (pf a₀) (pf a₁) (pf a₁) a~ (refU (_ ,Σ (pf a₁))) x₀- (toEl~ (pf~ a₁) (un↑ps x-₁))) (symEl (pf a₀) (pf a₁) a~ x₁-)
        y₀₀ = f₀ x₀₀ ; y₀₁ = coeEl (pf b₀ x₀₀) (pf b₁ x₀₁) (b~ x₀-) y₀₀ ; y₀- = cohEl (pf b₀ x₀₀) (pf b₁ x₀₁) (b~ x₀-) y₀₀
        y₁₀ = f₀ x₁₀ ; y₁₁ = coeEl (pf b₀ x₁₀) (pf b₁ x₁₁) (b~ x₁-) y₁₀ ; y₁- = cohEl (pf b₀ x₁₀) (pf b₁ x₁₁) (b~ x₁-) y₁₀
        y-₀ = f₀~ x₀₀ x₁₀ (mk↑ps (fromEl~ (pf~ a₀) x-₀)) in
     fromEl~ (pf~ b₁ (un↑ps x-₁)) (transEl⁻¹ (pf b₀ x₀₀) (pf b₁ x₀₁) (pf b₁ x₁₁) (b~ x₀-) (tr (_ ,Σ pf~ b₁ (un↑ps x-₁))) (symEl (pf b₀ x₀₀) (pf b₁ x₀₁) (b~ x₀-) y₀-) (transEl (pf b₀ x₀₀) (pf b₀ x₁₀) (pf b₁ x₁₁) (tr (_ ,Σ pf~ b₀ (fromEl~ (pf~ a₀) x-₀))) (b~ x₁-) (toEl~ (pf~ b₀ (fromEl~ (pf~ a₀) x-₀)) y-₀) y₁- ))
  where
    a~ = projπ~₁ w
    b~ = projπ~₂ w

coeEl⁻¹ bool bool = λ _ x → x
coeEl⁻¹ bool (π _ _) = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl⁻¹ (π _ _) bool = λ w _ → ⊥pelim (withTrunc w λ ())
coeEl⁻¹ (π a₀ b₀) (π a₁ b₁) w (f₁ ,sp f₁~) =
  (λ x₀ → let x₁ = coeEl (pf a₀) (pf a₁) Â₀₁ x₀ ; x₀₁ = cohEl (pf a₀) (pf a₁) Â₀₁ x₀ in coeEl⁻¹ (pf b₀ x₀) (pf b₁ x₁) (B̂₀₁ x₀₁) (f₁ x₁)) ,sp
  (λ x₀₀ x₁₀ x-₀ →
    let x₀₁ = coeEl (pf a₀) (pf a₁) Â₀₁ x₀₀ ; x₀- = cohEl (pf a₀) (pf a₁) Â₀₁ x₀₀ in
    let x₁₁ = coeEl (pf a₀) (pf a₁) Â₀₁ x₁₀ ; x₁- = cohEl (pf a₀) (pf a₁) Â₀₁ x₁₀ in
    let x-₁ = transEl⁻¹ (pf a₀) (pf a₁) (pf a₁) Â₀₁ (refU (_ ,Σ (pf a₁))) (transEl⁻¹ (pf a₀) (pf a₁) (pf a₀) Â₀₁ (symU (pf a₀) (pf a₁) Â₀₁) (symEl (pf a₀) (pf a₁) Â₀₁ x₀-) (toEl~ (pf~ a₀) (un↑ps x-₀))) x₁- in
    let y₀₁ = f₁ x₀₁ ; y₀₀ = coeEl⁻¹ (pf b₀ x₀₀) (pf b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ ; y₀- = cohEl⁻¹ (pf b₀ x₀₀) (pf b₁ x₀₁) (B̂₀₁ x₀-) y₀₁ in
    let y₁₁ = f₁ x₁₁ ; y₁₀ = coeEl⁻¹ (pf b₀ x₁₀) (pf b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ ; y₁- = cohEl⁻¹ (pf b₀ x₁₀) (pf b₁ x₁₁) (B̂₀₁ x₁-) y₁₁ in
    let y-₁ = f₁~ x₀₁ x₁₁ (mk↑ps (fromEl~ (pf~ a₁) x-₁)) in
    fromEl~ (pf~ b₀ (un↑ps x-₀)) (transEl (pf b₀ x₀₀) (pf b₁ x₁₁) (pf b₀ x₁₀) (B̂₀₁ (transEl (pf a₀) (pf a₁) (pf a₁) Â₀₁ (refU (_ ,Σ (pf a₁))) x₀- x-₁)) (symU _ _ (B̂₀₁ x₁-)) (transEl (pf b₀ x₀₀) (pf b₁ x₀₁) (pf b₁ x₁₁) (B̂₀₁ x₀-) (tr (_ ,Σ pf~ b₁ (fromEl~ (pf~ a₁) x-₁))) y₀- (toEl~ (pf~ b₁ (fromEl~ (pf~ a₁) x-₁)) y-₁) ) (symEl (pf b₀ x₁₀) (pf b₁ x₁₁) (B̂₀₁ x₁-) y₁-)))
  where
    Â₀₁ = projπ~₁ w ; B̂₀₁ = projπ~₂ w

cohEl bool bool = λ _ → λ { ff → ttp ; tt → ttp }
cohEl bool (π _ _) = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl (π _ _) bool = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl (π a₀ b₀) (π a₁ b₁) w (f₀ ,sp f₀~) x₀ x₁ x₀₁ =
  let Â₀₁ = projπ~₁ w
      B̂₀₁ = projπ~₂ w
      x₂ = coeEl⁻¹ (pf a₀) (pf a₁) Â₀₁ x₁
      x₂₁ = cohEl⁻¹ (pf a₀) (pf a₁) Â₀₁ x₁
      x₀₂ = transEl (pf a₀) (pf a₁) (pf a₀) Â₀₁ (symU _ _ Â₀₁) (un↑ps x₀₁) (symEl _ _ Â₀₁ x₂₁)
  in transEl (pf b₀ x₀) (pf b₀ x₂) (pf b₁ x₁) (tr (_ ,Σ pf~ b₀ (fromEl~ (pf~ a₀) x₀₂))) (B̂₀₁ x₂₁)
       (toEl~ (pf~ b₀ (fromEl~ (pf~ a₀) x₀₂)) (f₀~ _ _ (mk↑ps (fromEl~ (pf~ a₀) x₀₂)))) (cohEl (pf b₀ x₂) (pf b₁ x₁) (B̂₀₁ x₂₁) (f₀ x₂))

cohEl⁻¹ bool bool = λ _ → λ { ff → ttp ; tt → ttp }
cohEl⁻¹ bool (π _ _) = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl⁻¹ (π _ _) bool = λ w _ → ⊥pelimp (withTrunc w λ ())
cohEl⁻¹ (π a₀ b₀) (π a₁ b₁) w (f₁ ,sp f₁~) x₀ x₁ x₀₁ =
  let Â₀₁ = projπ~₁ w ; B̂₀₁ = projπ~₂ w in
  let x₂ = coeEl (pf a₀) (pf a₁) Â₀₁ x₀ ; x₀₂ = cohEl (pf a₀) (pf a₁) Â₀₁ x₀ ; x₁₂ = transEl⁻¹ (pf a₀) (pf a₁) (pf a₁) Â₀₁ (tr (_ ,Σ pf~ a₁)) (symEl (pf a₀) (pf a₁) Â₀₁ (un↑ps x₀₁)) x₀₂ ; x₂₁ = fromEl~ (pf~ a₁) (symEl (pf a₁) (pf a₁) (tr (_ ,Σ pf~ a₁)) x₁₂) in
  transEl (pf b₀ x₀) (pf b₁ x₂) (pf b₁ x₁) (B̂₀₁ x₀₂) (tr (_ ,Σ pf~ b₁ x₂₁)) (cohEl⁻¹ (pf b₀ x₀) (pf b₁ x₂) (B̂₀₁ x₀₂) (f₁ x₂)) (toEl~ (pf~ b₁ x₂₁) (f₁~ _ _ (mk↑ps x₂₁)))

transU bool bool bool = λ _ _ → tr (_ ,Σ bool~)
transU bool bool (π _ _) = λ { w (tr ()) }
transU bool (π _ _) _ = λ { (tr ()) }
transU (π _ _) bool _ = λ { (tr ()) }
transU (π _ _) (π _ _) bool = λ { w (tr ()) }
transU (π a₀ b₀) (π a₁ b₁) (π a₂ b₂) w₀₁ w₁₂ =
  let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂
  in transU (pf a₀) (pf a₁) (pf a₂) Â₀₁ Â₁₂ ,π~
    λ {x₀}{x₂} x₀₂ → let x₁ = coeEl (pf a₀) (pf a₁) Â₀₁ x₀ ; x₀₁ = cohEl (pf a₀) (pf a₁) Â₀₁ x₀ ; x₁₂ = transEl⁻¹ (pf a₀) (pf a₁) (pf a₂) Â₀₁ Â₁₂ (symEl (pf a₀) (pf a₁) Â₀₁ x₀₁) x₀₂ in
      transU (pf b₀ x₀) (pf b₁ x₁) (pf b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂)

transEl bool bool bool = λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }
transEl bool bool (π _ _) = λ { w (tr ()) }
transEl bool (π _ _) _ = λ { (tr ()) }
transEl (π _ _) bool _ = λ { (tr ()) }
transEl (π _ _) (π _ _) bool = λ { w (tr ()) }
transEl (π a₀ b₀) (π a₁ b₁) (π a₂ b₂) w₀₁ w₁₂ =
  let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
  λ f₀₁ f₁₂ x₀ x₂ x₀₂ →
    let x₁ = coeEl (pf a₀) (pf a₁) Â₀₁ x₀
        x₀₁ = cohEl (pf a₀) (pf a₁) Â₀₁ x₀
        x₁₂ = transEl⁻¹ (pf a₀) (pf a₁) (pf a₂) Â₀₁ Â₁₂ (symEl (pf a₀) (pf a₁) Â₀₁ x₀₁) (un↑ps x₀₂)
        in transEl (pf b₀ x₀) (pf b₁ x₁) (pf b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ x₁₂) (f₀₁ x₀ x₁ (mk↑ps x₀₁)) (f₁₂ x₁ x₂ (mk↑ps x₁₂))

transEl⁻¹ bool bool bool = λ { _ _ {ff}{ff}{ff} _ _ → ttp ; _ _ {tt}{tt}{tt} _ _ → ttp }
transEl⁻¹ bool bool (π _ _) = λ { w (tr ()) }
transEl⁻¹ bool (π _ _) _ = λ { (tr ()) }
transEl⁻¹ (π _ _) bool _ = λ { (tr ()) }
transEl⁻¹ (π _ _) (π _ _) bool = λ { w (tr ()) }
transEl⁻¹ (π a₀ b₀) (π a₁ b₁) (π a₂ b₂) w₀₁ w₁₂ =
  let Â₀₁ = projπ~₁ w₀₁ ; Â₁₂ = projπ~₁ w₁₂ ; B̂₀₁ = projπ~₂ w₀₁ ; B̂₁₂ = projπ~₂ w₁₂ in
  λ f₁₀ f₀₂ x₁ x₂ x₁₂ → let x₀ = coeEl⁻¹ (pf a₀) (pf a₁) Â₀₁ x₁ ; x₀₁ = cohEl⁻¹ (pf a₀) (pf a₁) Â₀₁ x₁ ; x₁₀ = symEl (pf a₀) (pf a₁) Â₀₁ x₀₁ ; x₀₂ = transEl (pf a₀) (pf a₁) (pf a₂) Â₀₁ Â₁₂ x₀₁ (un↑ps x₁₂) in
  transEl⁻¹ (pf b₀ x₀) (pf b₁ x₁) (pf b₂ x₂) (B̂₀₁ x₀₁) (B̂₁₂ (un↑ps x₁₂)) (f₁₀ x₁ x₀ (mk↑ps x₁₀)) (f₀₂ x₀ x₂ (mk↑ps x₀₂)) 

--------------------------------------------------------------------------------

Univ : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
Univ = mkTy
  (λ _ → ∣U∣)
  (λ _ → _~U_)
  refU
  (symU _ _)
  (transU _ _ _ )
  (λ _ Â → Â)
  (λ _ → refU)

UnivEl : ∀{i}{Γ : Con i} → Tm Γ Univ → Ty Γ lzero
UnivEl Â = mkTy
  (λ γ → ∣El∣ (∣ Â ∣t γ))
  (λ γ₀₁ x₀ x₁ → ElP (El~ (~t Â γ₀₁) x₀ x₁))
  (λ {γ} → refEl {∣ Â ∣t γ})
  (λ {_}{_}{γ₀₁} → symEl _ _ (~t Â γ₀₁))
  (λ {_}{_}{_}{γ₀₁}{γ₁₂} → transEl _ _ _ (~t Â γ₀₁) (~t Â γ₁₂))
  (λ {_}{_} γ₀₁ → coeEl _ _ (~t Â γ₀₁))
  (λ {_}{_} γ₀₁ → cohEl _ _ (~t Â γ₀₁))

ΠS : ∀{i Γ}(Â : Tm Γ Univ)(B̂ : Tm (Γ ▷ UnivEl {i} Â) Univ) → Tm Γ Univ
ΠS {Γ = Γ} Â B̂ = record {
  ∣_∣t = λ γ → _ ,Σ
    π (std (proj₂ (∣ Â ∣t γ)) (in-El~ _ _ (refU (∣ Â ∣t γ))))
      (ixstd (λ x → proj₂ (∣ B̂ ∣t (γ ,Σ x))) λ x₀₁ → in-El~ _ _ (~t B̂ (refC Γ γ ,p x₀₁)))
    ;
  ~t = λ {γ₀}{γ₁} γ₀₁ → tr (_ ,Σ π~ (rel (in-El~ _ _ (~t Â γ₀₁))) (ixrel (λ x₀₁ → in-El~ _ _ (~t B̂ (γ₀₁ ,p x₀₁))))
     ) }

BoolS : ∀{i}{Γ : Con i} → Tm Γ Univ
BoolS = record {
  ∣_∣t = λ _ → _ ,Σ bool ;
  ~t = λ _ → tr (_ ,Σ bool~) }
