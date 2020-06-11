{-# OPTIONS --without-K --prop #-}

module SetoidHom.Sets where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF

withTrunc : ∀{i j}{A : Set i}{P : Prop j} → Tr A → (A → P) → P
withTrunc w f = untr f w

∣U∣ : Set₁
∣U∣ = Σ Set in-U

∣El∣ : ∣U∣ → Set
∣El∣ (A ,Σ a) = A

_~U_ : ∣U∣ → ∣U∣ → Prop₁
(A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) =  Tr (Σ (A₀ → A₁ → Prop) (λ A₀₁ → in-U~ a₀ a₁ A₀₁))

El~     : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop

fromEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → A₀₁ x₀ x₁
toEl~   : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁ x₀ x₁ → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁
-- these say that El~ reconstructs the relation that is already there in "(A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)"

El~ {a₀ = bool}                {bool}                 _ x₀ x₁ = if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)
El~ {a₀ = bool}                {π a a~ b b~}          w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π a a~ b b~}         {bool}                 w _  _  = ⊥pelim (withTrunc w λ ())
El~ {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{π {A₁} a₁ a₁~ b₁ b₁~} w f₀ f₁ =
  (x₀ : A₀)(x₁ : A₁)(x₀₁ : El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ _) → tr (_ ,Σ a₀₁) }) x₀ x₁) →
  El~ (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁)

fromEl~ {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁
fromEl~ {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ b₀₁) f₀₁ _ _ x₀₁ = fromEl~ (b₀₁ x₀₁) (f₀₁ _ _ (toEl~ a₀₁ x₀₁))

toEl~   {a₀ = bool}           {bool}           bool~                    x₀₁         = x₀₁
toEl~   {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ b₀₁) f₀₁ _ _ x₀₁ = toEl~ (b₀₁ (fromEl~ a₀₁ x₀₁)) (f₀₁ _ _ (fromEl~ a₀₁ x₀₁))

in-El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ {a₀ = bool} {bool} w = bool~
in-El~ {a₀ = bool} {π a a~ b b~} w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ = π a a~ b b~} {bool} w = ⊥pelim (withTrunc w λ ())
in-El~ {a₀ = π a₀ a₀~ b₀ b₀~} {π a₁ a₁~ b₁ b₁~} w = π~ 
  (in-El~ {a₀ = a₀}{a₁} (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ a₀₁) })))
  {B₀₁ = λ x₀₁ → El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }))}
  (λ x₀₁ → in-El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) })))

refU : (Â : ∣U∣) → Â ~U Â
refU (_ ,Σ bool) = tr (_ ,Σ bool~)
refU (_ ,Σ π a a~ b {B~} b~) = tr (_ ,Σ π~ a~ {B₀₁ = B~} b~)

refEl : {Â : ∣U∣}(x : ∣El∣ Â) → El~ (refU Â) x x
refEl {Â = _ ,Σ bool}        tt = ttp
refEl {Â = _ ,Σ bool}        ff = ttp
refEl {Â = _ ,Σ π a a~ b b~} (f ,sp f~) _ _ x₀₁ = toEl~ (b~ (fromEl~ a~ x₀₁)) (f~ _ _ (fromEl~ a~ x₀₁))

symU  : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)
symEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} →
  El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr (symU a₀₁)) x₁ x₀

symU {a₀ = bool}           {bool}            bool~                   = _ ,Σ bool~
symU {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) = _ ,Σ
  π~ (proj₂ (symU a₀₁))
     {B₀₁ = λ x₀₁ → proj₁ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (toEl~ (proj₂ (symU a₀₁)) x₀₁)))))}
     (λ x₀₁ →  proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (toEl~ (proj₂ (symU a₀₁)) x₀₁))))))

symEl {a₀ = bool}           {bool}            bool~                               {tt}{tt} _ = ttp
symEl {a₀ = bool}           {bool}            bool~                               {ff}{ff} _ = ttp
symEl {a₀ = π a₀ a₀~ b₀ b₀~}{π a₁ a₁~ b₁ b₁~}(π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁) {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ =
  symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) x₀₁))) (f₀₁ _ _ (symEl (proj₂ (symU a₀₁)) x₀₁))

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

U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
EL U γ = record {
  ∣_∣C = ∣U∣ ;
  _⊢_~_ = _~U_ ;
  refC = refU ;
  symC = λ Â₀₁ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → tr (symU a₀₁) }  ;
  transC = λ Â₀₁ Â₁₂ → withTrunc Â₀₁ λ { (_ ,Σ a₀₁) → withTrunc Â₁₂ λ { (_ ,Σ a₁₂) → tr (transU a₀₁ a₁₂) } } }
subst U γ~ = record { ∣_∣s = λ Â → Â ; ~s = λ Â~ → Â~ }
subst-ref U = refU
subst-trans U = λ _ _ → refU

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
EL (El {Γ = Γ} Â) γ = record {
  ∣_∣C = ∣El∣ (∣ Â ∣t γ) ;
  _⊢_~_ = El~ (~t Â (refC Γ γ)) ;
  refC = refEl {∣ Â ∣t γ} ;
  symC = λ {_}{_} → withTrunc (~t Â (refC Γ γ)) λ { (_ ,Σ a₀₁) → symEl a₀₁ } ;
  transC = λ {_}{_}{_} → withTrunc (~t Â (refC Γ γ)) λ { (_ ,Σ a₀₁) → withTrunc (~t Â (refC Γ γ)) λ { (_ ,Σ a₁₂) → transEl a₀₁ a₁₂ } } }
subst (El {Γ = Γ} Â) {γ}{γ'} γ~ = record {
  ∣_∣s = coeEl (~t Â γ~) ;
  ~s = λ {α}{α'} α~ → {!withTrunc (~t Â γ~) λ { (_ ,Σ a₀₁) → symEl a₀₁ (cohEl (~t Â γ~) α) }!} } --  
subst-ref (El {Γ = Γ} Â) {γ} α = withTrunc (~t Â (refC Γ γ)) λ { (_ ,Σ a₀₁) → symEl a₀₁ (cohEl (~t Â (refC Γ γ)) α) }
subst-trans (El Â) = {!!}

{-
mkTy
  (λ γ → ∣El∣ (∣ Â ∣t γ))
  (λ γ₀₁ → El~ (~t Â γ₀₁))
  (λ {γ} → refEl {∣ Â ∣t γ})
  (λ {_}{_}{γ₀₁} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → symEl a₀₁ })
  (λ {_}{_}{_}{γ₀₁}{γ₁₂} → withTrunc (~t Â γ₀₁) λ { (_ ,Σ a₀₁) → withTrunc (~t Â γ₁₂) λ { (_ ,Σ a₁₂) → transEl a₀₁ a₁₂ } })
  (λ {_}{_} γ₀₁ → coeEl (~t Â γ₀₁))
  (λ {_}{_} γ₀₁ → cohEl (~t Â γ₀₁))
-}
ΠS : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
ΠS {Γ = Γ} Â B̂ = record {
  ∣_∣t = λ γ → _ ,Σ π
    (proj₂ (∣ Â ∣t γ))
    (in-El~ (refU (∣ Â ∣t γ)))
    (λ x → proj₂ (∣ B̂ ∣t (γ ,Σ x)))
    {λ x₀₁ → El~ (~t B̂ (refC Γ γ ,p {!x₀₁!}))}
    (λ x₀₁ → in-El~ (~t B̂ (refC Γ γ ,p {!!}))) ;
  ~t = λ {γ₀}{γ₁} γ₀₁ → tr (_ ,Σ π~
    (in-El~ (~t Â γ₀₁))
    {B₀₁ = λ x₀₁ → El~ (~t B̂ (γ₀₁ ,p {!!}))}
     λ x₀₁ → in-El~ (~t B̂ (γ₀₁ ,p {!!}))) }

BoolS : ∀{i}{Γ : Con i} → Tm Γ U
BoolS = record {
  ∣_∣t = λ _ → _ ,Σ bool ;
  ~t = λ _ → tr (_ ,Σ bool~) }

