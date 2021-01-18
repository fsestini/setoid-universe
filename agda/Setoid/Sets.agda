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
∣El∣ = proj₁

_~U_ : ∣U∣ → ∣U∣ → Prop₁
Â₀ ~U Â₁ = Tr (Σ (proj₁ Â₀ → proj₁ Â₁ → Prop) (λ A₀₁ → in-U~ (proj₂ Â₀) (proj₂ Â₁) A₀₁))

El~' : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁) → Σsp
  ((A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop) λ A₀₁' →
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁' (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ ↔ A₀₁ x₀ x₁
El~' = double.ind-in-U
  (λ {A₀}{A₁} a₀ a₁ → Σsp
  ((A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop) λ A₀₁' →
  {A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁' (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ ↔ A₀₁ x₀ x₁)
  ((λ _ x₀ x₁ → x₀ ≟𝟚 x₁) ,sp λ { bool~ {x₀}{x₁} → (λ x₀₁ → x₀₁) ,p (λ x₀₁ → x₀₁) })
  (λ a a~ b b~ → (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ())
  (λ a a~ b b~ → (λ w _ _ → ⊥pelim (withTrunc w λ ())) ,sp λ ())
  λ {A₀}{A₁} El~a₀a₁ a~₀ a~₁ El~b₀b₁ b~₀ b~₁ → (λ w f₀ f₁ → (x₀ : A₀)(x₁ : A₁)(x₀₁ : ↑ps (proj₁sp El~a₀a₁ (withTrunc w λ { (_ ,Σ π~ a₀₁ _) → tr (_ ,Σ a₀₁) }) x₀ x₁)) →
    proj₁sp (El~b₀b₁ x₀ x₁) (withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ ((proj₁p (proj₂sp El~a₀a₁ a₀₁)) (un↑ps x₀₁))) }) (proj₁sp f₀ x₀) (proj₁sp f₁ x₁)) ,sp
    λ { (π~ {A₀₁ = A₀₁} a₀₁ b₀₁) →
      (λ f₀₁ x₀ x₁ x₀₁ → proj₁p ((proj₂sp (El~b₀b₁ x₀ x₁)) (b₀₁ (un↑ps x₀₁))) (f₀₁ _ _ (mk↑ps (proj₂p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁))))) ,p
      (λ f₀₁ x₀ x₁ x₀₁ → proj₂p (proj₂sp (El~b₀b₁ x₀ x₁) (b₀₁ (proj₁p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps (proj₁p (proj₂sp El~a₀a₁ a₀₁) (un↑ps x₀₁))))) }

El~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁) → A₀ → A₁ → Prop
El~ {a₀ = a₀}{a₁} = proj₁sp (El~' a₀ a₁)

fromEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → A₀₁ x₀ x₁
fromEl~ {a₀ = a₀}{a₁} a~ = proj₁p (proj₂sp (El~' a₀ a₁) a~)

toEl~ : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} → A₀₁ x₀ x₁ → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁
toEl~ {a₀ = a₀}{a₁} a~ = proj₂p (proj₂sp (El~' a₀ a₁) a~)

in-El~ : ∀{A₀ A₁}(a₀ : in-U A₀)(a₁ : in-U A₁)(w : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁)) → in-U~ a₀ a₁ (El~ w)
in-El~ bool bool w = bool~
in-El~ bool (π a a~ b b~) w = ⊥pelim (withTrunc w λ ())
in-El~ (π a a~ b b~) bool w = ⊥pelim (withTrunc w λ ())
in-El~ (π a₀ a₀~ b₀ b₀~)(π a₁ a₁~ b₁ b₁~) w =  π~ 
  (in-El~ a₀ a₁ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ a₀₁) })))
  {B₀₁ = λ x₀₁ → El~ (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) }))}
  (λ x₀₁ → in-El~ (b₀ _) (b₁ _) (withTrunc w (λ { (_ ,Σ π~ a₀₁ b₀₁) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ x₀₁)) })))

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

sym : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) →
  Σsp (Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)) λ a₁₀' → ({x₀ : A₀}{x₁ : A₁} → El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr a₁₀') x₁ x₀) ×p ({x₀ : A₀}{x₁ : A₁} → El~ (tr a₁₀') x₁ x₀ → El~ (tr (_ ,Σ a₀₁)) x₀ x₁)
sym = simple.ind-in-U~ (λ _ → ⊤) (λ {A₀}{A₁}{a₀}{a₁} a₀₁ → Σsp (Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)) λ a₁₀' → ({x₀ : A₀}{x₁ : A₁} → El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr a₁₀') x₁ x₀) ×p ({x₀ : A₀}{x₁ : A₁} → El~ (tr a₁₀') x₁ x₀ → El~ (tr (_ ,Σ a₀₁)) x₀ x₁)) tt (λ _ _ _ _ → tt)
  ((_ ,Σ bool~) ,sp ((λ { {tt}{tt} _ → ttp ; {ff}{ff} _ → ttp }) ,p (λ { {tt}{tt} _ → ttp ; {ff}{ff} _ → ttp })))
  λ {A₀}{a₀} _ {A₀~}{a₀~} _ {A₁}{a₁} _ _ {A₀₁}{a₀₁} symA₀₁ {B₀}{b₀} _ {B₀~}{b₀~} _ {B₁}{b₁} _ {B₁~}{b₁~} _ {B₀₁}{b₀₁} symB₀₁ →
    _ ,Σ π~ (proj₂ (proj₁sp symA₀₁)) {B₀₁ = λ x₀₁ → proj₁ (proj₁sp (symB₀₁ (fromEl~ a₀₁ (proj₂p (proj₂sp symA₀₁) (toEl~ (proj₂ (proj₁sp symA₀₁)) x₀₁)))))} (λ x₀₁ →  proj₂ (proj₁sp (symB₀₁ (fromEl~ a₀₁ (proj₂p (proj₂sp symA₀₁) (toEl~ (proj₂ (proj₁sp symA₀₁)) x₀₁)))))) ,sp
    ((λ {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ → proj₁p (proj₂sp (symB₀₁ (fromEl~ a₀₁ (proj₂p (proj₂sp symA₀₁) (un↑ps x₀₁))))) (f₀₁ _ _ (mk↑ps (proj₂p (proj₂sp symA₀₁) (un↑ps x₀₁))))) ,p
    λ {f₀}{f₁} f₀₁ x₀ x₁ x₀₁ → proj₂p (proj₂sp (symB₀₁ (fromEl~ a₀₁ (un↑ps x₀₁)))) (f₀₁ _ _ (mk↑ps (proj₁p (proj₂sp symA₀₁) (un↑ps x₀₁)))))

symU  : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁) → Σ (A₁ → A₀ → Prop) (in-U~ a₁ a₀)
symU a₀₁ = proj₁sp (sym a₀₁)

symEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}{A₀₁ : A₀ → A₁ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁){x₀ : A₀}{x₁ : A₁} →
  El~ (tr (_ ,Σ a₀₁)) x₀ x₁ → El~ (tr (symU a₀₁)) x₁ x₀
symEl a₀₁ = proj₁p (proj₂sp (sym a₀₁))

theT : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → Set₁
theT {A₀} {A₁} {A₂} a₀ a₁ a₂ =
  ((Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → Σsp A₁ λ x₁ → El~ Â₀₁ x₀ x₁) ×
  ({A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂) →
  Σsp (Σ (A₀ → A₂ → Prop) (in-U~ a₀ a₂)) λ a₀₂ →
      {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → El~ (tr (A₁₂ ,Σ a₁₂)) x₁ x₂ → El~ (tr a₀₂) x₀ x₂)

cotr-simple : ∀{A₀ A₁ A₂} (a₀ : in-U A₀) (a₁ : in-U A₁) (a₂ : in-U A₂) → theT a₀ a₁ a₂
cotr-simple =
  triple theT
    ((λ Â₀₁ t → t ,sp refEl {_ ,Σ bool} t) ,Σ λ { bool~ bool~ → (_ ,Σ bool~) ,sp λ { {tt}{tt}{tt} _ _ → ttp ; {ff}{ff}{ff} _ _ → ttp } })
    ((λ { _ tt → tt ,sp ttp ; _ ff → ff ,sp ttp }) ,Σ λ _ ())
    ((λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ λ ())
    ((λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ λ ())
    (λ {A₀} {a₀} {A₀~} {a₀~} {A₁} {a₁} {A₁~} {a₁~} {B₀} {b₀} {B₀~} {b₀~} {B₁} {b₁} {B₁~} {b₁~} a100 a010 a110 b001 b101 b011 →
      let coEl-simple = proj₁ a100
      in (λ { w (f₀ ,sp f₀~) → (
                (λ x₁ → proj₁sp (proj₁ (b011 (proj₁sp (coEl-simple (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁)) x₁ x₁)
                              (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))) })
                              (f₀ (proj₁sp (proj₁ a100 (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))))) ,sp
                λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ (un↑ps x₀₁)) (proj₂sp (proj₂ (b101 _ _ _)
                    (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))))))
                    (proj₂ (proj₁sp (proj₂ (b001 _ _ _) (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁)))
                     (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁)))
                       (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl-simple (tr (symU a₀₁)) x₁)))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁))
                         (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))))
                    (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))))
                         (proj₂sp (proj₁ (b011 (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₀)) _ _)
                                (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))))))
                                (f₀ (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₀))))))

                 (proj₂sp (proj₂ (b001 _ _ _)
                           (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁))
                             (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁))
                              (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                           (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                           (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁))
                            (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁))
                             (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                                  (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁))
                                   (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁))
                                    (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))))
                           (proj₂sp (proj₁ (b011 (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₁)) _ _)
                                     (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                                     (f₀ (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))
                      }) ,sp (
                     λ { x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → proj₂sp (proj₂ (b001 _ _ _)
                     (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))
                     (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                     (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))
                            (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))
                     (proj₂sp (proj₁ (b011 _ _ _) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁))
                      (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))) (f₀ _))) } }) }) ,Σ λ _ ()
         )
    λ { {A₀} {a₀} {A₀~} {a₀~} {A₁} {a₁} {A₁~} {a₁~} {A₂} {a₂} {A₂~} {a₂~}
        {B₀} {b₀} {B₀~} {b₀~} {B₁} {b₁} {B₁~} {b₁~} {B₂} {b₂} {B₂~} {b₂~}
        a100 a010 a110 a101 a012 a021 a011 a211 b001 b101 b011 b012 b112 →

          (λ { w (f₀ ,sp f₀~) → (
            (λ x₁ → proj₁sp (proj₁ (b011 (proj₁sp (proj₁ a100 (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁)) _ x₁)
                          (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))) })
                          (f₀ (proj₁sp (proj₁ a100 (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))))) ,sp
            λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ (un↑ps x₀₁)) (proj₂sp (proj₂ (b101 _ _ _)
                (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))))))
                (proj₂ (proj₁sp (proj₂ (b001 _ _ _) (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁)))
                 (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁))
                  (proj₂sp ((proj₁ a100 (tr (symU a₀₁)) x₁)) ))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))))
                (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))))
                     (proj₂sp (proj₁ (b011 (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₀)) _ _)
                            (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))))))
                            (f₀ (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₀))))))
                (proj₂sp (proj₂ (b001 _ _ _)
                  (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))
                   (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                  (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                  (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁))
                   (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                         (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₀)))
                          (proj₂sp (proj₂ a110 a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))))
                  (proj₂sp (proj₁ (b011 (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₁)) _ _)
                            (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
                            (f₀ (proj₁sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))
             }) ,sp (
            λ { x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → proj₂sp (proj₂ (b001 _ _ _)
            (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))
            (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁))))))
            (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))
                   (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ a010 a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))))
            (proj₂sp (proj₁ (b011 _ _ _) (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ a100 (tr (symU a₀₁)) x₁)))))) (f₀ _))) } }) }) ,Σ
          λ { (π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)(π~ {A₀₁ = A₁₂} a₁₂ {B₀₁ = B₁₂} b₁₂) →
              (_ ,Σ
              π~ (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                 λ {x₀}{x₂} x₀₂ → proj₂ (proj₁sp (proj₂ (b012 _ _ _)
                   (b₀₁ (fromEl~ a₀₁ (proj₂sp ((proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)) )))
                   (proj₂ (proj₁sp (proj₂ (b112 _ _ _)
                   (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ a101 (proj₂ (symU a₀₁)) a₀₁)
                      (symEl a₀₁ (proj₂sp ((proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)) ))
                      (proj₂sp (proj₂ a021
                        (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                        (proj₂ (symU a₁₂)))
                        (toEl~ (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂))) x₀₂)
                        (proj₂sp ((proj₁ a211 (tr (symU a₁₂)) x₂)) ))))) (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂))
                          (proj₂sp ((proj₁ a211 (tr (symU a₁₂)) x₂)))))))))))) ,sp
              (λ { {f₀ ,sp f₀~}{f₁ ,sp f₁~}{f₂ ,sp f₂~} f₀₁ f₁₂ x₀ x₂ x₀₂ →
              proj₂sp (proj₂ (b012 _ _ _)
                (b₀₁ (fromEl~ a₀₁ (proj₂sp ((proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)))))
                (proj₂ (proj₁sp (proj₂ (b112 _ _ _)
                  (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ a101 (proj₂ (symU a₀₁)) a₀₁)
                    (symEl a₀₁ (proj₂sp (proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)))
                    (proj₂sp (proj₂ a021
                      (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                      (proj₂ (symU a₁₂)))
                      (un↑ps x₀₂)
                      (proj₂sp ((proj₁ a211 (tr (symU a₁₂)) x₂)))))))
                  (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ a211 (tr (symU a₁₂)) x₂)))))))))
                (f₀₁ _ _ (mk↑ps (proj₂sp (proj₁ a011 (tr (_ ,Σ a₀₁)) x₀))))
                (proj₂sp (proj₂ (b112 _ _ _)
                  (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ a101 (proj₂ (symU a₀₁)) a₀₁)
                    (symEl a₀₁ (proj₂sp (proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)))
                    (proj₂sp (proj₂ a021
                      (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                      (proj₂ (symU a₁₂)))
                      (un↑ps x₀₂)
                      (proj₂sp ((proj₁ a211 (tr (symU a₁₂)) x₂)))))))
                  (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ a211 (tr (symU a₁₂)) x₂))))))
                  (toEl~ (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ a101 (proj₂ (symU a₀₁)) a₀₁)
                    (symEl a₀₁ (proj₂sp (proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)))
                    (proj₂sp (proj₂ a021
                      (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                      (proj₂ (symU a₁₂)))
                      (un↑ps x₀₂)
                      (proj₂sp (proj₁ a211 (tr (symU a₁₂)) x₂)))))) (f₁~ _ _ (mk↑ps (fromEl~ a₁~ (proj₂sp (proj₂ a101
                    (proj₂ (symU a₀₁))
                    a₀₁)
                    (symEl a₀₁ (proj₂sp (proj₁ a011 (tr (_ ,Σ a₀₁)) x₀)))
                    (proj₂sp (proj₂ a021
                      (proj₂ (proj₁sp (proj₂ a012 a₀₁ a₁₂)))
                      (proj₂ (symU a₁₂)))
                      (un↑ps x₀₂)
                      (proj₂sp (proj₁ a211 (tr (symU a₁₂)) x₂))))))))
                  (f₁₂ _ _ (mk↑ps (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ a211 (tr (symU a₁₂)) x₂)))))) })
            } }

cotr  : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂} →
  ((Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → Σsp A₁ λ x₁ → El~ Â₀₁ x₀ x₁) ×
  ({A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂) →
  Σsp (Σ (A₀ → A₂ → Prop) (in-U~ a₀ a₂)) λ a₀₂ →
      {x₀ : A₀}{x₁ : A₁}{x₂ : A₂} → El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → El~ (tr (A₁₂ ,Σ a₁₂)) x₁ x₂ → El~ (tr a₀₂) x₀ x₂)
cotr {a₀ = a₀}{a₁}{a₂} = cotr-simple a₀ a₁ a₂

coEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → Σsp A₁ λ x₁ → El~ Â₀₁ x₀ x₁
coEl {a₀ = a₀}{a₁ = a₁} = proj₁ (cotr {a₀ = a₀}{a₁ = a₁}{a₂ = a₁})

{-
coEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁} → (Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → Σsp A₁ λ x₁ → El~ Â₀₁ x₀ x₁
coEl {a₀ = a₀}{a₁ = a₁} = proj₁ (cotr {a₀ = a₀}{a₁ = a₁}{a₂ = a₁})

cotr {a₀ = bool}{a₁ = bool}{a₂ = bool} =
  (λ Â₀₁ t → t ,sp refEl {_ ,Σ bool} t) ,Σ
  λ { bool~ bool~ → (_ ,Σ bool~) ,sp λ { {tt}{tt}{tt} _ _ → ttp ; {ff}{ff}{ff} _ _ → ttp } }
cotr {a₀ = bool}{a₁ = bool}{a₂ = π a a~ b b~} =
  (λ { _ tt → tt ,sp ttp ; _ ff → ff ,sp ttp }) ,Σ λ _ ()
cotr {a₀ = bool}{a₁ = π a a~ b b~} = (λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ λ ()
cotr {a₀ = π a a~ b b~}{a₁ = bool} = (λ w _ → ⊥pelim (withTrunc w λ ())) ,Σ λ ()

cotr {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{a₁ = π {A₁} a₁ a₁~ b₁ b₁~}{a₂ = bool} =
  (λ { w (f₀ ,sp f₀~) → (
    (λ x₁ → proj₁sp ((coEl {a₀ = b₀ (proj₁sp (coEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))})
                  (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))) })
                  (f₀ (proj₁sp (proj₁ cotr (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))))) ,sp
    λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ (un↑ps x₀₁)) (proj₂sp (proj₂ cotr
        (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀)))))))
        (proj₂ (proj₁sp (proj₂ cotr (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))))
        (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀)))))
             (proj₂sp (proj₁ (cotr {a₀ = b₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₀))})
                    (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))))))
                    (f₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₀))))))
        (proj₂sp (proj₂ cotr
          (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
          (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
          (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
                 (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))))
          (proj₂sp (proj₁ (cotr {a₀ = b₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₁))})
                    (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
                    (f₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))
     }) ,sp (
    λ { x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → proj₂sp (proj₂ cotr
    (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))
    (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
    (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))
           (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))
    (proj₂sp (proj₁ cotr (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))) (f₀ _))) } }) }) ,Σ λ _ ()

cotr {a₀ = π {A₀} a₀ a₀~ b₀ b₀~}{a₁ = π {A₁} a₁ a₁~ b₁ b₁~}{a₂ = π {A₂} a₂ a₂~ {B₂} b₂ b₂~} =
  (λ { w (f₀ ,sp f₀~) → (
    (λ x₁ → proj₁sp ((coEl {a₀ = b₀ (proj₁sp (coEl (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))})
                  (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))) })
                  (f₀ (proj₁sp (proj₁ cotr (withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → tr (symU a₀₁) }) x₁))))) ,sp
    λ x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ (π~ a₀₁ b₀₁)) → fromEl~ (b₁~ (un↑ps x₀₁)) (proj₂sp (proj₂ cotr
        (proj₂ (symU (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀)))))))
        (proj₂ (proj₁sp (proj₂ cotr (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (coEl (tr (symU a₀₁)) x₁)))))) (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))))
        (symEl (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀)))))
             (proj₂sp (proj₁ (cotr {a₀ = b₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₀))})
                    (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))))))
                    (f₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₀))))))
        (proj₂sp (proj₂ cotr
          (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
          (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
          (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
                 (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₀))) (proj₂sp (proj₂ cotr a₁~ (proj₂ (symU a₀₁))) (toEl~ a₁~ (un↑ps x₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))))
          (proj₂sp (proj₁ (cotr {a₀ = b₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₁))})
                    (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
                    (f₀ (proj₁sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))
     }) ,sp (
    λ { x₀ x₁ x₀₁ → withTrunc w λ { (_ ,Σ π~ a₀₁ b₀₁) → proj₂sp (proj₂ cotr
    (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))
    (b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁))))))
    (toEl~ (b₀~ (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))
           (f₀~ _ _ (mk↑ps (fromEl~ a₀~ (proj₂sp (proj₂ cotr a₀₁ (proj₂ (symU a₀₁))) (un↑ps x₀₁) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))))
    (proj₂sp (proj₁ cotr (tr (_ ,Σ b₀₁ (fromEl~ a₀₁ (symEl (proj₂ (symU a₀₁)) (proj₂sp (proj₁ cotr (tr (symU a₀₁)) x₁)))))) (f₀ _))) } }) }) ,Σ
  λ { (π~ {A₀₁ = A₀₁} a₀₁ {B₀₁ = B₀₁} b₀₁)(π~ {A₀₁ = A₁₂} a₁₂ {B₀₁ = B₁₂} b₁₂) →
      (_ ,Σ
      π~ (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
         λ {x₀}{x₂} x₀₂ → proj₂ (proj₁sp (proj₂ cotr
           (b₀₁ (fromEl~ a₀₁ (proj₂sp (coEl (tr (_ ,Σ a₀₁)) x₀))))
           (proj₂ (proj₁sp (proj₂ cotr
           (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ cotr
              (proj₂ (symU a₀₁))
              a₀₁)
              (symEl a₀₁ (proj₂sp (coEl (tr (_ ,Σ a₀₁)) x₀)))
              (proj₂sp (proj₂ cotr
                (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
                (proj₂ (symU a₁₂)))
                (toEl~ (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂))) x₀₂)
                (proj₂sp (coEl (tr (symU a₁₂)) x₂)))))) (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (proj₂sp (coEl (tr (symU a₁₂)) x₂))))))))))) ,sp
      (λ { {f₀ ,sp f₀~}{f₁ ,sp f₁~}{f₂ ,sp f₂~} f₀₁ f₁₂ x₀ x₂ x₀₂ →
      proj₂sp (proj₂ cotr
        (b₀₁ (fromEl~ a₀₁ (proj₂sp (coEl (tr (_ ,Σ a₀₁)) x₀))))
        (proj₂ (proj₁sp (proj₂ cotr
          (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ cotr
            (proj₂ (symU a₀₁))
            a₀₁)
            (symEl a₀₁ (proj₂sp (proj₁ cotr (tr (_ ,Σ a₀₁)) x₀)))
            (proj₂sp (proj₂ cotr
              (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
              (proj₂ (symU a₁₂)))
              (un↑ps x₀₂)
              (proj₂sp (coEl (tr (symU a₁₂)) x₂))))))
          (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ cotr (tr (symU a₁₂)) x₂)))))))))
        (f₀₁ _ _ (mk↑ps (proj₂sp (proj₁ cotr (tr (_ ,Σ a₀₁)) x₀))))
        (proj₂sp (proj₂ cotr
          (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ cotr
            (proj₂ (symU a₀₁))
            a₀₁)
            (symEl a₀₁ (proj₂sp (proj₁ cotr (tr (_ ,Σ a₀₁)) x₀)))
            (proj₂sp (proj₂ cotr
              (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
              (proj₂ (symU a₁₂)))
              (un↑ps x₀₂)
              (proj₂sp (coEl (tr (symU a₁₂)) x₂))))))
          (b₁₂ (fromEl~ a₁₂ (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ cotr (tr (symU a₁₂)) x₂))))))
          (toEl~ (b₁~ (fromEl~ a₁~ (proj₂sp (proj₂ cotr
            (proj₂ (symU a₀₁))
            a₀₁)
            (symEl a₀₁ (proj₂sp (proj₁ cotr (tr (_ ,Σ a₀₁)) x₀)))
            (proj₂sp (proj₂ cotr
              (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
              (proj₂ (symU a₁₂)))
              (un↑ps x₀₂)
              (proj₂sp (proj₁ cotr (tr (symU a₁₂)) x₂)))))) (f₁~ _ _ (mk↑ps (fromEl~ a₁~ (proj₂sp (proj₂ cotr
            (proj₂ (symU a₀₁))
            a₀₁)
            (symEl a₀₁ (proj₂sp (proj₁ cotr (tr (_ ,Σ a₀₁)) x₀)))
            (proj₂sp (proj₂ cotr
              (proj₂ (proj₁sp (proj₂ cotr a₀₁ a₁₂)))
              (proj₂ (symU a₁₂)))
              (un↑ps x₀₂)
              (proj₂sp (proj₁ cotr (tr (symU a₁₂)) x₂))))))))
          (f₁₂ _ _ (mk↑ps (symEl (proj₂ (symU a₁₂)) (proj₂sp (proj₁ cotr (tr (symU a₁₂)) x₂)))))) })
    }  
-}

transU : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂) →
  Σ (A₀ → A₂ → Prop) (in-U~ a₀ a₂)
transU a₀₁ a₁₂ = proj₁sp (proj₂ cotr a₀₁ a₁₂)

transEl : ∀{A₀ A₁ A₂}{a₀ : in-U A₀}{a₁ : in-U A₁}{a₂ : in-U A₂}{A₀₁ : A₀ → A₁ → Prop}{A₁₂ : A₁ → A₂ → Prop}(a₀₁ : in-U~ a₀ a₁ A₀₁)(a₁₂ : in-U~ a₁ a₂ A₁₂){x₀ : A₀}{x₁ : A₁}{x₂ :
 A₂} →
  El~ (tr (A₀₁ ,Σ a₀₁)) x₀ x₁ → El~ (tr (A₁₂ ,Σ a₁₂)) x₁ x₂ → El~ (tr (transU a₀₁ a₁₂)) x₀ x₂
transEl a₀₁ a₁₂ = proj₂sp (proj₂ cotr a₀₁ a₁₂)

coeEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → A₁
coeEl Â₀₁ x₀ = proj₁sp (coEl Â₀₁ x₀)

cohEl : ∀{A₀ A₁}{a₀ : in-U A₀}{a₁ : in-U A₁}(Â₀₁ : (A₀ ,Σ a₀) ~U (A₁ ,Σ a₁))(x₀ : A₀) → El~ Â₀₁ x₀ (coeEl Â₀₁ x₀)
cohEl Â₀₁ x₀ = proj₂sp (coEl Â₀₁ x₀)

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

