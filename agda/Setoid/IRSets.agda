{-# OPTIONS --without-K --prop #-}

module Setoid.IRSets where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF


-- an inductive-recursive universe of sets
module IR where

  data U : Set₁
  _~U_ : U → U → Prop₁
  refU : (a : U) → a ~U a
  El : U → Set
  _⊢_~El_ : {a a' : U}(a~ : a ~U a') → El a → El a' → Prop

  data U where
    bool : U
    π : (a : U)(b : El a → U)(refb : {x x' : El a}(x~ : refU a ⊢ x ~El x') → b x ~U b x') → U
    ⊥s : U
    Σs : (a : U)(b : El a → U)(refb : {x x' : El a}(x~ : refU a ⊢ x ~El x') → b x ~U b x') → U
    ι : Prop → U

  -- El (π a b refb) = Σsp ((x : El a) → El (b x)) λ f → {x x' : El a}(x~ : refU a ⊢ x ~El x') → refb x~ ⊢ f x ~El f x'

  bool ~U bool = ⊤p'
  ⊥s ~U ⊥s = ⊤p'
  Σs a b refb ~U Σs a' b' refb' = Σp (a ~U a') λ a~ → {x : El a}{x' : El a'}(x~ : a~ ⊢ x ~El x') → b x ~U b' x'
  π a b refb ~U π a' b' refb' = Σp (a ~U a') λ a~ → {x : El a}{x' : El a'}(x~ : a~ ⊢ x ~El x') → b x ~U b' x'
  ι a ~U ι b = ↑pl ((a → b) ×p (b → a))
  _ ~U _ = ⊥p'

  refU bool = ttp'
  refU ⊥s = ttp'
  refU (Σs a b refb) = refU a ,p λ x~ → refb x~
  refU (π a b refb) = refU a ,p λ x~ → refb x~
  refU (ι a) = mk↑pl ((λ x → x) ,p (λ x → x))

  El bool = 𝟚
  El ⊥s = ⊥
  El (Σs a b refb) = Σ (El a) λ x → El (b x)
  El (π a b refb) = Σsp ((x : El a) → El (b x)) λ f → (x x' : El a)(x~ : ↑ps (refU a ⊢ x ~El x')) → refb (un↑ps x~) ⊢ f x ~El f x'
  El (ι a) = ↑ps a

  _⊢_~El_ {bool} {bool} a~ x₀ x₁ = x₀ ≟𝟚 x₁
  _⊢_~El_ {bool} {⊥s} () x x'
  _⊢_~El_ {bool} {Σs a' b' refb'} () x x'
  _⊢_~El_ {bool} {π a' b' refb'} () x x'
  _⊢_~El_ {bool} {ι a} () x x'
  _⊢_~El_ {⊥s} {bool} () x x'
  _⊢_~El_ {⊥s} {⊥s} a~ x x' = ⊤p
  _⊢_~El_ {⊥s} {Σs a' b' refb'} () x x'
  _⊢_~El_ {⊥s} {π a' b' refb'} () x x'
  _⊢_~El_ {⊥s} {ι a} () x x'
  _⊢_~El_ {Σs a b refb} {bool} () x x'
  _⊢_~El_ {Σs a b refb} {⊥s} () x x'
  _⊢_~El_ {Σs a b refb} {Σs a' b' refb'} w~ (x ,Σ y) (x' ,Σ y') = Σp (proj₁p w~ ⊢ x ~El x') λ x~ → proj₂p w~ x~ ⊢ y ~El y'
  _⊢_~El_ {Σs a b refb} {π a' b' refb'} () x x'
  _⊢_~El_ {Σs a b refb} {ι c} () x x'
  _⊢_~El_ {π a b refb} {bool} () x x'
  _⊢_~El_ {π a b refb} {⊥s} () x x'
  _⊢_~El_ {π a b refb} {Σs a' b' refb'} () x x'
  _⊢_~El_ {π a b refb} {π a' b' refb'} w~ (f ,sp _) (f' ,sp _) = (x : El a)(x' : El a')(x~ : ↑ps (proj₁p w~ ⊢ x ~El x')) → proj₂p w~ (un↑ps x~) ⊢ f x ~El f' x'
  _⊢_~El_ {π a b refb} {ι c} () x x'
  _⊢_~El_ {ι a} {bool} ()
  _⊢_~El_ {ι a} {⊥s} ()
  _⊢_~El_ {ι a} {Σs b b₁ refb} ()
  _⊢_~El_ {ι a} {π b b₁ refb} ()
  _⊢_~El_ {ι a} {ι b} _ x y = ⊤p'


  refEl : {a : U}(x : El a) → refU a ⊢ x ~El x
  refEl {bool} x = ref𝟚 x
  refEl {⊥s} x = ttp
  refEl {Σs a b refb} (x ,Σ y) = refEl x ,p refEl y
  refEl {π a b refb} (f ,sp reff) _ _ x~ = reff _ _ x~
  refEl {ι a} x = ttp'


  symU : {a a' : U}(a~ : a ~U a') → a' ~U a
  symEl : {a a' : U}{a~ : a ~U a'}{x : El a}{x' : El a'}(x~ : a~ ⊢ x ~El x') → symU a~ ⊢ x' ~El x

  symU {bool} {bool} a~ = ttp'
  symU {bool} {⊥s} ()
  symU {bool} {Σs a' b' refb'} ()
  symU {bool} {π a' b' refb'} ()
  symU {⊥s} {bool} ()
  symU {⊥s} {⊥s} a~ = ttp'
  symU {⊥s} {Σs a' b' refb'} ()
  symU {⊥s} {π a' b' refb'} ()
  symU {Σs a b refb} {bool} ()
  symU {Σs a b refb} {⊥s} ()
  symU {Σs a b refb} {Σs a' b' refb'}(a~ ,p b~) = symU a~ ,p λ x~ → symU (b~ (symEl {a~ = symU a~} x~))
  symU {Σs a b refb} {π a' b' refb'} ()
  symU {π a b refb} {bool} ()
  symU {π a b refb} {⊥s} ()
  symU {π a b refb} {Σs a' b' refb'} ()
  symU {π a b refb} {π a' b' refb'}(a~ ,p b~) = symU a~ ,p λ x~ → symU (b~ (symEl {a~ = symU a~} x~))
  symU {ι a} {bool} ()
  symU {ι a} {⊥s} ()
  symU {ι a} {Σs b b₁ refb} ()
  symU {ι a} {π b b₁ refb} ()
  symU {ι a} {ι x₁} (mk↑pl (f ,p g)) = mk↑pl (g ,p f)

  symEl {bool} {bool} {a~} {x} {x'} x~ = sym𝟚 {x} {x'} x~
  symEl {bool} {⊥s} {()}
  symEl {bool} {Σs a' b' refb'} {()}
  symEl {bool} {π a' b' refb'} {()}
  symEl {⊥s} {bool} {()}
  symEl {⊥s} {⊥s} {a~} {x} {x'} x~ = ttp
  symEl {⊥s} {Σs a' b' refb'} {()}
  symEl {⊥s} {π a' b' refb'} {()}
  symEl {Σs a b refb} {bool} {()}
  symEl {Σs a b refb} {⊥s} {()}
  symEl {Σs a b refb} {Σs a' b' refb'} {w~} {x ,Σ y} {x' ,Σ y'}(x~ ,p y~) = symEl {a} x~ ,p symEl {b x} y~
  symEl {Σs a b refb} {π a' b' refb'} {()}
  symEl {π a b refb} {bool} {()}
  symEl {π a b refb} {⊥s} {()}
  symEl {π a b refb} {Σs a' b' refb'} {()}
  symEl {π a b refb} {π a' b' refb'} {w~} {f ,sp _} {f' ,sp _} f~ x x' x~ = symEl {b x'} (f~ _ _ (mk↑ps (symEl {a'} (un↑ps x~))))
  symEl {ι a} {bool} {()}
  symEl {ι a} {⊥s} {()}
  symEl {ι a} {Σs b b₁ refb} {()}
  symEl {ι a} {π b b₁ refb} {()}
  symEl {ι a} {ι b} x = x


  transU : {a a' a'' : U}(a~ : a ~U a')(a~' : a' ~U a'') → a ~U a''
  transEl : {a a' a'' : U}{a~ : a ~U a'}{a~' : a' ~U a''}{x : El a}{x' : El a'}{x'' : El a''}
    (x~ : a~ ⊢ x ~El x')(x~' : a~' ⊢ x' ~El x'') → transU a~ a~' ⊢ x ~El x''
  coeEl : {a a' : U}(a~ : a ~U a') → El a → El a'
  cohEl : {a a' : U}(a~ : a ~U a')(x : El a) → a~ ⊢ x ~El coeEl a~ x

  transU {bool} {bool} {bool} a~ a~' = ttp'
  transU {bool} {bool} {⊥s} a~ ()
  transU {bool} {bool} {Σs a'' b'' refb''} a~ ()
  transU {bool} {bool} {π a'' b'' refb''} a~ ()
  transU {bool} {⊥s} {_} ()
  transU {bool} {Σs a' b refb'} {_} ()
  transU {bool} {π a' b refb'} {_} ()
  transU {⊥s} {bool} {_} ()
  transU {⊥s} {⊥s} {bool} a~ ()
  transU {⊥s} {⊥s} {⊥s} a~ a~' = ttp'
  transU {⊥s} {⊥s} {Σs a'' b'' refb''} a~ ()
  transU {⊥s} {⊥s} {π a'' b'' refb''} a~ ()
  transU {⊥s} {Σs a' b' refb'} {_} ()
  transU {⊥s} {π a' b' refb'} {_} ()
  transU {Σs a b refb} {bool} {_} ()
  transU {Σs a b refb} {⊥s} {_} ()
  transU {Σs a b refb} {Σs a' b' refb'} {bool} a~ ()
  transU {Σs a b refb} {Σs a' b' refb'} {⊥s} a~ ()
  transU {Σs a b refb} {Σs a' b' refb'} {Σs a'' b'' refb''} (a~ ,p b~) (a~' ,p b~') =
    transU a~ a~' ,p
    λ {x}{x''} x~ → transU (b~ (cohEl a~ x)) (transU
                           (refb' (transEl {a~ = symU a~} (symEl {a~ = a~} (cohEl a~ x)) (transEl {a~ = transU a~ a~'} x~ (cohEl (symU a~') x''))))
                           (b~' (symEl {a~ = symU a~'} (cohEl (symU a~') x''))))
  transU {Σs a b refb} {Σs a' b' refb'} {π a'' b'' refb''} a~ ()
  transU {Σs a b refb} {π a' b' refb'} {_} ()
  transU {π a b refb} {bool} {_} ()
  transU {π a b refb} {⊥s} {_} ()
  transU {π a b refb} {Σs a' b' refb'} {_} ()
  transU {π a b refb} {π a' b' refb'} {bool} a~ ()
  transU {π a b refb} {π a' b' refb'} {⊥s} a~ ()
  transU {π a b refb} {π a' b' refb'} {Σs a'' b'' refb''} a~ ()
  transU {π a b refb} {π a' b' refb'} {π a'' b'' refb''} (a~ ,p b~) (a~' ,p b~') =
    transU a~ a~' ,p
    λ {x}{x''} x~ → transU (b~ (cohEl a~ x)) (transU
                           (refb' (transEl {a~ = symU a~} (symEl {a~ = a~} (cohEl a~ x)) (transEl {a~ = transU a~ a~'} x~ (cohEl (symU a~') x'')) ))
                           (b~' (symEl {a~ = symU a~'} (cohEl (symU a~') x''))))
  transU {ι a} {bool} {c} ()
  transU {ι a} {⊥s} {c} ()
  transU {ι a} {Σs b b₁ refb} {c} ()
  transU {ι a} {π b b₁ refb} {c} ()
  transU {ι a} {ι b} {bool} x ()
  transU {ι a} {ι b} {⊥s} x ()
  transU {ι a} {ι b} {Σs c b₁ refb} x ()
  transU {ι a} {ι b} {π c b₁ refb} x ()
  transU {ι a} {ι b} {ι c} (mk↑pl (f ,p g)) (mk↑pl (f' ,p g')) = mk↑pl ((λ x → f' (f x)) ,p (λ y → g (g' y)))

  transEl {bool} {bool} {bool} {_} {_} {x} {x'} {x''} x~ x~' = trans𝟚 {x} {x'} {x''} x~ x~'
  transEl {bool} {bool} {⊥s} {_} {()}
  transEl {bool} {bool} {Σs a'' b'' refb''} {_} {()}
  transEl {bool} {bool} {π a'' b'' refb''} {_} {()}
  transEl {bool} {⊥s} {_} {()}
  transEl {bool} {Σs a' b' refb'} {_} {()}
  transEl {bool} {π a' b' refb'} {_} {()}
  transEl {⊥s} {bool} {_} {()}
  transEl {⊥s} {⊥s} {bool} {_} {()}
  transEl {⊥s} {⊥s} {⊥s} {_} {_} {x} {x'} {x''} x~ x~' = ttp
  transEl {⊥s} {⊥s} {Σs a'' b'' refb''} {_} {()}
  transEl {⊥s} {⊥s} {π a'' b'' refb''} {_} {()}
  transEl {⊥s} {Σs a' b' refb'} {_} {()}
  transEl {⊥s} {π a' b' refb'} {_} {()}
  transEl {Σs a b refb} {bool} {_} {()}
  transEl {Σs a b refb} {⊥s} {_} {()}
  transEl {Σs a b refb} {Σs a' b' refb'} {bool} {_} {()}
  transEl {Σs a b refb} {Σs a' b' refb'} {⊥s} {_} {()}
  transEl {Σs a b refb} {Σs a' b' refb'} {Σs a'' b'' refb''}{_}{_}{x ,Σ y}{x' ,Σ y'}{x'' ,Σ y''}(x~ ,p y~)(x~' ,p y~') =
    transEl {a} x~ x~' ,p transEl {b x} y~ y~'
  transEl {Σs a b refb} {Σs a' b' refb'} {π a'' b'' refb''} {_} {()}
  transEl {Σs a b refb} {π a' b' refb'} {_} {()}
  transEl {π a b refb} {bool} {_} {()}
  transEl {π a b refb} {⊥s} {_} {()}
  transEl {π a b refb} {Σs a' b' refb'} {_} {()}
  transEl {π a b refb} {π a' b' refb'} {bool} {_} {()}
  transEl {π a b refb} {π a' b' refb'} {⊥s} {_} {()}
  transEl {π a b refb} {π a' b' refb'} {Σs a'' b'' refb''}{_}{()}
  transEl {π a b refb} {π a' b' refb'} {π a'' b'' refb''}{a~ ,p b~}{a~' ,p b~'}{f ,sp reff}{f' ,sp reff'}{f'' ,sp reff''} f~ f~' x x'' x~ =
    let X = f~ x (coeEl a~ x) (mk↑ps (cohEl a~ x)) in
    let Y = f~' (coeEl a~ x) (coeEl a~' (coeEl a~ x)) (mk↑ps (cohEl a~' (coeEl a~ x))) in
    let z = transEl {a~ = symU (transU a~ a~') }{transU a~ a~'}
                    (transEl {a~ = symU a~'} {symU a~} (symEl {a~ = a~'} (cohEl a~' (coeEl a~ x))) (symEl {a~ = a~} (cohEl a~ x))) (un↑ps x~) in
    let Z = reff'' (coeEl a~' (coeEl a~ x)) x'' (mk↑ps z) in
    let XY = transEl {a~ = b~ (cohEl a~ x)}{b~' (cohEl a~' (coeEl a~ x))} X Y in
    transEl {a~ = transU (b~ (cohEl a~ x)) (b~' (cohEl a~' (coeEl a~ x)))} {refb'' z} XY Z
  transEl {ι a} {bool} {c} {()}
  transEl {ι a} {⊥s} {c} {()}
  transEl {ι a} {Σs b b₁ refb} {c} {()}
  transEl {ι a} {π b b₁ refb} {c} {()}
  transEl {ι a} {ι b} {bool} {_} {()}
  transEl {ι a} {ι b} {⊥s} {_} {()}
  transEl {ι a} {ι b} {Σs c b₁ refb} {_} {()}
  transEl {ι a} {ι b} {π c b₁ refb} {_} {()}
  transEl {ι a} {ι b} {ι c} x y = ttp'

  coeEl {bool} {bool} a~ x = x
  coeEl {bool} {⊥s} () x
  coeEl {bool} {Σs a' b' refb'} () x
  coeEl {bool} {π a' b' refb'} () x
  coeEl {⊥s} {bool} () x
  coeEl {⊥s} {⊥s} a~ x = x
  coeEl {⊥s} {Σs a' b refb} () x
  coeEl {⊥s} {π a' b refb} () x
  coeEl {Σs a b refb} {bool} () x
  coeEl {Σs a b refb} {⊥s} () x
  coeEl {Σs a b refb} {Σs a' b' refb'} (a~ ,p b~) (x ,Σ y) = coeEl a~ x ,Σ coeEl (b~ (cohEl a~ x)) y
  coeEl {Σs a b refb} {π a' b' refb'} () x
  coeEl {π a b refb} {bool} () x
  coeEl {π a b refb} {⊥s} () x
  coeEl {π a b refb} {Σs a' b' refb'} () x
  coeEl {π a b refb} {π a' b' refb'} (a~ ,p b~) (f ,sp reff) =
    let F : (x : El a') → El (b' x)
        F = λ x' → coeEl (b~ (symEl {a~ = symU a~} (cohEl (symU a~) x'))) (f (coeEl (symU a~) x'))
        refF : (x x' : El a') (x~ : ↑ps (refU a' ⊢ x ~El x')) → refb' (un↑ps x~) ⊢ F x ~El F x'
        refF = λ x x' x~ →
                 let a~s = symU a~
                     symEla~s = symEl {a~ = a~s}
                     X = cohEl (b~ (symEla~s (cohEl a~s x))) (f (coeEl a~s x))
                     Z = cohEl (b~ (symEla~s (cohEl a~s x'))) (f (coeEl a~s x'))
                     y = transEl {a~ = a~} (symEla~s (cohEl a~s x)) (transEl {a~ = refU a'} (un↑ps x~) (cohEl a~s x'))
                     Y = reff _ _ (mk↑ps y)
                     XY = transEl {a~ = symU (b~ (symEla~s (cohEl a~s x)))} (symEl {a~ = b~ (symEla~s (cohEl a~s x))} X) Y
                 in transEl {a~ = transU (symU (b~ (symEla~s (cohEl a~s x)))) (refb y)} XY Z
    in F ,sp refF
  coeEl {ι a} {bool} x = ⊥pelim' x
  coeEl {ι a} {⊥s} x = ⊥pelim' x
  coeEl {ι a} {Σs b b₁ refb} x = ⊥pelim' x
  coeEl {ι a} {π b b₁ refb} x = ⊥pelim' x
  coeEl {ι a} {ι b} fg (mk↑ps x) = mk↑ps (proj₁p (un↑pl fg) x)

  cohEl {bool} {bool} a~ x = ref𝟚 x
  cohEl {bool} {⊥s} ()
  cohEl {bool} {Σs a' b' refb'} ()
  cohEl {bool} {π a' b' refb'} ()
  cohEl {⊥s} {bool} ()
  cohEl {⊥s} {⊥s} a~ x = ttp
  cohEl {⊥s} {Σs a' b' refb'} ()
  cohEl {⊥s} {π a' b' refb'} ()
  cohEl {Σs a b refb} {bool} ()
  cohEl {Σs a b refb} {⊥s} ()
  cohEl {Σs a b refb} {Σs a' b' refb'}(a~ ,p b~)(x ,Σ y) = cohEl a~ x ,p cohEl (b~ (cohEl a~ x)) y
  cohEl {Σs a b refb} {π a' b' refb'} ()
  cohEl {π a b refb} {bool} ()
  cohEl {π a b refb} {⊥s} ()
  cohEl {π a b refb} {Σs a' b' refb'} ()
  cohEl {π a b refb} {π a' b' refb'}(a~ ,p b~)(f ,sp reff) x x' x~ =
    let a~s = symU a~
        xx = transEl {a~ = a~} (un↑ps x~) (cohEl a~s x')
        X = reff _ _ (mk↑ps xx)
        Y = cohEl (b~ (symEl {a~ = a~s} (cohEl a~s x'))) (f (coeEl a~s x'))
    in transEl {a~ = refb xx} X Y
  cohEl {ι a} {bool} ()
  cohEl {ι a} {⊥s} ()
  cohEl {ι a} {Σs b b₁ refb} ()
  cohEl {ι a} {π b b₁ refb} ()
  cohEl {ι a} {ι b} (mk↑pl (f ,p g)) x = ttp'



-- the actual definition of the universe

U : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
∣ U ∣T γ = IR.U
_T_⊢_~_ U _ = IR._~U_
refT U = IR.refU
symT U = IR.symU
transT U = IR.transU
coeT U _ a = a
cohT U _ = IR.refU

El : ∀{i}{Γ : Con i} → Tm Γ U → Ty Γ lzero
∣ El a ∣T γ = IR.El (∣ a ∣t γ)
_T_⊢_~_ (El a) γ₀₁ = IR._⊢_~El_ (~t a γ₀₁)
refT (El a) {γ} = IR.refEl {∣ a ∣t γ}
symT (El a) {_}{_}{γ₀₁} = IR.symEl {a~ = ~t a γ₀₁}
transT (El a) {_}{_}{_}{γ₀₁}{γ₁₂} = IR.transEl {a~ = ~t a γ₀₁}{~t a γ₁₂}
coeT (El a) γ₀₁ = IR.coeEl (~t a γ₀₁)
cohT (El a) γ₀₁ = IR.cohEl (~t a γ₀₁)


data _≡_ {ℓ}{A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≡ x
infix 8 _≡_

U[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ} → (U [ σ ]T) ≡ U
U[] = refl

El[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ}{a : Tm Δ U}
     → (El a [ σ ]T) ≡ (El (a [ σ ]t))
El[] = refl


open import Setoid.Bool

bool : ∀{i}{Γ : Con i} → Tm Γ U
∣ bool ∣t γ = IR.bool
~t bool γ₀₁ = ttp'

bool[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ} → (bool [ σ ]t) ≡ bool
bool[] = refl

Elbool : ∀{i}{Γ} → El bool ≡ Bool {i}{Γ}
Elbool = refl

open import Setoid.Pi

π : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
∣ π {Γ = Γ} Â B̂ ∣t γ = IR.π (∣ Â ∣t γ) (λ x → ∣ B̂ ∣t (γ ,Σ x)) (λ x~ → ~t B̂ (refC Γ γ ,p x~))
~t (π {Γ = Γ} Â B̂) γ₀₁ = (~t Â γ₀₁) ,p (λ x~ → ~t B̂ (γ₀₁ ,p x~))

π[] : ∀{i j}{Γ Δ}{σ : Tms {i}{j} Γ Δ}{a : Tm Δ U}{b : Tm (Δ ▷ El a) U}
    → ((π a b) [ σ ]t) ≡ π (a [ σ ]t) (b [ _,_ (σ ∘ π₁ {A = (El a) [ σ ]T} id) {A = El a} (π₂ {A = (El a) [ σ ]T} id)  ]t) -- (b [ σ ^ El a ]t)
π[] = refl

Elπ : ∀{i Γ}(a : Tm Γ U)(b : Tm (Γ ▷ El {i} a) U) → El (π a b) ≡ Π (El a) (El b)
Elπ a b = refl

open import Setoid.Props

ι : ∀{i}{Γ : Con i} → Tm Γ (P lzero) → Tm Γ U
∣ ι {Γ} a ∣t γ = IR.ι (∣ a ∣t γ)
~t (ι {Γ} a) γ₀₁ with ~t a γ₀₁
~t (ι {Γ} a) γ₀₁ | mk↑pl (f ,p g) = mk↑pl ((λ x → f (mk↑ps x)) ,p (λ x → g (mk↑ps x)))

ι[] : ∀{i j}{Γ Θ}{σ : Tms {i}{j} Γ Θ}(t : Tm Θ (P lzero)) → ((ι t) [ σ ]t) ≡ (ι (t [ σ ]t))
ι[] t = refl

Elι : ∀{i}{Γ : Con i}(a : Tm Γ (P lzero)) → El (ι a) ≡  ElP a
Elι a = refl
