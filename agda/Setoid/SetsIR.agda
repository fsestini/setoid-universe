{-# OPTIONS --without-K --prop #-}

module Setoid.SetsIR where

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
  Σs a b refb ~U Σs a' b' refb' = Σp (a ~U a') λ a~ → (x : El a)(x' : El a')(x~ : ↑ps (a~ ⊢ x ~El x')) → b x ~U b' x'
  π  a b refb ~U π  a' b' refb' = Σp (a ~U a') λ a~ → (x : El a)(x' : El a')(x~ : ↑ps (a~ ⊢ x ~El x')) → b x ~U b' x'
  ι a ~U ι b = ↑pl ((↑ps a → b) ×p (↑ps b → a))
  _ ~U _ = ⊥p'

  refU bool = ttp'
  refU ⊥s = ttp'
  refU (Σs a b refb) = refU a ,p λ _ _ x~ → refb (un↑ps x~)
  refU (π a b refb) = refU a ,p λ _ _ x~ → refb (un↑ps x~)
  refU (ι a) = mk↑pl ((λ x → un↑ps x) ,p (λ x → un↑ps x))

  El bool = 𝟚
  El ⊥s = ⊥
  El (Σs a b refb) = Σ (El a) λ x → El (b x)
  El (π a b refb) = Σsp ((x : El a) → El (b x)) λ f → (x x' : El a)(x~ : ↑ps (refU a ⊢ x ~El x')) → refb (un↑ps x~) ⊢ f x ~El f x'
  El (ι a) = ↑ps a

  _⊢_~El_ {bool} {bool} a~ x₀ x₁ = x₀ ≟𝟚 x₁
  _⊢_~El_ {⊥s} {⊥s} a~ x x' = ⊤p
  _⊢_~El_ {Σs a b refb} {Σs a' b' refb'} w~ (x ,Σ y) (x' ,Σ y') = Σp (proj₁p w~ ⊢ x ~El x') λ x~ → proj₂p w~ _ _ (mk↑ps x~) ⊢ y ~El y'
  _⊢_~El_ {π a b refb} {π a' b' refb'} w~ (f ,sp _) (f' ,sp _)
    = (x : El a)(x' : El a')(x~ : ↑ps (proj₁p w~ ⊢ x ~El x'))
    → proj₂p w~ _ _ x~ ⊢ f x ~El f' x'
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
  symU {⊥s} {⊥s} a~ = ttp'
  symU {Σs a b refb} {Σs a' b' refb'}(a~ ,p b~) = symU a~ ,p λ _ _ x~ → symU (b~ _ _ (mk↑ps (symEl {a~ = symU a~} (un↑ps x~))))
  symU {π a b refb} {π a' b' refb'}(a~ ,p b~) =
    symU a~ ,p λ _ _ x~ → symU (b~ _ _ (mk↑ps (symEl {a~ = symU a~} (un↑ps x~))))
  symU {ι a} {ι x₁} (mk↑pl (f ,p g)) = mk↑pl (g ,p f)

  symEl {bool} {bool} {a~} {x} {x'} x~ = sym𝟚 {x} {x'} x~
  symEl {⊥s} {⊥s} {a~} {x} {x'} x~ = ttp
  symEl {Σs a b refb} {Σs a' b' refb'} {w~} {x ,Σ y} {x' ,Σ y'}(x~ ,p y~) = symEl {a} x~ ,p symEl {b x} y~
  symEl {π a b refb} {π a' b' refb'} {w~} {f ,sp _} {f' ,sp _} f~ x x' x~ =
    symEl {b x'} (f~ _ _ (mk↑ps (symEl {a'} (un↑ps x~))))
  symEl {ι a} {ι b} x = x

  transU : {a a' a'' : U}(a~ : a ~U a')(a~' : a' ~U a'') → a ~U a''
  transEl : {a a' a'' : U}{a~ : a ~U a'}{a~' : a' ~U a''}{x : El a}{x' : El a'}{x'' : El a''}
    (x~ : a~ ⊢ x ~El x')(x~' : a~' ⊢ x' ~El x'') → transU a~ a~' ⊢ x ~El x''
  coeEl : {a a' : U}(a~ : a ~U a') → El a → El a'
  cohEl : {a a' : U}(a~ : a ~U a')(x : El a) → a~ ⊢ x ~El coeEl a~ x

  transU {bool} {bool} {bool} a~ a~' = ttp'
  transU {⊥s} {⊥s} {⊥s} a~ a~' = ttp'
  transU {Σs a b refb} {Σs a' b' refb'} {Σs a'' b'' refb''} (a~ ,p b~) (a~' ,p b~') =
    transU a~ a~' ,p
    λ x x'' x~ → transU (b~ _ _ (mk↑ps (cohEl a~ x))) (transU
                        (refb' (transEl {a~ = symU a~} (symEl {a~ = a~} (cohEl a~ x)) (transEl {a~ = transU a~ a~'} (un↑ps x~) (cohEl (symU a~') x''))))
                        (b~' _ _ (mk↑ps (symEl {a~ = symU a~'} (cohEl (symU a~') x'')))))
  transU {π a b refb} {π a' b' refb'} {π a'' b'' refb''} (a~ ,p b~) (a~' ,p b~') =
    transU a~ a~' ,p
    λ x x'' x~ → transU (b~ _ _ (mk↑ps (cohEl a~ x))) (transU
                        (refb' (transEl {a~ = symU a~} (symEl {a~ = a~} (cohEl a~ x)) (transEl {a~ = transU a~ a~'} (un↑ps x~) (cohEl (symU a~') x'')) ))
                        (b~' _ _ (mk↑ps (symEl {a~ = symU a~'} (cohEl (symU a~') x'')))))
  transU {ι a} {ι b} {ι c} (mk↑pl (f ,p g)) (mk↑pl (f' ,p g')) = mk↑pl ((λ x → f' (mk↑ps (f x))) ,p (λ y → g (mk↑ps (g' y))))

  transEl {bool} {bool} {bool} {_} {_} {x} {x'} {x''} x~ x~' = trans𝟚 {x} {x'} {x''} x~ x~'
  transEl {⊥s} {⊥s} {⊥s} {_} {_} {x} {x'} {x''} x~ x~' = ttp
  transEl {Σs a b refb} {Σs a' b' refb'} {Σs a'' b'' refb''}{_}{_}{x ,Σ y}{x' ,Σ y'}{x'' ,Σ y''}(x~ ,p y~)(x~' ,p y~') =
    transEl {a} x~ x~' ,p transEl {b x} y~ y~'
  transEl {π a b refb} {π a' b' refb'} {π a'' b'' refb''}{a~ ,p b~}{a~' ,p b~'}{f ,sp reff}{f' ,sp reff'}{f'' ,sp reff''} f~ f~' x x'' x~ =
    let X = f~ x (coeEl a~ x) (mk↑ps (cohEl a~ x)) in
    let Y = f~' (coeEl a~ x) (coeEl a~' (coeEl a~ x)) (mk↑ps (cohEl a~' (coeEl a~ x))) in
    let z = transEl {a~ = symU (transU a~ a~') }{transU a~ a~'}
                    (transEl {a~ = symU a~'} {symU a~} (symEl {a~ = a~'} (cohEl a~' (coeEl a~ x))) (symEl {a~ = a~} (cohEl a~ x))) (un↑ps x~) in
    let Z = reff'' (coeEl a~' (coeEl a~ x)) x'' (mk↑ps z) in
    let XY = transEl {a~ = b~ _ _ (mk↑ps (cohEl a~ x))}{b~' _ _ (mk↑ps (cohEl a~' (coeEl a~ x)))} X Y in
    transEl {a~ = transU (b~ _ _ (mk↑ps (cohEl a~ x))) (b~' _ _ (mk↑ps (cohEl a~' (coeEl a~ x))))} {refb'' z} XY Z
  transEl {ι a} {ι b} {ι c} x y = ttp'

  coeEl {bool} {bool} a~ x = x
  coeEl {Σs a b refb} {Σs a' b' refb'} (a~ ,p b~) (x ,Σ y) = coeEl a~ x ,Σ coeEl (b~ _ _ (mk↑ps (cohEl a~ x))) y
  coeEl {π a b refb} {π a' b' refb'} (a~ ,p b~) (f ,sp reff) =
    let F : (x : El a') → El (b' x)
        F = λ x' → coeEl (b~ _ _ (mk↑ps (symEl {a~ = symU a~} (cohEl (symU a~) x')))) (f (coeEl (symU a~) x'))
        refF : (x x' : El a') (x~ : ↑ps (refU a' ⊢ x ~El x')) → refb' (un↑ps x~) ⊢ F x ~El F x'
        refF = λ x x' x~ →
                 let a~s = symU a~
                     symEla~s = symEl {a~ = a~s}
                     X = cohEl (b~ _ _ (mk↑ps (symEla~s (cohEl a~s x)))) (f (coeEl a~s x))
                     Z = cohEl (b~ _ _ (mk↑ps (symEla~s (cohEl a~s x')))) (f (coeEl a~s x'))
                     y = transEl {a~ = a~} (symEla~s (cohEl a~s x)) (transEl {a~ = refU a'} (un↑ps x~) (cohEl a~s x'))
                     Y = reff _ _ (mk↑ps y)
                     XY = transEl {a~ = symU (b~ _ _ (mk↑ps (symEla~s (cohEl a~s x))))} (symEl {a~ = b~ _ _ (mk↑ps (symEla~s (cohEl a~s x)))} X) Y
                 in transEl {a~ = transU (symU (b~ _ _ (mk↑ps (symEla~s (cohEl a~s x))))) (refb y)} XY Z
    in F ,sp refF
  coeEl {ι a} {ι b} fg (mk↑ps x) = mk↑ps (proj₁p (un↑pl fg) (mk↑ps x))
  coeEl {⊥s} {⊥s} p x = x

  cohEl {bool} {bool} a~ x = ref𝟚 x
  cohEl {Σs a b refb} {Σs a' b' refb'}(a~ ,p b~)(x ,Σ y) = cohEl a~ x ,p cohEl (b~ _ _ (mk↑ps (cohEl a~ x))) y
  cohEl {π a b refb} {π a' b' refb'}(a~ ,p b~)(f ,sp reff) x x' x~ =
    let a~s = symU a~
        xx = transEl {a~ = a~} (un↑ps x~) (cohEl a~s x')
        X = reff _ _ (mk↑ps xx)
        Y = cohEl (b~ _ _ (mk↑ps (symEl {a~ = a~s} (cohEl a~s x')))) (f (coeEl a~s x'))
    in transEl {a~ = refb xx} X Y
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

bool : ∀{i}{Γ : Con i} → Tm Γ U
∣ bool ∣t γ = IR.bool
~t bool γ₀₁ = ttp'

⊥̂ : ∀{i}{Γ : Con i} → Tm Γ U
∣ ⊥̂ ∣t γ = IR.⊥s
~t ⊥̂ γ₀₁ = ttp'

π : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
∣ π {Γ = Γ} Â B̂ ∣t γ = IR.π (∣ Â ∣t γ) (λ x → ∣ B̂ ∣t (γ ,Σ x)) (λ x~ → ~t B̂ (refC Γ γ ,p x~))
~t (π {Γ = Γ} Â B̂) γ₀₁ = ~t Â γ₀₁ ,p λ _ _ x~ → ~t B̂ (γ₀₁ ,p un↑ps x~)

Σ̂ : ∀{i Γ}(Â : Tm Γ U)(B̂ : Tm (Γ ▷ El {i} Â) U) → Tm Γ U
∣ Σ̂ {Γ = Γ} Â B̂ ∣t γ = IR.Σs (∣ Â ∣t γ) (λ x → ∣ B̂ ∣t (γ ,Σ x)) λ x~ → ~t B̂ (refC Γ γ ,p x~)
~t (Σ̂ {Γ = Γ} Â B̂) γ₀₁ = ~t Â γ₀₁ ,p λ _ _ x~ → ~t B̂ (γ₀₁ ,p un↑ps x~)

open import Setoid.Props

ι : ∀{i}{Γ : Con i} → Tm Γ (P lzero) → Tm Γ U
∣ ι {Γ} a ∣t γ = IR.ι (∣ a ∣t γ)
~t (ι {Γ} a) γ₀₁ = ~t a γ₀₁
