{-# OPTIONS --without-K --prop #-}

module SetoidRed.CwF where

open import Agda.Primitive
open import SetoidRed.lib

infixl 5 _▷_
infixl 7 _[_]T
infixl 5 _,_
infixr 6 _∘_
infixl 8 _[_]t

Con = Setoid
Tms = SetoidMor
Ty  = SetoidFam
Tm  = SetoidSec

coeT* : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → ∣ A ∣T γ' → ∣ A ∣T γ
coeT* {_}{Γ} A γ~ α' = coeT A (symC Γ γ~) α'

cohT* : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){γ γ' : ∣ Γ ∣C}(γ~ : Γ C γ ~ γ')(α' : ∣ A ∣T γ') → A T γ~ ⊢ coeT* A γ~ α' ~ α'
cohT* {_}{Γ} A γ~ α' = symT A (cohT A (symC Γ γ~) α')

transC3 : ∀{i}(Γ : Con i){γ γ' γ'' γ''' : ∣ Γ ∣C} → Γ C γ ~ γ' → Γ C γ' ~ γ'' → Γ C γ'' ~ γ''' → Γ C γ ~ γ'''
transC3 Γ γ~ γ~' γ~'' = transC Γ γ~ (transC Γ γ~' γ~'')

transT3 : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){γ γ' γ'' γ''' : ∣ Γ ∣C}
  {γ~ : Γ C γ ~ γ'}{γ~' : Γ C γ' ~ γ''}{γ~'' : Γ C γ'' ~ γ'''}
  {α : ∣ A ∣T γ}{α' : ∣ A ∣T γ'}{α'' : ∣ A ∣T γ''}{α''' : ∣ A ∣T γ'''}
  (α~ : A T γ~ ⊢ α ~ α')(α~' : A T γ~' ⊢ α' ~ α'')(α~'' : A T γ~'' ⊢ α'' ~ α''')
  → A T transC3 Γ γ~ γ~' γ~'' ⊢ α ~ α'''
transT3 A α~ α~' α~'' = transT A α~ (transT A α~' α~'')

coeR~ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){γ : ∣ Γ ∣C}(α : ∣ A ∣T γ) → A T refC Γ γ ⊢ coeT A (refC Γ γ) α ~ α
coeR~ A α = symT A (cohT A _ α)

coeTr~ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){γ₀ γ₁ γ₂ : ∣ Γ ∣C}(γ₀₁ : Γ C γ₀ ~ γ₁)(γ₁₂ : Γ C γ₁ ~ γ₂)(α₀ : ∣ A ∣T γ₀) →
  A T refC Γ γ₂ ⊢ coeT A (transC Γ γ₀₁ γ₁₂) α₀ ~ coeT A γ₁₂ (coeT A γ₀₁ α₀)
coeTr~ {Γ = Γ} A γ₀₁ γ₁₂ α₀ = transT3 A
  (symT A (cohT A (transC Γ γ₀₁ γ₁₂) α₀))
  (cohT A γ₀₁ α₀)
  (cohT A γ₁₂ (coeT A γ₀₁ α₀))

• : Con lzero
∣ • ∣C = ⊤
• C _ ~ _ = ⊤p
refC • _ = ttp
symC • _ = ttp
transC • _ _ = ttp

_▷_ : ∀{i}(Γ : Con i){j} → Ty Γ j → Con (i ⊔ j)
_▷_ Γ A = record
  { ∣_∣C   = Σ ∣ Γ ∣C ∣ A ∣T_
  ; _C_~_  = λ { (γ ,Σ α)(γ' ,Σ α') → Σp (Γ C γ ~ γ') (A T_⊢ α ~ α') }
  ; refC   = λ { (γ ,Σ α) → refC Γ γ ,p refT A α }
  ; symC   = λ { {γ ,Σ α}{γ' ,Σ α'} e → symC Γ (proj₁p {A = Γ C γ ~ γ'}{A T_⊢ α ~ α'} e) ,p symT A (proj₂p {A = Γ C γ ~ γ'}{A T_⊢ α ~ α'} e) }
  ; transC = λ { {γ ,Σ α}{γ' ,Σ α'}{γ'' ,Σ α''} e e' → transC Γ (proj₁p {A = Γ C γ ~ γ'}{A T_⊢ α ~ α'} e) (proj₁p {A = Γ C γ' ~ γ''}{A T_⊢ α' ~ α''} e') ,p transT A (proj₂p {A = Γ C γ ~ γ'}{A T_⊢ α ~ α'} e) (proj₂p {A = Γ C γ' ~ γ''}{A T_⊢ α' ~ α''} e') }
  }

_[_]T : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k} → Ty Δ k → Tms Γ Δ → Ty Γ k
A [ σ ]T = record
  { ∣_∣T_   = λ γ → ∣ A ∣T (∣ σ ∣s γ)
  ; _T_⊢_~_ = λ p α α' → A T ~s σ p ⊢ α ~ α'
  ; refT    = refT A
  ; symT    = symT A
  ; transT  = transT A
  ; coeT    = λ p → coeT A (~s σ p)
  ; cohT    = λ p → cohT A (~s σ p)
  }

id : ∀{i}{Γ : Con i} → Tms Γ Γ
id = record
  { ∣_∣s = λ γ → γ
  ; ~s   = λ p → p
  }

_∘_ : ∀{i}{Γ : Con i}{j}{Θ : Con j}{k}{Δ : Con k} → Tms Θ Δ → Tms Γ Θ → Tms Γ Δ
σ ∘ ν = record
  { ∣_∣s = λ γ → ∣ σ ∣s (∣ ν ∣s γ)
  ; ~s   = λ p → ~s σ (~s ν p)
  }

ε : ∀{i}{Γ : Con i} → Tms Γ •
∣ ε ∣s _ = tt
~s ε _ = ttp

_,_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Tms Γ Δ){b}{A : Ty Δ b} → Tm Γ (A [ σ ]T) → Tms Γ (Δ ▷ A)
σ , t = record { ∣_∣s = λ γ → ∣ σ ∣s γ ,Σ ∣ t ∣t γ ; ~s = λ p → ~s σ p ,p ~t t p }

π₁ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k} → Tms Γ (Δ ▷ A) →  Tms Γ Δ
π₁ {Δ = Δ}{A = A} σ = record {
  ∣_∣s = λ γ → proj₁ (∣ σ ∣s γ) ;
  ~s = λ {γ}{γ'} p → proj₁p {A = Δ C proj₁ (∣ σ ∣s γ) ~ proj₁ (∣ σ ∣s γ')}{B = A T_⊢ proj₂ (∣ σ ∣s γ) ~ proj₂ (∣ σ ∣s γ')} (~s σ p) }

_[_]t : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k} → Tm Δ A → (σ : Tms Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ]t = record { ∣_∣t = λ γ → ∣ t ∣t (∣ σ ∣s γ) ; ~t = λ p → ~t t (~s σ p) }

π₂ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{A : Ty Δ k}(σ : Tms Γ (Δ ▷ A)) → Tm Γ (A [ π₁ {A = A} σ ]T)
π₂ {Δ = Δ}{A = A} σ = record {
  ∣_∣t = λ γ → proj₂ (∣ σ ∣s γ) ;
  ~t = λ {γ}{γ'} p → proj₂p  {A = Δ C proj₁ (∣ σ ∣s γ) ~ proj₁ (∣ σ ∣s γ')}{B = A T_⊢ proj₂ (∣ σ ∣s γ) ~ proj₂ (∣ σ ∣s γ')} (~s σ p) }
