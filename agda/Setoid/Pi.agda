{-# OPTIONS --without-K --prop #-}

module Setoid.Pi where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

module _ {i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k) where
  ∣Π∣ : ∣ Γ ∣C → Set (j ⊔ k)
  ∣Π∣ γ = Σsp ((α : ∣ A ∣T γ) → ∣ B ∣T (γ ,Σ α)) λ f →
              (α α' : ∣ A ∣T γ)(α~ : ↑ps (A T refC Γ γ ⊢ α ~ α')) → B T refC Γ γ ,p un↑ps α~ ⊢ f α ~ f α'

  Π : Ty Γ (j ⊔ k)
  Π = mkTy {Γ = Γ}{j ⊔ k}
    ∣Π∣
    (λ {γ}{γ'} γ~ f f' → (α : ∣ A ∣T γ)(α' : ∣ A ∣T γ')(α~ : ↑ps (A T γ~ ⊢ α ~ α')) → B T γ~ ,p un↑ps α~ ⊢ proj₁sp f α ~ proj₁sp f' α')
    proj₂sp
    (λ f~ _ _ α~ → symT B (f~ _ _ (mk↑ps (symT A (un↑ps α~)))))
    (λ {_}{_}{_}{γ~} f~ f~' α α' α~ → transT B (f~ _ _ (mk↑ps (cohT A γ~ α))) (f~' _ _ (mk↑ps (transT A (symT A (cohT A γ~ α)) (un↑ps α~)))))
    (λ γ~ f → (λ α' → coeT B (γ~ ,p cohT* A γ~ α') (proj₁sp f (coeT A (symC Γ γ~) α'))) ,sp
              λ  α α' α~ → transT3 B
                                   (symT B (cohT B (γ~ ,p cohT* A γ~ α) (proj₁sp f (coeT* A γ~ α))))
                                   (proj₂sp f _ _ (mk↑ps (transT A (cohT* A γ~ α) (transT A (un↑ps α~) (cohT A (symC Γ γ~) α')))))
                                   (cohT B (γ~ ,p cohT* A γ~ α') (proj₁sp f (coeT* A γ~ α'))))
    (λ {γ}{γ'} γ~ f α α' α~ → transT B (proj₂sp f _ _ (mk↑ps (transT A (un↑ps α~) (cohT A (symC Γ γ~) α')))) (cohT B (γ~ ,p cohT* A γ~ α') (proj₁sp f (coeT A (symC Γ γ~) α'))))

lam : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam {Γ = Γ} t = record { ∣_∣t = λ γ → (λ α → ∣ t ∣t (γ ,Σ α)) ,sp λ _ _ α~ → ~t t (refC Γ γ ,p un↑ps α~) ; ~t = λ γ~ _ _ α~ → ~t t (γ~ ,p un↑ps α~) }

app : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k} → Tm Γ (Π A B) → Tm (Γ ▷ A) B
app t = record { ∣_∣t = λ { (γ ,Σ α) → proj₁sp (∣ t ∣t γ) α } ; ~t = λ { (γ~ ,p α~) → ~t t γ~ _ _ (mk↑ps α~) } }
