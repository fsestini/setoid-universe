{-# OPTIONS --without-K --prop #-}

module Setoid.Id where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(a : Tm Γ A) where

  Id : Ty (Γ ▷ A) (i ⊔ j)
  ∣ Id ∣T (_ ,Σ α) = ∣Id∣ A a α
  Id T (γ₀₁ ,p α₀₁) ⊢ p₀ ~ p₁ = Id~ A a α₀₁ p₀ p₁
  refT   Id = refId
  symT   Id = symId
  transT Id = transId
  coeT   Id (_ ,p α₀₁) = coeId α₀₁
  cohT   Id (_ ,p α₀₁) = cohId α₀₁

  idp : Tm Γ (Id [ _,_ id {A = A} a ]T)
  ∣ idp ∣t γ = ∣idp∣
  ~t idp γ~ = idp~

  module _ {k}(Id' : Ty (Γ ▷ A) k)(idp' : Tm Γ (Id' [ _,_ id {A = A} a ]T)) where

    ∣recId∣ : ∀{γ}{α : ∣ A ∣T γ} → ∣Id∣ A a α → ∣ Id' ∣T (_ ,Σ α)
    ∣recId∣ {γ} ∣idp∣ = ∣ idp' ∣t γ
    ∣recId∣ (coeId {_}{_}{γ~} α~ p) = coeT Id' (γ~ ,p α~) (∣recId∣ p)

    recId~ : ∀{γ₀ γ₁}{γ₀₁ : Γ C γ₀ ~ γ₁}{α₀ α₁}{α₀₁ : A T γ₀₁ ⊢ α₀ ~ α₁}{p₀ p₁} →
      Id~ A a α₀₁ p₀ p₁ → Id' T _ ,p α₀₁ ⊢ ∣recId∣ p₀ ~ ∣recId∣ p₁
    recId~ {γ₀₁ = γ₀₁} idp~ = ~t idp' γ₀₁
    recId~ (refId _) = refT Id' _
    recId~ (symId p~) = symT Id' (recId~ p~)
    recId~ (transId p~ p~') = transT Id' (recId~ p~) (recId~ p~')
    recId~ (cohId α₀₁ p~) = cohT Id' _ (∣recId∣ p~)

    recId : Tm (Γ ▷ A ▷ Id) (Id' [ π₁ {A = Id} id ]T)
    ∣ recId ∣t (_ ,Σ αs)   = ∣recId∣ αs
    ~t recId   (_ ,p p₀₁) = recId~  p₀₁
