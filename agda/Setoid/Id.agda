{-# OPTIONS --without-K --prop #-}

module Setoid.Id where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.CwF

module _ {i}(A : Ty • i)(a : Tm • A) where

  data ∣Id∣ : ∣ A ∣T tt → Set i where
    idp : ∣Id∣ (∣ a ∣t tt)
    coe : ∀{α α'} → A T ttp ⊢ α ~ α' → ∣Id∣ α → ∣Id∣ α'

  Id : Ty (• ▷ A) i
  ∣ Id ∣T (_ ,Σ α) = ∣Id∣ α
  Id T γ~ ⊢ α ~ α' = ↑pl ⊤p
  refT Id _ = mk↑pl ttp
  symT Id _ = mk↑pl ttp
  transT Id _ _ = mk↑pl ttp
  coeT Id {_ ,Σ α}{_ ,Σ α'} (ttp ,p α~) e = coe α~ e
  cohT Id _ _ = mk↑pl ttp

  transport : ∀{j}(P : Ty (• ▷ A) j){α : ∣ A ∣T tt}(e : ∣Id∣ α) →
    ∣ P ∣T (tt ,Σ ∣ a ∣t tt) → ∣ P ∣T (tt ,Σ α)
  transport P idp u = u
  transport P {α'} (coe {α} α~ e) u = coeT P (ttp ,p transT A {!!} α~) u

  transp : ∀{j}(P : Ty (• ▷ A) j){a' : Tm • A}(e : Tm • (Id [ _,_ ε {A = A} a' ]T)) →
    Tm • (P [ _,_ ε {A = A} a ]T) → Tm • (P [ _,_ ε {A = A} a' ]T)
  ∣ transp P e u ∣t γ = coeT P (ttp ,p {!!}) (∣ u ∣t γ)
  ~t (transp P e u) _ = {!!}
