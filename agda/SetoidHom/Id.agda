{-# OPTIONS --without-K --prop #-}

module SetoidHom.Id where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF
open import lib

record Liftp {ℓ}(A : Prop ℓ) : Set ℓ where
  constructor liftp
  field
    unliftp : A
open Liftp public

record LiftP {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor liftP
  field
    unliftP : A
open LiftP public

⊤p' : ∀{ℓ} → Prop ℓ
⊤p' = LiftP ⊤p

ttp' : ∀{ℓ} → ⊤p' {ℓ}
ttp' = liftP ttp


module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(u : Tm Γ A) where

  module _ (v : Tm Γ A) where
    Id : Ty Γ j
    ∣ EL Id γ ∣C = Liftp (EL A γ ⊢ ∣ u ∣t γ ~ ∣ v ∣t γ)
    _⊢_~_ (EL Id γ) _ _ = ⊤p'
    refC (EL Id γ) _ = ttp'
    symC (EL Id γ) _ = ttp'
    transC (EL Id γ) _ _ = ttp'
    ∣ subst Id γ~ ∣s (liftp e) = liftp (transC3 (EL A _) (symC (EL A _) (~t u γ~)) (~s (subst A γ~) e) (~t v γ~))
    ~s (subst Id γ~) _ = ttp'
    subst-ref Id _ = ttp'
    subst-trans Id _ _ _ = ttp'


  idp : Tm Γ (Id u)
  ∣ idp ∣t γ = liftp (refC (EL A _) _)
  ~t idp γ~ = ttp'

  module _ {k}(Id' : Ty (Γ ▷ A) k){v : Tm Γ A}(e : Tm Γ (Id v))(idp' : Tm Γ (Id' [ _,_ id {A = A} u ]T)) where

    recId : Tm Γ (Id' [  _,_ id {A = A} v ]T)
    ∣ recId ∣t γ =  ∣ subst Id' (refC Γ γ ,p transC (EL A γ) (subst-ref A _) (unliftp (∣ e ∣t γ))) ∣s (∣ idp' ∣t γ)
    ~t recId γ~ = transC3 (EL Id' _) (symC (EL Id' _) (subst-trans Id' _ _ _))
                                     (subst-trans Id' _ _ _)
                                     (~s (subst Id' _) (~t idp' γ~))

-- weak β rule
recIdβ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j)(u : Tm Γ A){k}(Id' : Ty (Γ ▷ A) k)(idp' : Tm Γ (Id' [ _,_ id {A = A} u ]T))
         → Tm Γ (Id _ (recId A u Id' {u} (idp A u) idp') idp')
∣ recIdβ A u Id' idp' ∣t γ = liftp (subst-ref Id' _)
~t (recIdβ A u Id' idp') _ = ttp'



-- module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(a : Tm Γ A) where

--   Id : Ty (Γ ▷ A) j
--   ∣ EL Id (γ ,Σ α) ∣C = Liftp (EL A γ ⊢ ∣ a ∣t γ ~ α)
--   _⊢_~_ (EL Id γ) _ _ = ⊤p'
--   refC (EL Id γ) _ = ttp'
--   symC (EL Id γ) _ = ttp'
--   transC (EL Id γ) _ _ = ttp'
--   ∣ subst Id (γ~ ,p a~) ∣s (liftp e) = liftp (transC3 (EL A _) (symC (EL A _) (~t a γ~)) (~s (subst A γ~) e) a~)
--   ~s (subst Id (γ~ ,p a~)) _ = ttp'
--   subst-ref Id _ = ttp'
--   subst-trans Id _ _ _ = ttp'

--   idp : Tm Γ (Id [ _,_ id {A = A} a ]T)
--   ∣ idp ∣t γ = liftp (refC (EL A _) (∣ a ∣t γ))
--   ~t idp γ~ = ttp'

--   module _ {k}(Id' : Ty (Γ ▷ A) k)(idp' : Tm Γ (Id' [ _,_ id {A = A} a ]T)) where

--     recId : Tm (Γ ▷ A ▷ Id) (Id' [ π₁ {A = Id} id ]T)
--     ∣ recId ∣t (γ ,Σ α ,Σ liftp e) = ∣ subst Id' (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ a ∣t γ)) e) ∣s (∣ idp' ∣t γ)
--     ~t recId {γ ,Σ α ,Σ p} {γ' ,Σ α' ,Σ p'} (γ~ ,p α~ ,p _) = transC3 (EL Id' _) (symC (EL Id' _) (subst-trans Id' _ _ _))
--                                                                                  (subst-trans Id' _ _ _)
--                                                                                  (~s (subst Id' _) (~t idp' γ~))
