{-# OPTIONS --without-K --prop #-}

module SetoidHom.Id where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF
open import SetoidHom.Props
open import lib


module _ {i}{Γ : Con i}{j}(A : Ty Γ j)(u : Tm Γ A) where

  module _ (v : Tm Γ A) where
    Id : Tm Γ (P j)
    ∣ Id ∣t γ = EL A γ ⊢ ∣ u ∣t γ ~ ∣ v ∣t γ
    ~t Id γ~ = mk↑pl ((λ { (mk↑ps uv) → transC3 (EL A _) (symC (EL A _) (~t u γ~)) (~s (subst A γ~) uv) (~t v γ~)})
                      ,p (λ { (mk↑ps uv) → transC3 (EL A _) (symC (EL A _) (~t u (symC Γ γ~))) ((~s (subst A (symC Γ γ~)) uv)) (~t v (symC Γ γ~)) }))

  idp : Tm Γ (ElP (Id u))
  ∣ idp ∣t γ = mk↑ps (refC (EL A _) _)
  ~t idp γ~ = ttp'

  module _ {k}(Id' : Ty (Γ ▷ A) k){v : Tm Γ A}(e : Tm Γ (ElP (Id v)))(idp' : Tm Γ (Id' [ _,_ id {A = A} u ]T)) where

    recId : Tm Γ (Id' [  _,_ id {A = A} v ]T)
    ∣ recId ∣t γ =  ∣ subst Id' (refC Γ γ ,p transC (EL A γ) (subst-ref A _) (un↑ps (∣ e ∣t γ))) ∣s (∣ idp' ∣t γ)
    ~t recId γ~ = transC3 (EL Id' _) (symC (EL Id' _) (subst-trans Id' _ _ _))
                                     (subst-trans Id' _ _ _)
                                     (~s (subst Id' _) (~t idp' γ~))

-- weak β rule
recIdβ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j)(u : Tm Γ A){k}(Id' : Ty (Γ ▷ A) k)(idp' : Tm Γ (Id' [ _,_ id {A = A} u ]T))
         → Tm Γ (ElP (Id _ (recId A u Id' {u} (idp A u) idp') idp'))
∣ recIdβ A u Id' idp' ∣t γ = mk↑ps (subst-ref Id' _)
~t (recIdβ A u Id' idp') _ = ttp'
