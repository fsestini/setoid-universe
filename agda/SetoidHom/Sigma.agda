{-# OPTIONS --without-K --prop #-}

module SetoidHom.Sigma where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF

module _ {i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k) where

  Σ' : Ty Γ (j ⊔ k)
  ∣ EL Σ' γ ∣C = Σ (∣ A ∣T γ) (λ α → ∣ B ∣T (γ ,Σ α))
  EL Σ' γ ⊢ (a ,Σ b) ~ (a' ,Σ b') = Σp (EL A γ ⊢ a ~ a') (λ p → EL B (γ ,Σ a') ⊢ ∣ subst B (refC Γ γ ,p transC (EL A γ) (~s (subst A _) p) (subst-ref A _)) ∣s b ~ b')
  refC (EL Σ' γ) (a ,Σ b) = refC (EL A γ) a ,p subst-ref B _
  symC (EL Σ' γ) {a ,Σ b} {a' ,Σ b'} (a~ ,p b~) = symC (EL A γ) a~ ,p
                          transC3 (EL B _) (symC (EL B (γ ,Σ a)) (~s (subst B (refC Γ _ ,p transC (EL A γ) (subst-ref A _) (symC (EL A _) a~))) b~))
                                           (symC (EL B (γ ,Σ a)) (subst-trans B _ _ _))
                                           (subst-ref B _)
  transC (EL Σ' γ) (a~ ,p b~) (a~' ,p b~') = (transC (EL A γ) a~ a~') ,p transC3 (EL B _) (subst-trans B _ _ _) (~s (subst B _) b~) b~'
  ∣ subst Σ' γ~ ∣s (a ,Σ b) = (∣ subst A γ~ ∣s a) ,Σ ∣ subst B (γ~ ,p (refC (EL A _) _)) ∣s b
  ~s (subst Σ' γ~) (a~ ,p b~) = ~s (subst A γ~) a~ ,p
                                transC3 (EL B _) (symC (EL B _) (subst-trans B _ _ _)) (subst-trans B _ _ _) (~s (subst B (γ~ ,p refC (EL A _) _)) b~)
  subst-ref Σ' (a ,Σ b) = subst-ref A a ,p transC (EL B _) (symC (EL B _) (subst-trans B _ _ _)) (subst-ref B _)
  subst-trans Σ' γ~ γ~' (a ,Σ b) = subst-trans A γ~ γ~' a ,p transC (EL B _) (symC (EL B _) (subst-trans B _ _ _)) (subst-trans B _ _ _)

_,Σ'_ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}(u : Tm Γ A)(v : Tm Γ (B [ _,_ id {A = A} u ]T)) → Tm Γ (Σ' A B)
∣ u ,Σ' v ∣t γ = ∣ u ∣t γ ,Σ ∣ v ∣t γ
~t (_,Σ'_ {B = B} u v) γ~ = ~t u γ~ ,p transC (EL B _) (symC (EL B _) (subst-trans B _ _ _)) (~t v γ~)

pr₁ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k} → Tm Γ (Σ' A B) → Tm Γ A
∣ pr₁ t ∣t γ = proj₁ (∣ t ∣t γ)
~t (pr₁ t) γ~ = proj₁p (~t t γ~)

pr₂ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▷ A) k}(t : Tm Γ (Σ' A B)) → Tm Γ (B [ _,_ id {A = A} (pr₁ {A = A}{B} t) ]T)
∣ pr₂ t ∣t γ = proj₂ (∣ t ∣t γ)
~t (pr₂ {B = B} t) γ~ = transC (EL B _) (subst-trans B _ _ _) (proj₂p (~t t γ~))
