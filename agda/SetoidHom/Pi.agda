{-# OPTIONS --without-K --prop #-}

module SetoidHom.Pi where

open import Agda.Primitive
open import SetoidHom.lib
open import SetoidHom.CwF

module _ {i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▷ A) k) where
  Π : Ty Γ (j ⊔ k)
  Π = record {
    EL = λ γ → record {
      ∣_∣C = Σsp ((α : ∣ EL A γ ∣C) → ∣ EL B (γ ,Σ α) ∣C) λ f →
                 {α α' : ∣ EL A γ ∣C}(α~ : EL A γ ⊢ α ~ α') → EL B (γ ,Σ α') ⊢ ∣ subst B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) ∣s (f α) ~ f α' ;
      _⊢_~_ = λ { (f ,sp _)(f' ,sp _) → {α α' : ∣ EL A γ ∣C}(α~ : EL A γ ⊢ α ~ α') → EL B (γ ,Σ α') ⊢ ∣ subst B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) ∣s (f α) ~ f' α' } ;
      refC = proj₂sp ;
      symC = λ { {f ,sp reff}{f' ,sp reff'} f~ {α}{α'} α~ → transC (EL B (γ ,Σ α'))
        (~s (subst B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~)) (symC (EL B (γ ,Σ α)) (f~ (symC (EL A γ) α~))))
        (transC (EL B (γ ,Σ α')) (symC (EL B (γ ,Σ α')) (subst-trans B (refC Γ γ ,p transC (EL A γ) (subst-ref A α') (symC (EL A γ) α~)) (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) (f α')))
        (subst-ref B (f α'))) } ;
      transC = λ { {f ,sp reff}{f' ,sp reff'}{f'' ,sp reff''} f~ f~' {α}{α''} α~ → transC (EL B (γ ,Σ α''))
        (~s (subst B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~)) (transC (EL B (γ ,Σ α))
          (symC (EL B (γ ,Σ α)) (subst-ref B {γ ,Σ α} (f α)))
          (f~ (refC (EL A γ) α))))
        (f~' α~) } } ;
    subst = λ {γ}{γ'} γ~ → record {
      ∣_∣s = λ { (f ,sp reff) →
        (λ α' → ∣ subst B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α')) (subst-ref A α')) ∣s (f (∣ subst A (symC Γ γ~) ∣s α'))) ,sp
        λ {α}{α'} α~ → transC (EL B (γ' ,Σ α'))
          (transC (EL B (γ' ,Σ α'))
            (symC (EL B (γ' ,Σ α'))
              (subst-trans B
                (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α)) (subst-ref A α))
                (refC Γ γ' ,p transC (EL A γ') (subst-ref A α) α~)
                (f (∣ subst A (symC Γ γ~) ∣s α))))
            (subst-trans B
              (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ subst A (symC Γ γ~) ∣s α)) (~s (subst A (symC Γ γ~)) α~))
              (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α')) (subst-ref A α'))
              (f (∣ subst A (symC Γ γ~) ∣s α))))
          (~s
            (subst B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α')) (subst-ref A α')))
            (reff (~s (subst A (symC Γ γ~)) α~))) } ;
      ~s = λ { {f ,sp reff}{f' ,sp reff'} f~ {α}{α'} α~ → transC (EL B (γ' ,Σ α')) (transC (EL B (γ' ,Σ α'))
        (symC (EL B (γ' ,Σ α')) (subst-trans B
          (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α)) (subst-ref A α))
          (refC Γ γ' ,p transC (EL A γ') (subst-ref A α) α~)
          (f (∣ subst A (symC Γ γ~) ∣s α))))
        (subst-trans B
          (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ subst A (symC Γ γ~) ∣s α)) (~s (subst A (symC Γ γ~)) α~))
          (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α')) (subst-ref A α'))
          (f (∣ subst A (symC Γ γ~) ∣s α))))
        (~s (subst B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α')) (subst-ref A α'))) (f~ (~s (subst A (symC Γ γ~)) α~))) } } ;
    subst-ref = λ { {γ}(f ,sp reff){α}{α'} α~ → transC (EL B (γ ,Σ α'))
      (symC (EL B (γ ,Σ α')) (subst-trans B (refC Γ γ ,p transC (EL A γ) (symC (EL A γ) (subst-trans A (symC Γ (refC Γ γ)) (refC Γ γ) α)) (subst-ref A α)) (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) (f (∣ subst A (symC Γ (refC Γ γ)) ∣s α)))) (transC (EL B (γ ,Σ α')) (transC (EL B (γ ,Σ α'))
      (subst-trans B (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ subst A (refC Γ γ) ∣s α)) (subst-ref A α)) (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) (f (∣ subst A (refC Γ γ) ∣s α)))
      (~s (subst B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~)) (reff (subst-ref A α))))
      (reff α~)) } ;
    subst-trans = λ { {γ}{γ'}{γ''} γ~ γ~' (f ,sp reff){α}{α''} α~ → transC (EL B (γ'' ,Σ α''))
      (symC (EL B (γ'' ,Σ α'')) (subst-trans B (transC Γ γ~ γ~' ,p transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ (transC Γ γ~ γ~')) (transC Γ γ~ γ~') α)) (subst-ref A α)) (refC Γ γ'' ,p transC (EL A γ'') (subst-ref A α) α~) (f (∣ subst A (symC Γ (transC Γ γ~ γ~')) ∣s α)))) (transC (EL B (γ'' ,Σ α'')) (transC (EL B (γ'' ,Σ α'')) (transC (EL B (γ'' ,Σ α'')) (transC (EL B (γ'' ,Σ α''))
      (subst-trans B (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ subst A (symC Γ (transC Γ γ~ γ~')) ∣s α)) (~s (subst A (symC Γ (transC Γ γ~ γ~'))) α~)) (transC Γ (refC Γ γ) (transC Γ γ~ γ~') ,p transC (EL A γ'') (subst-trans A (refC Γ γ) (transC Γ γ~ γ~') (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α'')) (transC (EL A γ'') (~s (subst A (transC Γ γ~ γ~')) (transC (EL A γ) (subst-ref A (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α'')) (subst-trans A (symC Γ γ~') (symC Γ γ~) α''))) (transC (EL A γ'') (subst-trans A γ~ γ~' (∣ subst A (symC Γ γ~) ∣s (∣ subst A (symC Γ γ~') ∣s α''))) (transC (EL A γ'') (~s (subst A γ~') (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A (symC Γ γ~') ∣s α''))) (subst-ref A (∣ subst A (symC Γ γ~') ∣s α'')))) (transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ γ~') γ~' α'')) (subst-ref A α'')))))) (f (∣ subst A (symC Γ (transC Γ γ~ γ~')) ∣s α)))
      (~s (subst B (transC Γ (refC Γ γ) (transC Γ γ~ γ~') ,p transC (EL A γ'') (subst-trans A (refC Γ γ) (transC Γ γ~ γ~') (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α'')) (transC (EL A γ'') (~s (subst A (transC Γ γ~ γ~')) (transC (EL A γ) (subst-ref A (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α'')) (subst-trans A (symC Γ γ~') (symC Γ γ~) α''))) (transC (EL A γ'') (subst-trans A γ~ γ~' (∣ subst A (symC Γ γ~) ∣s (∣ subst A (symC Γ γ~') ∣s α''))) (transC (EL A γ'') (~s (subst A γ~') (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A (symC Γ γ~') ∣s α''))) (subst-ref A (∣ subst A (symC Γ γ~') ∣s α'')))) (transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ γ~') γ~' α'')) (subst-ref A α''))))))) (reff (~s (subst A (symC Γ (transC Γ γ~ γ~'))) α~))))
      (subst-trans B (refC Γ γ ,p transC (EL A γ) (subst-ref A (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α'')) (subst-trans A (symC Γ γ~') (symC Γ γ~) α'')) (transC Γ γ~ γ~' ,p transC (EL A γ'') (subst-trans A γ~ γ~' (∣ subst A (symC Γ γ~) ∣s (∣ subst A (symC Γ γ~') ∣s α''))) (transC (EL A γ'') (~s (subst A γ~') (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A (symC Γ γ~') ∣s α''))) (subst-ref A (∣ subst A (symC Γ γ~') ∣s α'')))) (transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ γ~') γ~' α'')) (subst-ref A α'')))) (f (∣ subst A (transC Γ (symC Γ γ~') (symC Γ γ~)) ∣s α''))))
      (~s (subst B (transC Γ γ~ γ~' ,p transC (EL A γ'') (subst-trans A γ~ γ~' (∣ subst A (symC Γ γ~) ∣s (∣ subst A (symC Γ γ~') ∣s α''))) (transC (EL A γ'') (~s (subst A γ~') (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A (symC Γ γ~') ∣s α''))) (subst-ref A (∣ subst A (symC Γ γ~') ∣s α'')))) (transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ γ~') γ~' α'')) (subst-ref A α''))))) (reff (subst-trans A (symC Γ γ~') (symC Γ γ~) α''))))
      (subst-trans B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A (symC Γ γ~') ∣s α''))) (subst-ref A (∣ subst A (symC Γ γ~') ∣s α''))) (γ~' ,p transC (EL A γ'') (symC (EL A γ'') (subst-trans A (symC Γ γ~') γ~' α'')) (subst-ref A α'')) (f (∣ subst A (symC Γ γ~) ∣s (∣ subst A (symC Γ γ~') ∣s α''))))) } }

lam : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam {Γ = Γ}{A = A}{B = B} t = record {
  ∣_∣t = λ γ → (λ α → ∣ t ∣t (γ ,Σ α)) ,sp λ {α}{α'} α~ → ~t t (refC Γ γ ,p transC (EL A γ) (subst-ref A α) α~) ;
  ~t = λ {γ}{γ'} γ~ {α}{α'} α~ → transC (EL B (γ' ,Σ α'))
    (symC (EL B (γ' ,Σ α')) (subst-trans B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α)) (subst-ref A α)) (refC Γ γ' ,p transC (EL A γ') (subst-ref A α) α~) (∣ t ∣t (γ ,Σ ∣ subst A (symC Γ γ~) ∣s α))))
    (~t t (γ~ ,p transC (EL A γ') (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ α)) (subst-ref A α)) α~)) }

app : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▷ A) k} → Tm Γ (Π A B) → Tm (Γ ▷ A) B
app {Γ = Γ}{A = A}{B = B} t = record {
  ∣_∣t = λ { (γ ,Σ α) → proj₁sp (∣ t ∣t γ) α } ;
  ~t = λ { {γ ,Σ α}{γ' ,Σ α'}(γ~ ,p α~) → transC (EL B (γ' ,Σ α')) (transC (EL B (γ' ,Σ α'))
    (transC (EL B (γ' ,Σ α'))
      (subst-trans B (refC Γ γ ,p transC (EL A γ) (subst-ref A α) (transC (EL A γ) (symC (EL A γ) (subst-ref A α)) (subst-trans A γ~ (symC Γ γ~) α))) (transC Γ γ~ (refC Γ γ') ,p transC (EL A γ') (subst-trans A γ~ (refC Γ γ') (∣ subst A (symC Γ γ~) ∣s (∣ subst A γ~ ∣s α))) (transC (EL A γ') (~s (subst A (refC Γ γ')) (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A γ~ ∣s α))) (subst-ref A (∣ subst A γ~ ∣s α)))) (transC (EL A γ') (subst-ref A (∣ subst A γ~ ∣s α)) α~))) (proj₁sp (∣ t ∣t γ) α))
      (~s (subst B (transC Γ γ~ (refC Γ γ') ,p transC (EL A γ') (subst-trans A γ~ (refC Γ γ') (∣ subst A (symC Γ γ~) ∣s (∣ subst A γ~ ∣s α))) (transC (EL A γ') (~s (subst A (refC Γ γ')) (transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A γ~ ∣s α))) (subst-ref A (∣ subst A γ~ ∣s α)))) (transC (EL A γ') (subst-ref A (∣ subst A γ~ ∣s α)) α~)))) (proj₂sp (∣ t ∣t γ) (transC (EL A γ) (symC (EL A γ) (subst-ref A α)) (subst-trans A γ~ (symC Γ γ~) α)))))
    (subst-trans B (γ~ ,p transC (EL A γ') (symC (EL A γ') (subst-trans A (symC Γ γ~) γ~ (∣ subst A γ~ ∣s α))) (subst-ref A (∣ subst A γ~ ∣s α))) (refC Γ γ' ,p transC (EL A γ') (subst-ref A (∣ subst A γ~ ∣s α)) α~) (proj₁sp (∣ t ∣t γ) (∣ subst A (symC Γ γ~) ∣s (∣ subst A γ~ ∣s α)))))
    (~t t γ~ α~) } }
