-- we enable type-in-type do not bother with universe levels
{-# OPTIONS --without-K --prop --type-in-type --show-irrelevant #-}

module Setoid.UnivElim-Sets3 where

open import Agda.Primitive
open import Setoid.lib
open import Setoid.Sets3.lib-abbrev
open import Setoid.Sets3.mini-univ
open import Setoid.Sets3
open import Setoid.CwF as CwF
open import Abbrevs using (wk)

toSU : Std → ∣U∣
toSU x = _ ,Σ pf x

open import Setoid.Pi

π₂' = λ Γ Δ A → π₂ {Γ = Γ} {Δ = Δ} {A = A}
wk' = λ Γ A → wk {Γ = Γ} {A = A}
id' = λ Γ → id {Γ = Γ}
app' = λ Γ A B → app {Γ = Γ} {A = A} {B = B}
ext = λ Γ Δ σ A → _,_ {Γ = Γ} {Δ = Δ} σ {A = A}

module _ {i} {Γ} where

  std-to-univ : Std → Tm Γ Univ
  std-to-univ A = record { ∣_∣t = λ γ' → _ ,Σ pf A ; ~t = λ p → tr (_ ,Σ pf~ A) }

  IxUniv : Ty (Γ ▷ Univ) _
  IxUniv = UnivEl (π₂ {Γ = Γ ▷ Univ} {Δ = Γ} {A = Univ} id) -- (π₂ id)

  ixstd-to-univ : ∀{A} → IxStd A → Tm (Γ ▷ UnivEl (std-to-univ A)) Univ
  ixstd-to-univ {A} B = record { ∣_∣t = λ { (γ' ,Σ a) → _ ,Σ pf B a }
                           ; ~t = λ p → tr (_ ,Σ (pf~ B (fromEl~ (pf~ A) (proj₂p p)))) }

  ΓAB = Γ ▷ Univ ▷ Π IxUniv Univ

  ΓAB→A : Tm ΓAB Univ
  ΓAB→A = π₂' ΓAB Γ Univ (wk' _ (Π IxUniv Univ))

  ΓAB→B : Tm ΓAB (Π IxUniv Univ [ wk' _ (Π IxUniv Univ) ]T)
  ΓAB→B = π₂' ΓAB (Γ ▷ Univ) (Π IxUniv Univ) (id' ΓAB)

  ΠS' : Tm ΓAB Univ
  ΠS' = ΠS {i} {ΓAB} ΓAB→A (app' ΓAB (UnivEl ΓAB→A) Univ ΓAB→B)

  id-sub : ∀ Γ → Tm {i} Γ Univ → Tms Γ (Γ ▷ Univ)
  id-sub Γ x = _,_ id {A = Univ} x

  wkwk : Tms ΓAB Γ
  wkwk = wk' Γ Univ ∘ wk' (Γ ▷ Univ) (Π IxUniv Univ)

  wkwk' : ∀ Γ A B → Tms (Γ ▷ A ▷ B) Γ
  wkwk' Δ A B = wk' Δ A ∘ wk' (Δ ▷ A) B

  ext-ΓAB : (ta : Tm Γ Univ) → Tm Γ (Π IxUniv Univ [ ext Γ Γ (id' Γ) Univ ta ]T) → Tms Γ ΓAB
  ext-ΓAB ta tb = ext Γ (Γ ▷ Univ) (ext Γ Γ (id' Γ) Univ ta) (Π IxUniv Univ) tb

  ext4 : ∀ A B C D
       → (ta : Tm Γ (A [ id' Γ ]T))
       → (tb : Tm Γ (B [ ext Γ Γ (id' Γ) A ta ]T))
       → (tc : Tm Γ (C [ ext Γ (Γ ▷ A) (ext Γ Γ (id' Γ) A ta) B tb ]T))
       → Tm Γ (D [ ext Γ (Γ ▷ A ▷ B) (ext Γ (Γ ▷ A) (ext Γ Γ (id' Γ) A ta) B tb) C tc ]T)
       → Tms Γ (Γ ▷ A ▷ B ▷ C ▷ D)
  ext4 = λ A B C D ta tb tc td →
    ext Γ (Γ ▷ A ▷ B ▷ C) (ext Γ (Γ ▷ A ▷ B) (ext Γ (Γ ▷ A) (ext Γ Γ (id' Γ) A ta) B tb) C tc) D td

  module _ (F : Ty (Γ ▷ Univ) i) where

    F-bool = F [ id-sub Γ BoolS ]T

    F-a : Ty ΓAB lzero
    F-a = F [ ext ΓAB Γ wkwk Univ ΓAB→A ]T

    F-b' : Ty ΓAB lzero
    F-b' = Π (IxUniv [ wk' (Γ ▷ Univ) (Π IxUniv Univ) ]T)
             (F [ ext ctx Γ (wkwk ∘ wk' ΓAB ElA) Univ (app' ΓAB ElA Univ (π₂' ΓAB (Γ ▷ Univ) (Π IxUniv Univ) id)) ]T)
      where
        ElA = IxUniv [ wk' (Γ ▷ Univ) (Π IxUniv Univ) ]T
        ctx = (ΓAB ▷ ElA)

    F-b : Ty (ΓAB ▷ F-a) lzero
    F-b = F-b' [ wk' ΓAB F-a ]T

    _‣_ = _▷_

    ih-simple : (a : Tm Γ Univ) → Tm Γ (Π Univ F) → Tm Γ (F [ id-sub Γ a ]T)
    ih-simple a elm = app' Γ Univ F elm [ id-sub _ a ]t

    ih-ix : (a : _) → (b : _) →  Tm Γ (Π Univ F) → Tm Γ (Π a (F [ ext (Γ ‣ a) Γ (wk' Γ a) Univ b ]T))
    ih-ix a b elm = lam {Γ = Γ} {A = a} {B = F-ta}
                     (app' Γ Univ F elm [ ext (Γ ‣ a) Γ (wk' Γ a) Univ b ]t)
          where F-ta = (F [ ext (Γ ▷ a) Γ (wk' Γ a) Univ b ]T)

    Elim-fun
      : Tm Γ F-bool
      → Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T)
      → (γ : ∣ Γ ∣C) → ∣ Π {Γ = Γ} Univ F ∣T γ

    Elim-fun-1
      : Tm Γ F-bool
      → Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T)
      → (γ : ∣ Γ ∣C) → (α : ∣ Univ {Γ = Γ} ∣T γ) → ∣ F ∣T γ ,Σ α

    Elim-fun-2
      : (fb : Tm Γ F-bool)
      → (fp : Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T))
      → ∀ {γ γ'} (γ~ : Γ C γ ~ γ')
         (α : ∣ Univ {Γ = Γ} ∣T γ) (α' : ∣ Univ {Γ = Γ} ∣T γ')
         (α~ : ↑ps (Univ {Γ = Γ} T γ~ ⊢ α ~ α'))
       → F T γ~ ,p un↑ps α~ ⊢ Elim-fun-1 fb fp γ α ~ Elim-fun-1 fb fp γ' α'

    Elim-fun-1 fb fp γ (_ ,Σ bool) = ∣ fb ∣t γ
    Elim-fun-1 fb fp γ (_ ,Σ π a b) = goal
      where
        tm-a : Tm Γ Univ
        tm-a = std-to-univ a
        ty-a = UnivEl (std-to-univ a)
        tm-b : Tm (Γ ▷ ty-a) Univ
        tm-b = ixstd-to-univ b
        tm-b' : Tm Γ (Π IxUniv Univ [ id-sub Γ tm-a ]T)
        tm-b' = lam {Γ = Γ} {A = IxUniv [ id-sub Γ tm-a ]T} {B = Univ} tm-b
        pi = ΠS tm-a tm-b
        πab : in-U (Σsp-U ∣ a ∣ ∣ b ∣ (a ~) (b ~))
        πab = π a b
        πsab : in-U (Σsp-U ∣ a ∣ ∣ b ∣ (El~ (tr (_ ,Σ pf~ a)))
                  λ x₀₁ → El~ (tr (_ ,Σ (pf~ b (fromEl~ (pf~ a) x₀₁)))))
        πsab = (proj₂ (∣ pi ∣t γ))
        eee : in-U~ (π a b)
                    (proj₂ (∣ (ΠS tm-a tm-b) ∣t γ))
                    (λ f₀ f₁ → fun-≡-P _ _ (El~ (tr (_ ,Σ pf~ a))) _ _
                               (λ x₀₁ → El~ (tr (_ ,Σ (pf~ b (fromEl~ (pf~ a) x₀₁)))))
                               (proj₁sp f₀) (proj₁sp f₁))
        eee = π~ (rel (in-El~ _ _ (tr (_ ,Σ pf~ a))))
                 (ixrel (λ x₀₁ → in-El~ _ _ (tr (_ ,Σ pf~ b (fromEl~ (pf~ a) x₀₁)))))
        eq = tr (_ ,Σ eee)

        -- ih-a'' : ∣ F ∣T ∣ id-sub Γ tm-a ∣s γ
        ih-a'' = Elim-fun-1 fb fp γ (_ ,Σ pf a)
        -- ih-b'' : ∣ Π ty-a (F [ ext (Γ ‣ ty-a) Γ (wk' Γ ty-a) Univ tm-b ]T) ∣T γ
        ih-b'' = (λ α → Elim-fun-1 fb fp γ (_ ,Σ pf b α))
               ,sp λ α α' α~ → Elim-fun-2 fb fp (refC Γ γ) (_ ,Σ pf b α) (_ ,Σ pf b α')
                                 (mk↑ps (tr (_ ,Σ pf~ b (fromEl~ (pf~ a) (un↑ps α~)))))

        aux''' : ∣ F ∣T (γ ,Σ (∣ pi ∣t γ))
        aux''' = ∣ fp ∣t ((_ ,Σ (_ ,Σ pf a) ,Σ ∣ tm-b' ∣t γ ,Σ ih-a'') ,Σ ih-b'')

        goal : ∣ F ∣T (γ ,Σ (_ ,Σ π a b))
        goal = coeT* F (refC Γ γ ,p eq) aux'''

    Elim-fun fb fp γ = Elim-fun-1 fb fp γ ,sp Elim-fun-2 fb fp (refC Γ γ)

    Elim-fun-2 fb fp γ~ _ _ (mk↑ps (tr (_ ,Σ bool~))) = ~t fb γ~
    Elim-fun-2 fb fp γ~ _ _ (mk↑ps (tr (_ ,Σ π~ {a₀} {a₁} {b₀} {b₁} a₀₁ b₀₁))) =
      transT F (symT F (cohT F _ _)) (transT F (~t fp
        ((((γ~ ,p (tr (_ ,Σ pf a₀₁))) ,p λ α α' α~ → tr (_ ,Σ (pf b₀₁ (fromEl~ (pf a₀₁) (un↑ps α~))))) ,p
          Elim-fun-2 fb fp γ~ _ _ (mk↑ps (tr (_ ,Σ pf a₀₁)))) ,p
            λ x x' x~ → Elim-fun-2 fb fp γ~ _ (_ ,Σ pf b₁ x') (mk↑ps (tr (_ ,Σ pf b₀₁ (fromEl~ (pf a₀₁) (un↑ps x~))))))
        ) (cohT F _ _))

    Elim : Tm Γ F-bool
         → Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T)
         → Tm Γ (Π Univ F)
    Elim fb fp = record { ∣_∣t = Elim-fun fb fp ; ~t = Elim-fun-2 fb fp }

    open import Relation.Binary.PropositionalEquality
    open import Setoid.Id

    Elim-bool-≡
      : (F[bool] : Tm Γ F-bool)
      → (F[pi] : Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T))
      → (app' Γ Univ F (Elim F[bool] F[pi]) [ id-sub Γ BoolS ]t) ≡ F[bool]
    Elim-bool-≡ F[bool] F[pi] = refl

    Elim-pi-≡
      : (F[bool] : Tm Γ F-bool)
      → (F[pi] : Tm (ΓAB ▷ F-a ▷ F-b) (F [ ext ΓAB Γ wkwk Univ ΠS' ∘ wkwk' ΓAB F-a F-b ]T))
      → (a : _) (b : _)
      → let b' = lam {Γ = Γ} {A = UnivEl a} {B = Univ} b
            elm = Elim F[bool] F[pi]
            ty = F [ id-sub Γ (ΠS a b) ]T
            p1 = app' Γ Univ F elm [ id-sub Γ (ΠS a b) ]t
            p2 = F[pi] [ ext4 Univ (Π IxUniv Univ) F-a F-b a b' (ih-simple a elm) (ih-ix (UnivEl a) b elm) ]t
        in Tm Γ (Id ty p1 [ ext Γ Γ (id' Γ) ty p2 ]T)
    ∣ Elim-pi-≡ F[bool] F[pi] a b ∣t γ =
      coeId {γ₀₁ = refC Γ γ}
        (symT F (transT F (~t F[pi] ((((refC Γ γ ,p withTrunc ee (λ { (_ ,Σ π~ A₀₁ B₀₁) → tr (_ ,Σ pf A₀₁)})) ,p
                λ x x' x~ → withTrunc ee (λ { (_ ,Σ π~ A₀₁ B₀₁) → tr (_ ,Σ (pf B₀₁ (fromEl~ (pf A₀₁) (un↑ps x~))))})) ,p
                  ~t (Elim F[bool] F[pi]) (refC Γ γ) (∣ a ∣t γ) (∣ a ∣t γ) (mk↑ps (refT (Univ {_} {Γ}) {γ} (∣ a ∣t γ))
                  )) ,p
                  λ x x' x~ → ~t (Elim F[bool] F[pi]) (refC Γ γ) (∣ b ∣t (_ ,Σ x)) (∣ b ∣t (_ ,Σ x'))
                     (mk↑ps (withTrunc ee (λ { (_ ,Σ π~ A₀₁ B₀₁) → tr (_ ,Σ (pf B₀₁ (fromEl~ (pf A₀₁) (un↑ps x~))))}))))) (cohT F _ (∣ F[pi] ∣t _)))) ∣idp∣
      where
        pi = ΠS a b
        ee = refU (∣ pi ∣t γ)
    ~t (Elim-pi-≡ F[bool] F[pi] a b) {γ} {γ'} p =
      transId (transId (symId (cohId _ ∣idp∣)) (idp~ {γ₀₁ = p})) (cohId _ ∣idp∣)

