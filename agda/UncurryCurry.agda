{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

-- proof that uncurry (curry P) ≃ P

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import HoTT
open import Polynomial
open import FinType
open import Bij
open import FinPolynomial
open ≡-Reasoning

import Bij as 𝔹
open 𝔹 using (𝔹)


module _ {I J K : Type₀} where

  
  op-uc→ : (P : (I ⊔ J) ↝f K) {k : K} → Op (fst (uncurry (curry P))) k → Op (fst P) k
  op-uc→ P (_ , c , _) = c


  op-uc≃ : (P : (I ⊔ J) ↝f K) {k : K} → is-equiv (op-uc→ P {k})
  op-uc≃ P = qinv-to-equiv ((λ c → (op-to-exp P c) , (c , refl)) , (lem , (λ _ → refl)))
    where
    lem : {k : K} (c : Op (fst (uncurry (curry P))) k) →  (op-to-exp P (op-uc→ P c) , op-uc→ P c , refl) ≡ c
    lem (_ , c , refl) = Σ-ext (ap (op-to-exp P) refl) (Σ-ext refl refl) -- a simple refl takes forever to compile
    

  uncurry-curry : (P : (I ⊔ J) ↝f K) →  fst (uncurry (curry P)) ≃₁ fst P
  uncurry-curry (P , Pf) = (record { Op→ = λ {k} → op-uc→ (P , Pf) {k}  ; Pm≃ = pm≃ }) , λ {k} → op-uc≃ (P , Pf) {k}
    where
    pm≃ : {ij : I ⊔ J} {k : K} {c : Op (fst (uncurry (curry (P , Pf)))) k} →
      Pm (fst (uncurry (curry (P , Pf)))) ij c ≃ Pm P ij (op-uc→ (P , Pf) c)
    pm≃ {inl i} {k} {jj , c} = ≃-refl
    pm≃ {inr j} {k} {c} = qinv (pm≃inr→ {j} {c}) (pm≃inr← {j} {c}) (pm≃inr←→ {j} {c}) (pm≃inr→← {j} {c})
      where
      pm≃inr→ : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} → Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)
                 → Pm P (inr j) (op-uc→ (P , Pf) c)
      pm≃inr→ {_} {_ , c , refl} (kₙ , eq) = transport (λ u → Pm P (inr u) c) eq (snd (coe (ap fst (≃ε 𝔹≃FinType (Pm-r (P , Pf) c))) kₙ))
      pm≃inr← : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} →  Pm P (inr j) (op-uc→ (P , Pf) c)
                → Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)
      fst (pm≃inr← {j} {_ , c , refl} p) = coe (! ap fst ( ≃ε 𝔹≃FinType (Pm-r (P , Pf) c))) (j , p)
      snd (pm≃inr← {j} {_ , c , refl} p) = ap fst (coe-∙! (ap fst (≃ε 𝔹≃FinType (Pm-r (P , Pf) c))) (j , p))
      pm≃inr←→ :  {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} (x : Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)) →
                    (pm≃inr← {j} {c} (pm≃inr→ {j} {c} x) ≡ x)
      pm≃inr←→ {j} {_ , c , refl} (kₙ , refl) =
        Σ-ext (coe-!∙ (ap fst (≃ε 𝔹≃FinType (Pm-r (P , Pf) c))) kₙ) (lem (ap fst (≃ε 𝔹≃FinType (Pm-r (P , Pf) c))) kₙ)
          where
          lem : ∀ {i} {A B : Type i} {P : B → Type i} (eq : A ≡ Σ B P) (x : A) →
            transport (λ p → fst (coe eq p) ≡ fst (coe eq x)) (coe-!∙ eq x) (ap fst (coe-∙! eq (coe eq x))) ≡ refl
          lem refl x = refl
      pm≃inr→← : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} (x : Pm P (inr j) (op-uc→ (P , Pf) c)) →
               (pm≃inr→ {j} {c} (pm≃inr← {j} {c} x) ≡ x)
      pm≃inr→← {j} {_ , c , refl} p = lem2 (j , p) (ap fst (≃ε 𝔹≃FinType (Pm-r (P , Pf) c)))
        where
        lem2 : ∀ {i} {A B : Type i} {P : A → Type i} (x : Σ A P) (p : B ≡ Σ A P) →
               transport (λ u → P u) (ap fst (coe-∙! p x)) (snd (coe p (coe (! p) x))) ≡ (snd x)
        lem2 x refl = refl
