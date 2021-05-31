{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

-- proof that curry (uncurry P) ≃ P

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

  Pm-r-uncurry→ : (P : I ↝f (Exp J × K)) (k : K) (n : 𝔹) (f : 𝔹-to-Fin n → J) (c : Op (fst P) ((n , f) , k)) →
                fst (Pm-r (uncurry P) ((n , f) , c)) → fst (≃→ 𝔹≃FinType n)
  Pm-r-uncurry→ P k n f c (_ , kₙ , _) = kₙ    

  Pm-r-uncurry : (P : I ↝f (Exp J × K)) (k : K) (n : 𝔹) (f : 𝔹-to-Fin n → J) (c : Op (fst P) ((n , f) , k)) → Pm-r (uncurry P) ((n , f) , c) ≡ ≃→ 𝔹≃FinType n
  Pm-r-uncurry P k n f c = Σ-ext (ua (qinv (Pm-r-uncurry→ P k n f c) pm-r-u← eq1 λ _ → refl)) (is-finite-is-prop (𝔹-to-Fin n) _ _) 
    where
    pm-r-u← : fst (≃→ 𝔹≃FinType n) → fst (Pm-r (uncurry P) ((n , f) , c))
    pm-r-u← x = (f x) , (x , refl)
    eq1 : (pm-r-u← ∘ (Pm-r-uncurry→ P k n f c)) ∼ id
    eq1 (_ , kₙ , refl) = refl

  transport-fst-Σ-ext : ∀ {i j} (B : Type i → Type j) {x y : Σ (Type i) B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y)
                         → transport fst (Σ-ext p q) ≡ coe p
  transport-fst-Σ-ext B refl refl = refl

  fst-Pm-r-uncurry : (P : I ↝f (Exp J × K)) (k : K) (n : 𝔹) (f : 𝔹-to-Fin n → J) (c : Op (fst P) ((n , f) , k)) →
                         fst ∘ transport fst (! Pm-r-uncurry P k n f c) ≡ f
  fst-Pm-r-uncurry P k n f c = 
                     begin
                       fst ∘ transport fst (! Σ-ext _ _)
                         ≡⟨ ap (λ u → fst ∘ transport fst u) (Σ-ext-! _ _) ⟩
                       fst ∘ transport fst (Σ-ext _ _)
                         ≡⟨ ap (λ u → fst ∘ u) (transport-fst-Σ-ext _ _ _) ⟩
                       fst ∘ coe (! ua _)
                         ≡⟨ ap (λ u → fst ∘ coe u) (ua-! _ _ _) ⟩
                       fst ∘ coe (ua _ )
                         ≡⟨ ap (λ u → fst ∘ u) (coe-ua _) ⟩
                         refl

  tlemma : ∀ {i} (A : Type i) (B : A → Type i) (C : Type i) {x y : A} (p : x ≡ y) (t : B x → C) → transport (λ u → B u → C) p t ≡ t ∘ (transport B (! p)) 
  tlemma A B C refl r = refl

  tlemma2 : ∀ {i} (A : Type i) (B : A → Type i) {C : Type i} {x y : A} (p : x ≡ y) (f : B x → C) (g : B y → C) →
    (f ≡ g ∘ transport B p) → (f ∘ transport B (! p) ≡ g)
  tlemma2 A B refl f g refl = refl

  ttt : ∀ {i j k} {A : Type i} {C : Type j} (B : A → Type k) (f g : C → A) (P : (c : C) → f c ≡ g c) {x y : C} (p : x ≡ y)
      → transport B (P x) ≡ (transport (B ∘ g) (! p)) ∘  (transport B (P y)) ∘ (transport B (ap f  p))
  ttt B f g P refl = refl

  triple : ∀ {i} {A B C D : Type i} {f f' : A → B} {g g' : B → C} {h h' : C → D}
             → (f ≡ f') → (g ≡ g') → (h ≡ h') → (h ∘ g ∘ f ≡ h' ∘ g' ∘ f')
  triple refl refl refl = refl

  lem2 : (P : I ↝f (Exp J × K)) (k : K) (f  : Exp J) (c : Op (fst P) (f , k)) →
    snd (op-to-exp (uncurry P) (f , c)) ≡ ((snd f) ∘ transport 𝔹-to-Fin (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k (fst f) (snd f) c) ∙ ≃η 𝔹≃FinType (fst f)))
  lem2 P k (n , f) c = begin
           (fst ∘ (coe (ap fst _)))
             ≡⟨ ap (λ u → fst ∘ u) (coe-ap fst _) ⟩
           fst ∘ (transport fst (≃ε 𝔹≃FinType (Pm-r (uncurry P) ((n , f) , c))))
             ≡⟨  ap (fst ∘_) (ttt fst _ _ (≃ε 𝔹≃FinType) (Pm-r-uncurry P k n f c)) ⟩ 
           (fst ∘ (transport fst (! Pm-r-uncurry P k n f c)) ∘ (transport fst (≃ε 𝔹≃FinType (≃→ 𝔹≃FinType n))) ∘ transport fst (ap (λ z → ≃→ 𝔹≃FinType (≃← 𝔹≃FinType z)) (Pm-r-uncurry P k n f c)))
             ≡⟨ triple {f = transport fst (ap (λ z → ≃→ 𝔹≃FinType (≃← 𝔹≃FinType z)) (Pm-r-uncurry P k n f c))}
                       {g = (transport fst (≃ε 𝔹≃FinType (≃→ 𝔹≃FinType n)))}
                       {h = fst ∘ (transport fst (! Pm-r-uncurry P k n f c))}
                       (! transport-ap-ext _ _ _ ∙ transport-ap-ext 𝔹-to-Fin (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c)) (! ap (transport fst) (≃c 𝔹≃FinType n) ∙ ! transport-ap-ext fst (≃→ 𝔹≃FinType) _) ((fst-Pm-r-uncurry P k n f c))  ⟩
           {! f ∘ (transport 𝔹-to-Fin (≃η 𝔹≃FinType n)) ∘ (transport 𝔹-to-Fin (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c)))
             ≡⟨  ap (f ∘_ ) (! transport-∙-ext 𝔹-to-Fin (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c))  (≃η 𝔹≃FinType n))  ⟩ refl !}
         -- takes too long to compile

  snd-op-to-exp-uncurry : (P : I ↝f (Exp J × K)) (k : K) (f : Exp J) (c : Op (fst P) (f , k)) →
    transport (λ b → 𝔹-to-Fin b → J) (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k (fst f) (snd f) c) ∙ ≃η 𝔹≃FinType (fst f)) (snd (op-to-exp (uncurry P) ((fst f , snd f) , c))) ≡ (snd f) 
  snd-op-to-exp-uncurry P k (n , f) c = begin
    _ ≡⟨ tlemma 𝔹 𝔹-to-Fin J (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c) ∙ ≃η 𝔹≃FinType n) (snd (op-to-exp (uncurry P) ((n , f) , c))) ⟩
    _ ≡⟨ tlemma2 𝔹 𝔹-to-Fin (ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c) ∙ ≃η 𝔹≃FinType n) (snd (op-to-exp (uncurry P) ((n , f) , c))) f (lem2 P k (n , f) c) ⟩ refl

  

  op-to-exp-uncurry' : (P : I ↝f (Exp J × K)) (k : K) (f : Exp J) (c : Op (fst P) (f , k))  → op-to-exp (uncurry P) (f , c) ≡ f
  op-to-exp-uncurry' P k (n , f) c = Σ-ext ((ap (≃← 𝔹≃FinType) (Pm-r-uncurry P k n f c)) ∙ (≃η 𝔹≃FinType n)) (snd-op-to-exp-uncurry P k (n , f) c )

  postulate -- we get bad performance if we use the version defined above...
    op-to-exp-uncurry : (P : I ↝f (Exp J × K)) (k : K) (f : Exp J) (c : Op (fst P) (f , k))  → op-to-exp (uncurry P) (f , c) ≡ f
  
  op-cu→ : (P : I ↝f (Exp J × K)) {f : Exp J} {k : K} → Op (fst (curry (uncurry P))) (f , k) → Op (fst P) (f , k)
  op-cu→ P {f} {k} ((f' , c) , eq ) = transport (λ u → Op (fst P) (u , k)) (! (! eq ∙ (op-to-exp-uncurry P k f' c))) c
 
      
  op-cu← : (P : I ↝f (Exp J × K)) {k : K} (f : Exp J)  → Op (fst P) (f , k) → Op (fst (curry (uncurry P))) (f , k)
  op-cu← P {k} f  c = (f , c) , op-to-exp-uncurry P k f c

  lem_n : ∀ {i} {A : Type i} (C : A → Type i) (B : A → Type i) (P : (a : A) → B a → C a) {x y : A} (p : x ≡ y) (u : B y) →
            P x (transport B (! p) u) ≡ transport C (! p) (P y u)
  lem_n C B P refl u = refl


  transport-op-uc : (P : I ↝f (Exp J × K)) (k : K) {f f' : Exp J} (p : f ≡ f') (c : Op (fst P) (f , k)) (q : op-to-exp (uncurry P) (f , c) ≡ f)
    → transport (λ (z : Exp J) → Op (fst (curry (uncurry P))) (z , k)) p ((f , c) , q) ≡ ((f , c) , q ∙ p)
  transport-op-uc P k refl c q =  Σ-ext refl (! ∙-unit-r q)

  op-cu≃ : (P : I ↝f (Exp J × K)) {f : Exp J} {k : K} → is-equiv (op-cu← P {k} f)
  op-cu≃ P {f} {k} = qinv-to-equiv ((op-cu→ P {f} {k}) , ((λ x → eq2 x) , λ x → eq1 x))
    where
    eq1 : {f : Exp J} {k : K} (x : Op (fst (curry (uncurry P))) (f , k)) → (op-cu← P f (op-cu→ P x) ≡ x)
    eq1 {_} {k} ((f , c) , refl) =
      _ ≡⟨ lem_n _ (λ u → Op (fst P) (u , k)) (op-cu← P)  (op-to-exp-uncurry P k f c) c ⟩
       _ ≡⟨ transport-op-uc P k (! op-to-exp-uncurry P k f c) _ _ ⟩ Σ-ext refl (∙-inv-r (op-to-exp-uncurry P k f c))
    eq2 : {f : Exp J} {k : K} (x : Op (fst P) (f , k)) → op-cu→ P (op-cu← P f x) ≡ x
    eq2 {f} {k} x = lem (λ u → Op (fst P) (u , k)) (op-to-exp-uncurry P k f x) x
      where
      lem : ∀ {i} {A : Type i} (P : A → Type i) {x y : A} (p : x ≡ y) (u : P y) →
          transport P (! (! p ∙ p)) u ≡ u
      lem P refl u = refl

  

  cu-≃₁ :  (P : I ↝f (Exp J × K)) →    fst P ≃₁ fst (curry (uncurry P))
  cu-≃₁ P = (record { Op→ = op→ ; Pm≃ = ≃-refl }) , op-cu≃ P
    where
    op→ : {j : Exp J × K}  → Op (fst P) j →  Op (fst (curry (uncurry P))) j
    op→ {(f , k)} c = op-cu← P f c
    
