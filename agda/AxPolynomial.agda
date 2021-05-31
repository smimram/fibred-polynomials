{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

-- Axiomatisation of finite polynomials

module AxPolynomial where

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import HoTT
open import Polynomial
open ≡-Reasoning


postulate
  is-small : ∀ {i} → Type i → Type i
  is-small-is-prop : ∀ {i} (A : Type i) → is-prop (is-small A)
  model : Type₀
  eq_model : model ≃ Σ Type₀ is-small
  is-small-Σ : ∀ {i j} {A : Type i} {B : A → Type j} → is-small A → ((a : A) → is-small (B a)) → is-small (Σ A B)
  is-small-⊔ : ∀ {i} {A B : Type i} → is-small A → is-small B → is-small (A ⊔ B)
  is-small-inl : ∀ {i} {A B : Type i} → is-small (A ⊔ B) → is-small A 
  is-small-inr : ∀ {i} {A B : Type i} → is-small (A ⊔ B) → is-small B
  is-small-⊤ : is-small ⊤
  transport-≃-small : ∀ {i j} {A : Type i} {B : Type j} (HA : is-small A) (B≃A : B ≃ A ) → is-small B
  transport-∥≃∥-small : ∀ {i j} {A : Type i} {B : Type j} (HA : is-small A) (B≃A : ∥ B ≃ A ∥ ) → is-small B
    -- these last two can be deduced from ua

m-to-Type : model → Type₀
m-to-Type b = fst (≃→ eq_model b)

is-small-pol : ∀ {ℓ} {I J : Type ℓ} (P : I ↝ J) → Type ℓ
is-small-pol {I = I} {J = J} P = {j : J} (c : Op P j) → is-small (Σ I (λ i → Pm P i c))

_↝s_ : ∀ {ℓ} (I J : Type ℓ) → Type (lsuc ℓ)
I ↝s J = Σ (Poly I J) is-small-pol



small-id : {I : Type₀} → is-small-pol (Id {I = I})
small-id {j = j} c = transport-≃-small is-small-⊤ (qinv (λ _ → tt) (λ _ → (j , refl)) (λ { ( _ , refl ) → refl} ) λ { tt → refl })

small-comp :
  {I J K : Type₀} {P : I ↝ J} {Q : J ↝ K} →
  is-small-pol P → is-small-pol Q → is-small-pol (P · Q)
small-comp {I} {J} {K} {P} {Q} FP FQ (c , a) = transport-≃-small {A = A} Af  (qinv f g g∘f f∘g)
  where
  A : Set
  A = Σ (Σ J (λ j → Pm Q j c)) λ { (j , b ) → Σ I λ i → Pm P i (a j b)}
  Af : is-small A
  Af = is-small-Σ (FQ c) (λ { (j , b) → FP (a j b) })
  f : Σ I (λ (i : I) → Pm (P · Q) i (c , a)) → A
  f (i , j , pQ , pP) =  ( j , pQ) , i , pP
  g : A → Σ I (λ (i : I) → Pm (P · Q) i (c , a))
  g (( j , pQ) , i , pP) = (i , j , pQ , pP)
  g∘f : (x : Σ I (λ (i : I) → Pm (P · Q) i (c , a))) → (g (f x) ≡ x)
  g∘f (_ , _ , _ , _) = refl
  f∘g : (x : A) → (f (g x) ≡ x)
  f∘g (( _ , _) , _ , _) = refl

is-small-⊔-r : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-small (Σ (I ⊔ J) P) → is-small (Σ J (P ∘ inr))
is-small-⊔-r F = is-small-inr (transport-≃-small F  ( ≃-sym Σ-⊔ ))


is-small-⊔-l : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-small (Σ (I ⊔ J) P) → is-small (Σ I (P ∘ inl))
is-small-⊔-l F = is-small-inl (transport-≃-small F   (≃-sym Σ-⊔) )

Σ-⊔-is-small : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-small (Σ I (P ∘ inl)) → is-small (Σ J (P ∘ inr)) → is-small (Σ (I ⊔ J) P)
Σ-⊔-is-small FI FJ = transport-≃-small (is-small-⊔ FI FJ)  Σ-⊔ 


module _ {I J K : Type₀} where

  Pm-r : (P : (I ⊔ J) ↝s K) {k : K} (c : Op (fst P) k) → Σ Type₀ is-small
  Pm-r P {k} c = Σ J ((λ i → Pm (fst P) i c) ∘ inr) ,
              is-small-⊔-r ((snd P) c)  

  Exps : Type₀ → Type₀
  Exps A = Σ model (λ b → (fst (≃→ eq_model b) → A))

  op-to-exp : (P : (I ⊔ J) ↝s K) {k : K} (c : Op (fst P) k) → Exps J
  op-to-exp (P , Pf) c = ≃← eq_model (Pm-r (P , Pf) c)  ,
    (λ p → fst (coe (ap fst (≃ε eq_model (Pm-r (P , Pf) c))) p))


  curry : (I ⊔ J) ↝s K → I ↝s (Exps J × K)
  curry (P , Pf) = Q , Qf
    where
    Q : Poly I (Exps J × K)
    Op Q (expj , k) = Σ (Op P k) (λ c → op-to-exp (P , Pf) c ≡ expj)
    Pm Q i {(b , f) , k} (c , e) = Pm P (inl i) c 
    Qf : is-small-pol Q
    Qf {(b , f) , k} (c , e) = is-small-⊔-l {I = I} {J = J} (Pf c) 

  uncurry : I ↝s (Exps J × K) → (I ⊔ J) ↝s K
  uncurry (P , Pf) = Q , Qf
    where
    Q : Poly (I ⊔ J) K
    Op Q k = Σ (Exps J) (λ jj → Op P (jj , k))
    Pm Q (inl i) (jj , c) = Pm P i c
    Pm Q (inr j) (jj , c) = Σ (fst (≃→ eq_model (fst jj))) (λ p → snd jj p ≡ j)
    Qf : is-small-pol Q
    Qf ((b , f) , c) = Σ-⊔-is-small (Pf c) (transport-≃-small (snd (≃→ eq_model b)) e  )
      where
      e : Σ J (λ j → Σ (fst (≃→ eq_model b)) (λ p → f p ≡ j)) ≃ (fst (≃→ eq_model b))
      e = qinv (λ { (.(_) , B , refl) → B }) (λ k → f k , k , refl) (λ { (_ , _ , refl) → refl }) (λ x → refl)


  ---- curry of uncurry ----

  Pm-r-uncurry→ : (P : I ↝s (Exps J × K)) (k : K) (n : model) (f : m-to-Type n → J) (c : Op (fst P) ((n , f) , k)) →
                fst (Pm-r (uncurry P) ((n , f) , c)) → fst (≃→ eq_model n)
  Pm-r-uncurry→ P k n f c (_ , kₙ , _) = kₙ    

  Pm-r-uncurry : (P : I ↝s (Exps J × K)) (k : K) (n : model) (f : m-to-Type n → J) (c : Op (fst P) ((n , f) , k)) → Pm-r (uncurry P) ((n , f) , c) ≡ ≃→ eq_model n
  Pm-r-uncurry P k n f c = Σ-ext (ua (qinv (Pm-r-uncurry→ P k n f c) pm-r-u← eq1 λ _ → refl)) (is-small-is-prop (m-to-Type n) _ _) 
    where
    pm-r-u← : fst (≃→ eq_model n) → fst (Pm-r (uncurry P) ((n , f) , c))
    pm-r-u← x = (f x) , (x , refl)
    eq1 : (pm-r-u← ∘ (Pm-r-uncurry→ P k n f c)) ∼ id
    eq1 (_ , kₙ , refl) = refl

  
  transport-fst-Σ-ext : ∀ {i j} (B : Type i → Type j) {x y : Σ (Type i) B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y)
                         → transport fst (Σ-ext p q) ≡ coe p
  transport-fst-Σ-ext B refl refl = refl

  fst-Pm-r-uncurry : (P : I ↝s (Exps J × K)) (k : K) (n : model) (f : m-to-Type n → J) (c : Op (fst P) ((n , f) , k)) →
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

  lem2 : (P : I ↝s (Exps J × K)) (k : K) (f  : Exps J) (c : Op (fst P) (f , k)) →
    snd (op-to-exp (uncurry P) (f , c)) ≡ ((snd f) ∘ transport m-to-Type (ap (≃← eq_model) (Pm-r-uncurry P k (fst f) (snd f) c) ∙ ≃η eq_model (fst f)))
  lem2 P k (n , f) c = begin
           (fst ∘ (coe (ap fst _)))
             ≡⟨ ap (λ u → fst ∘ u) (coe-ap fst _) ⟩
           fst ∘ (transport fst (≃ε eq_model (Pm-r (uncurry P) ((n , f) , c))))
             ≡⟨  ap (fst ∘_) (ttt fst _ _ (≃ε eq_model) (Pm-r-uncurry P k n f c)) ⟩ 
           (fst ∘ (transport fst (! Pm-r-uncurry P k n f c)) ∘ (transport fst (≃ε eq_model (≃→ eq_model n))) ∘ transport fst (ap (λ z → ≃→ eq_model (≃← eq_model z)) (Pm-r-uncurry P k n f c)))
             ≡⟨ triple {f = transport fst (ap (λ z → ≃→ eq_model (≃← eq_model z)) (Pm-r-uncurry P k n f c))}
                       {g = (transport fst (≃ε eq_model (≃→ eq_model n)))}
                       {h = fst ∘ (transport fst (! Pm-r-uncurry P k n f c))}
                       (! transport-ap-ext _ _ _ ∙ transport-ap-ext m-to-Type (≃← eq_model) (Pm-r-uncurry P k n f c)) (! ap (transport fst) (≃c eq_model n) ∙ ! transport-ap-ext fst (≃→ eq_model) _) ((fst-Pm-r-uncurry P k n f c))  ⟩
            f ∘ (transport m-to-Type (≃η eq_model n)) ∘ (transport m-to-Type (ap (≃← eq_model) (Pm-r-uncurry P k n f c)))
             ≡⟨  ap (f ∘_ ) (! transport-∙-ext m-to-Type (ap (≃← eq_model) (Pm-r-uncurry P k n f c))  (≃η eq_model n))  ⟩ refl 


  snd-op-to-exp-uncurry : (P : I ↝s (Exps J × K)) (k : K) (f : Exps J) (c : Op (fst P) (f , k)) →
    transport (λ b → m-to-Type b → J) (ap (≃← eq_model) (Pm-r-uncurry P k (fst f) (snd f) c) ∙ ≃η eq_model (fst f)) (snd (op-to-exp (uncurry P) ((fst f , snd f) , c))) ≡ (snd f) 
  snd-op-to-exp-uncurry P k (n , f) c = begin
    _ ≡⟨ tlemma model m-to-Type J (ap (≃← eq_model) (Pm-r-uncurry P k n f c) ∙ ≃η eq_model n) (snd (op-to-exp (uncurry P) ((n , f) , c))) ⟩
    _ ≡⟨ tlemma2 model m-to-Type (ap (≃← eq_model) (Pm-r-uncurry P k n f c) ∙ ≃η eq_model n) (snd (op-to-exp (uncurry P) ((n , f) , c))) f (lem2 P k (n , f) c) ⟩ refl




  op-to-exp-uncurry : (P : I ↝s (Exps J × K)) (k : K) (f : Exps J) (c : Op (fst P) (f , k))  → op-to-exp (uncurry P) (f , c) ≡ f
  op-to-exp-uncurry P k (n , f) c = Σ-ext ((ap (≃← eq_model) (Pm-r-uncurry P k n f c)) ∙ (≃η eq_model n)) (snd-op-to-exp-uncurry P k (n , f) c )


  op-cu→ : (P : I ↝s (Exps J × K)) {f : Exps J} {k : K} → Op (fst (curry (uncurry P))) (f , k) → Op (fst P) (f , k)
  op-cu→ P {f} {k} ((f' , c) , eq ) = transport (λ u → Op (fst P) (u , k)) (! (! eq ∙ (op-to-exp-uncurry P k f' c))) c
 
      
  op-cu← : (P : I ↝s (Exps J × K)) {k : K} (f : Exps J)  → Op (fst P) (f , k) → Op (fst (curry (uncurry P))) (f , k)
  op-cu← P {k} f  c = (f , c) , op-to-exp-uncurry P k f c

  lem_n : ∀ {i} {A : Type i} (C : A → Type i) (B : A → Type i) (P : (a : A) → B a → C a) {x y : A} (p : x ≡ y) (u : B y) →
            P x (transport B (! p) u) ≡ transport C (! p) (P y u)
  lem_n C B P refl u = refl


  transport-op-uc : (P : I ↝s (Exps J × K)) (k : K) {f f' : Exps J} (p : f ≡ f') (c : Op (fst P) (f , k)) (q : op-to-exp (uncurry P) (f , c) ≡ f)
    → transport (λ (z : Exps J) → Op (fst (curry (uncurry P))) (z , k)) p ((f , c) , q) ≡ ((f , c) , q ∙ p)
  transport-op-uc P k refl c q =  Σ-ext refl (! ∙-unit-r q)

  op-cu≃ : (P : I ↝s (Exps J × K)) {f : Exps J} {k : K} → is-equiv (op-cu← P {k} f)
  op-cu≃ P {f} {k} = qinv-to-equiv ((op-cu→ P {f} {k}) , ((λ x → eq2 x) , λ x → eq1 x))
    where
    eq1 : {f : Exps J} {k : K} (x : Op (fst (curry (uncurry P))) (f , k)) → (op-cu← P f (op-cu→ P x) ≡ x)
    eq1 {_} {k} ((f , c) , refl) =
      _ ≡⟨ lem_n _ (λ u → Op (fst P) (u , k)) (op-cu← P)  (op-to-exp-uncurry P k f c) c ⟩
       _ ≡⟨ transport-op-uc P k (! op-to-exp-uncurry P k f c) c _ ⟩ Σ-ext refl (∙-inv-r (op-to-exp-uncurry P k f c))
    eq2 : {f : Exps J} {k : K} (x : Op (fst P) (f , k)) → op-cu→ P (op-cu← P f x) ≡ x
    eq2 {f} {k} x = lem (λ u → Op (fst P) (u , k)) (op-to-exp-uncurry P k f x) x
      where
      lem : ∀ {i} {A : Type i} (P : A → Type i) {x y : A} (p : x ≡ y) (u : P y) →
          transport P (! (! p ∙ p)) u ≡ u
      lem P refl u = refl
      
  cu-≃₁ :  (P : I ↝s (Exps J × K)) → fst P ≃₁ fst (curry (uncurry P))
  cu-≃₁ P = (record { Op→ = op→ ; Pm≃ = ≃-refl }) , op-cu≃ P
    where
    op→ : {j : Exps J × K}  → Op (fst P) j →  Op (fst (curry (uncurry P))) j
    op→ {(f , k)} c = op-cu← P f c

 --- uncurry of curry ----

  op-uc→ : (P : (I ⊔ J) ↝s K) {k : K} → Op (fst (uncurry (curry P))) k → Op (fst P) k
  op-uc→ P (_ , c , _) = c


  op-uc≃ : (P : (I ⊔ J) ↝s K) {k : K} → is-equiv (op-uc→ P {k})
  op-uc≃ P = qinv-to-equiv ((λ c → (op-to-exp P c) , (c , refl)) , (lem , (λ _ → refl)))
    where
    lem : {k : K} (c : Op (fst (uncurry (curry P))) k) →  (op-to-exp P (op-uc→ P c) , op-uc→ P c , refl) ≡ c
    lem (_ , c , refl) = Σ-ext (ap (op-to-exp P) refl) (Σ-ext refl refl) -- a simple refl takes forever to compile
    


  uncurry-curry : (P : (I ⊔ J) ↝s K) →  fst (uncurry (curry P)) ≃₁ fst P
  uncurry-curry (P , Pf) = (record { Op→ = λ {k} → op-uc→ (P , Pf) {k}  ; Pm≃ = pm≃ }) , λ {k} → op-uc≃ (P , Pf) {k}
    where
    pm≃ : {ij : I ⊔ J} {k : K} {c : Op (fst (uncurry (curry (P , Pf)))) k} →
      Pm (fst (uncurry (curry (P , Pf)))) ij c ≃ Pm P ij (op-uc→ (P , Pf) c)
    pm≃ {inl i} {k} {jj , c} = ≃-refl
    pm≃ {inr j} {k} {c} = qinv (pm≃inr→ {j} {c}) (pm≃inr← {j} {c}) (pm≃inr←→ {j} {c}) (pm≃inr→← {j} {c})
      where
      pm≃inr→ : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} → Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)
                 → Pm P (inr j) (op-uc→ (P , Pf) c)
      pm≃inr→ {_} {_ , c , refl} (kₙ , eq) = transport (λ u → Pm P (inr u) c) eq (snd (coe (ap fst (≃ε eq_model (Pm-r (P , Pf) c))) kₙ))
      pm≃inr← : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} →  Pm P (inr j) (op-uc→ (P , Pf) c)
                → Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)
      fst (pm≃inr← {j} {_ , c , refl} p) = coe (! ap fst ( ≃ε eq_model (Pm-r (P , Pf) c))) (j , p)
      snd (pm≃inr← {j} {_ , c , refl} p) = ap fst (coe-∙! (ap fst (≃ε eq_model (Pm-r (P , Pf) c))) (j , p))
      pm≃inr←→ :  {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} (x : Pm (fst (uncurry (curry (P , Pf)))) (inr j) (c)) →
                    (pm≃inr← {j} {c} (pm≃inr→ {j} {c} x) ≡ x)
      pm≃inr←→ {j} {_ , c , refl} (kₙ , refl) =
        Σ-ext (coe-!∙ (ap fst (≃ε eq_model (Pm-r (P , Pf) c))) kₙ) (lem (ap fst (≃ε eq_model (Pm-r (P , Pf) c))) kₙ)
          where
          lem : ∀ {i} {A B : Type i} {P : B → Type i} (eq : A ≡ Σ B P) (x : A) →
            transport (λ p → fst (coe eq p) ≡ fst (coe eq x)) (coe-!∙ eq x) (ap fst (coe-∙! eq (coe eq x))) ≡ refl
          lem refl x = refl
      pm≃inr→← : {j : J} {c : Op (fst (uncurry (curry (P , Pf)))) k} (x : Pm P (inr j) (op-uc→ (P , Pf) c)) →
               (pm≃inr→ {j} {c} (pm≃inr← {j} {c} x) ≡ x)
      pm≃inr→← {j} {_ , c , refl} p = lem2' (j , p) (ap fst (≃ε eq_model (Pm-r (P , Pf) c)))
        where
        lem2' : ∀ {i} {A B : Type i} {P : A → Type i} (x : Σ A P) (p : B ≡ Σ A P) →
               transport (λ u → P u) (ap fst (coe-∙! p x)) (snd (coe p (coe (! p) x))) ≡ (snd x)
        lem2' x refl = refl
