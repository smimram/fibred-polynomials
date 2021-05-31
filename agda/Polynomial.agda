{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module Polynomial where

open import HoTT

open ≡-Reasoning

record Poly {ℓ} (I J : Type ℓ) : Type (lsuc ℓ) where
  field
    -- operations
    Op : J → Type ℓ
    -- parameters
    Pm : (i : I) → {j : J} → Op j → Type ℓ

open Poly public

module _ {ℓ} {I J : Type ℓ} where

  record Poly→ (P Q : Poly I J) : Type ℓ where
    field
      Op→ : {j : J} → Op P j → Op Q j
      Pm≃ : {i : I} {j : J} {c : Op P j} → Pm P i c ≃ Pm Q i (Op→ c)

  open Poly→

  _↝₂_ : (P Q : Poly I J) → Type ℓ
  P ↝₂ Q = Poly→ P Q

  module _ {P Q : Poly I J} (ϕ : P ↝₂ Q) where
    Pm→ : {i : I} {j : J} {c : Op P j} → Pm P i c → Pm Q i (Op→ ϕ c)
    Pm→ = ≃→ (Pm≃ ϕ)

    Pm← : {i : I} {j : J} {c : Op P j} → Pm Q i (Op→ ϕ c) → Pm P i c
    Pm← = ≃← (Pm≃ ϕ)

    Pmη : {i : I} {j : J} {c : Op P j} (p : Pm P i c) → Pm← (Pm→ p) ≡ p
    Pmη = ≃η (Pm≃ ϕ)

    Pmε : {i : I} {j : J} {c : Op P j} (p : Pm Q i (Op→ ϕ c)) → Pm→ (Pm← p) ≡ p
    Pmε = ≃ε (Pm≃ ϕ)

    -- record Poly≃ (ϕ : Poly→ P Q) : Type ℓ where
      -- field
        -- Op≃ : {j : J} → is-equiv (Op→ ϕ {j})
        -- Pm≃ : {j : J} {c : Op P j} → is-equiv (Pm→ ϕ {j} {c})

    -- open Poly≃

    -- Poly-ua : {ϕ : Poly→ P Q} (ϕ≃ : Poly≃ ϕ) → P ≡ Q
    -- Poly-ua {ϕ = ϕ} ϕ≃ with funext (λ j → ua (Op→ ϕ {j} , Op≃ ϕ≃ {j})) | funext2 (λ j c → ua (Pm→ ϕ {j} {c} , Pm≃ ϕ≃ {j} {c}))
    -- ... | refl | pm≃ = {!!}

  module _ {P Q : Poly I J} where

    record Poly≃₂ (ϕ ψ : P ↝₂ Q) : Type ℓ where
      field
        Op≃₂ : {j : J} (c : Op P j) → Op→ ϕ c ≡ Op→ ψ c
        Pm≃₂ : {i : I} {j : J} {c : Op P j} (p : Pm P i c) → transport (Pm Q i) (Op≃₂ c) (Pm→ ϕ p) ≡ Pm→ ψ p

open Poly→
open Poly≃₂

_↝_ : ∀ {ℓ} (I J : Type ℓ) → Type (lsuc ℓ)
I ↝ J = Poly I J

module _ {ℓ} {I J : Type ℓ} where

  Poly-equiv : {P Q : I ↝ J} (ϕ : P ↝₂ Q) → Type ℓ
  Poly-equiv ϕ = {j : J} → is-equiv (Op→ ϕ {j = j})

  _≃₁_ : (P Q : I ↝ J) → Type ℓ
  P ≃₁ Q = Σ (P ↝₂ Q) Poly-equiv

  ≃₁-sym : {P Q : I ↝ J} → P ≃₁ Q → Q ≃₁ P
  ≃₁-sym {Q = Q} (ϕ , ϕ≃) = (record { Op→ = ≃← (equiv ϕ≃) ; Pm≃ = λ {i} {j} {c} → ≃-trans (id-to-equiv (ap (Pm Q i) (! (≃ε (equiv ϕ≃) c)))) (≃-sym (Pm≃ ϕ)) }) , snd (≃-sym (equiv ϕ≃))

  Op≃ : {P Q : I ↝ J} (ϕ : P ≃₁ Q) {j : J} → Op P j ≃ Op Q j
  Op≃ (ϕ , ϕ≃) = equiv ϕ≃

  Poly-ext : (P Q : I ↝ J) (op : Op P ≡ Op Q) (pm : transport (λ Op → I → {j : J} → Op j → Type ℓ) op (Pm P) ≡ Pm Q) → P ≡ Q
  Poly-ext _ _ refl refl = refl

  Poly-funext : {P Q : I ↝ J} (op : (j : J) → Op P j ≡ Op Q j) (pm : (i : I) {j : J} (c : Op P j) → Pm P i c ≡ Pm Q i (coe (op j) c)) → P ≡ Q
  Poly-funext {P} {Q} op pm = Poly-ext P Q (funext op) lem
    where
    -- this is a general lemma similar to transport-arg but I am getting tired with multiple and implicit arguments
    lem2 : (p : (λ x → Op P x) ≡ (λ x → Op Q x)) → transport (λ Op → I → {j : J} → Op j → Type ℓ) p (Pm P) ≡ ((λ i {j} c → Pm P i (coe (! (happly p j)) c)))
    lem2 refl = refl
    lem : transport (λ Op → I → {j : J} → Op j → Type ℓ) (funext op) (Pm P) ≡ Pm Q
    lem =
      transport (λ Op → I → {j : J} → Op j → Type ℓ) (funext op) (Pm P) ≡⟨ lem2 (funext op) ⟩
      ((λ i {j} c → Pm P i (coe (! (happly (funext op) j)) c))) ≡⟨ funext (λ i → funextopt λ j → funext λ c → funext-comp op j |in-ctx λ op → Pm P i (coe (! op) c)) ⟩
      (λ i {j} c → Pm P i (coe (! (op j)) c)) ≡⟨ funext (λ i → funextopt λ j → funext λ c → pm i (coe (! (op j)) c)) ⟩
      (λ i {j} c → Pm Q i (coe (op j) (coe (! (op j)) c))) ≡⟨ funext (λ i → funextopt λ j → funext λ c → ap (λ O → Pm Q i (O c)) (trans (! coe-∙ (! (op j)) (op j)) (ap coe (∙-inv-l (op j))))) ⟩
      (λ i {j} c → Pm Q i c) ≡⟨ refl ⟩
      Pm Q ∎

  Poly-ua : {P Q : I ↝ J} → P ≃₁ Q → P ≡ Q
  Poly-ua {Q = Q} (ϕ , ϕ≃) = Poly-funext (λ j → ua (equiv ϕ≃)) (λ i {j} c → ua (≃-trans (Pm≃ ϕ {i = i} {c = c}) (id-to-equiv (ap (Pm Q i) (sym (happly (coe-ua (equiv ϕ≃)) c))))))

  _≃₂_ : {P Q : I ↝ J} (ϕ ψ : P ↝₂ Q) → Type ℓ
  _≃₂_ ϕ ψ = Poly≃₂ ϕ ψ

  infix 4 _≃₂_

  Poly-ua₂ : {P Q : I ↝ J} (ϕ ψ : P ≃₁ Q) → (fst ϕ) ≃₂ (fst ψ) → Poly-ua ϕ ≡ Poly-ua ψ
  Poly-ua₂ ϕ ψ e = {!!}

-- induced functor
⟦_⟧ : ∀ {ℓ ℓ'} → {I J : Type ℓ} → Poly I J → (I → Type ℓ') → (J → Type (lmax ℓ ℓ'))
⟦_⟧ {I = I} P X j = Σ (Op P j) (λ c → (i : I) → (p : Pm P i c) → (X i))

-- 1-dimensional structure

_·_ : ∀ {ℓ} → {I J K : Type ℓ} → Poly I J → Poly J K → Poly I K
Op (P · Q) = ⟦ Q ⟧ (Op P)
Pm (_·_ {J = J} P Q) i (c , a) = Σ J (λ j → Σ (Pm Q j c) (λ p → Pm P i (a j p)))

infixr 40 _·_

Id : {I : Type₀} → Poly I I
Op Id i = ⊤
Pm Id i {j = j} tt = i ≡ j

unit-l : {I J : Type₀} (P : I ↝ J) → (Id · P) ↝₂ P
Op→ (unit-l P) (c , a) = c
Pm≃ (unit-l P) = qinv (λ { (i , p , refl) → p }) (λ p → _ , p , refl) (λ { (i , p , refl) → refl }) (λ _ → refl)

unit-l-≃ : {I J : Type₀} (P : I ↝ J) → (Id · P) ≃₁ P
unit-l-≃ P = unit-l P , λ {j} → qinv-to-equiv ((λ c → c , λ i p → tt) , (λ _ → refl) , λ _ → refl)

unit-r : {I J : Type₀} → (P : I ↝ J) → (P · Id) ↝₂ P
Op→ (unit-r P) (tt , a) = a _ refl
Pm≃ (unit-r P) = qinv (λ { (j , refl , p) → p }) (λ p → _ , refl , p) (λ { (j , refl , _) → refl }) (λ _ → refl)

unit-r-≃ : {I J : Type₀} → (P : I ↝ J) → (P · Id) ≃₁ P
unit-r-≃ P = (unit-r P) , qinv-to-equiv ((λ c → tt , (λ { _ refl → c })) , (λ { (tt , a) → Σ-ext refl (funext2 λ { _ refl → refl }) }) , ∼-refl)

assoc : ∀ {ℓ} {I J K L : Type ℓ} (P : Poly I J) (Q : Poly J K) (R : Poly K L) → ((P · Q) · R) ↝₂ (P · (Q · R))
Op→ (assoc P Q R) (c , a) = (c , (λ k r → fst (a k r))) , (λ { j (k , r , q) → snd (a k r) j q })
Pm≃ (assoc P Q R) = qinv
  (λ { (k , r , j , q , p) → j , (k , r , q) , p })
  (λ { (j , (k , r , q) , p) → k , r , j , q , p })
  (λ _ → refl)
  (λ _ → refl)

assoc-≃ : ∀ {ℓ} {I J K L : Type ℓ} (P : I ↝ J) (Q : J ↝ K) (R : K ↝ L) → ((P · Q) · R) ≃₁ (P · (Q · R))
assoc-≃ P Q R = assoc P Q R , λ {j} → qinv-to-equiv ((λ { ((c , a) , b) → c , (λ k r → a k r , λ j q → b j (k , r , q)) }) , (λ _ → refl) , λ _ → refl)

-- 2-dimensional structure

_·₂_ : ∀ {ℓ} {I J : Type ℓ} {P Q R : I ↝ J} (ϕ : P ↝₂ Q) (ψ : Q ↝₂ R) → P ↝₂ R
Op→ (ϕ ·₂ ψ) c = Op→ ψ (Op→ ϕ c)
Pm≃ (ϕ ·₂ ψ) = ≃-trans (Pm≃ ϕ) (Pm≃ ψ)

infixr 30 _·₂_

ID : ∀ {ℓ} {I J : Type ℓ} (P : I ↝ J) → P ↝₂ P
Op→ (ID P) c = c
Pm≃ (ID P) = ≃-refl

unit-l₂ : ∀ {ℓ} {I J : Type ℓ} {P Q : I ↝ J} (ϕ : P ↝₂ Q) → ID P ·₂ ϕ ≃₂ ϕ
Op≃₂ (unit-l₂ ϕ) c = refl
Pm≃₂ (unit-l₂ ϕ) p = refl

unit-r₂ : ∀ {ℓ} {I J : Type ℓ} {P Q : I ↝ J} (ϕ : P ↝₂ Q) → ϕ ·₂ ID Q ≃₂ ϕ
Op≃₂ (unit-r₂ ϕ) c = refl
Pm≃₂ (unit-r₂ ϕ) p = refl

assoc₂ : ∀ {ℓ} {I J : Type ℓ} {P Q R S : I ↝ J} (ϕ : P ↝₂ Q) (χ : Q ↝₂ R) (ψ : R ↝₂ S) → (ϕ ·₂ χ) ·₂ ψ ≃₂ ϕ ·₂ (χ ·₂ ψ)
Op≃₂ (assoc₂ ϕ χ ψ) c = refl
Pm≃₂ (assoc₂ ϕ χ ψ) p = refl

-- NB: this is not true for arbitrary morphisms, we at least need to have cartesian morphisms
_↝₂·_ : ∀ {ℓ} {I J K : Type ℓ} {P P' : Poly I J} {Q Q' : Poly J K} → P ↝₂ P' → Q ↝₂ Q' → P · Q ↝₂ P' · Q'
Op→ (_↝₂·_ ϕ ψ) (c , a) = (Op→ ψ c , λ j p → Op→ ϕ (a j (Pm← ψ p)))
Pm≃ (_↝₂·_ {P' = P'} ϕ ψ) {i = i} {c = c , a} = Σ-≃ ≃-refl (λ j → Σ-≃ (Pm≃ ψ) (λ q → ≃-trans (Pm≃ ϕ) (id-to-equiv (ap (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q))))))
-- Pm≃ (_↝₂·_ {P' = P'} ϕ ψ) {i = i} {c = c} = Σ-≃ ≃-refl (λ j → Σ-≃ (Pm≃ ψ) (λ p → ≃-trans (Pm≃ ϕ) {!!}))

↝₂·-Pm→ : ∀ {ℓ} {I J K : Type ℓ} {P P' : I ↝ J} {Q Q' : J ↝ K} (ϕ : P ↝₂ P') (ψ : Q ↝₂ Q')
          {i : I} (j : J) {k : K} {c : Op Q k} {a : (j : J) → Pm Q j c → Op P j} (q : Pm Q j c) (p : Pm P i (a j q)) →
          Pm→ (ϕ ↝₂· ψ) {c = c , a} (j , q , p) ≡ (j , Pm→ ψ q , coe (ap (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q))) (Pm→ ϕ p))
↝₂·-Pm→ ϕ ψ j q p = refl

ID↝₂ID : ∀ {ℓ} {I J K : Type ℓ} (P : I ↝ J) (Q : J ↝ K) → ID P ↝₂· ID Q ≃₂ ID (P · Q)
Op≃₂ (ID↝₂ID P Q) (c , a) = refl
Pm≃₂ (ID↝₂ID P Q) (j , q , p) = refl

---- commented because it takes too long to compile
-- xch : ∀ {ℓ} {I J K : Type ℓ} {P P' P'' : I ↝ J} {Q Q' Q'' : J ↝ K} (ϕ : P ↝₂ P') (ϕ' : P' ↝₂ P'') (ψ : Q ↝₂ Q') (ψ' : Q' ↝₂ Q'') →
      -- (ϕ ·₂ ϕ') ↝₂· (ψ ·₂ ψ') ≃₂ (ϕ ↝₂· ψ) ·₂ (ϕ' ↝₂· ψ')
-- Op≃₂ (xch ϕ ϕ' ψ ψ') (c , a) = refl
-- Pm≃₂ (xch {P' = P'} {P'' = P''} ϕ ϕ' ψ ψ') {i} {k} {c , a} (j , q , p) = Σ-ext refl (Σ-ext refl lem)
  -- where
  -- lem : coe (ap (λ q → Pm P'' i (Op→ (ϕ ·₂ ϕ') (a j q))) (sym (Pmη (ψ ·₂ ψ') q))) (Pm→ (ϕ ·₂ ϕ') p) ≡ coe (ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q)))) (Pm→ ϕ' (coe (ap (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q))) (Pm→ ϕ p)))
  -- lem = begin
    -- coe (ap (λ q → Pm P'' i (Op→ (ϕ ·₂ ϕ') (a j q))) (sym (Pmη (ψ ·₂ ψ') q))) (Pm→ (ϕ ·₂ ϕ') p) ≡⟨ refl ⟩
    -- coe (ap (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη (ψ ·₂ ψ') q))) (Pm→ ϕ' (Pm→ ϕ p)) ≡⟨ ap (λ f → f (Pm→ (ϕ ·₂ ϕ') p)) (coe-ap (λ q → Pm P'' i (Op→ (ϕ ·₂ ϕ') (a j q))) (sym (Pmη (ψ ·₂ ψ') q))) ⟩
    -- transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη (ψ ·₂ ψ') q)) (Pm→ ϕ' (Pm→ ϕ p)) ≡⟨ ap (λ P → transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym P) (Pm→ ϕ' (Pm→ ϕ p))) (≃η-trans (Pm≃ ψ) (Pm≃ ψ') q) ⟩
    -- transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (trans (ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q))) (Pmη ψ q))) (Pm→ ϕ' (Pm→ ϕ p)) ≡⟨ ap (λ P → transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) P (Pm→ ϕ' (Pm→ ϕ p))) (∙-sym (ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q))) (Pmη ψ q)) ⟩
    -- transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (trans (sym (Pmη ψ q)) (sym (ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q))))) (Pm→ ϕ' (Pm→ ϕ p)) ≡⟨ transport-∙ (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (sym (ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q)))) (Pm→ ϕ' (Pm→ ϕ p)) ⟩
    -- transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q')))) (sym (ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q)))) (transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (Pm→ ϕ' (Pm→ ϕ p))) ≡⟨ ap (λ P → transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q')))) P (transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (Pm→ ϕ' (Pm→ ϕ p)))) (sym-ap (Pm← ψ) (Pmη ψ' (Pm→ ψ q))) ⟩
    -- transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q')))) (ap (Pm← ψ) (sym (Pmη ψ' (Pm→ ψ q)))) (transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (Pm→ ϕ' (Pm→ ϕ p))) ≡⟨ ! (transport-ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q')))) (Pm← ψ) (sym (Pmη ψ' (Pm→ ψ q))) (transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (Pm→ ϕ' (Pm→ ϕ p)))) ⟩
    -- transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q))) (transport (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (sym (Pmη ψ q)) (Pm→ ϕ' (Pm→ ϕ p))) ≡⟨ ap (transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q)))) (transport-nat (λ q → Pm P' i (Op→ ϕ (a j q))) (λ q → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j q)))) (Pm→ ϕ') (sym (Pmη ψ q)) (Pm→ ϕ p)) ⟩
    -- transport (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q))) (Pm→ ϕ' (transport (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q)) (Pm→ ϕ p))) ≡⟨ ap (λ f → f (Pm→ ϕ' (transport (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q)) (Pm→ ϕ p)))) (! coe-ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q))))  ⟩
    -- coe (ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q)))) (Pm→ ϕ' (transport (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q)) (Pm→ ϕ p))) ≡⟨ ap (λ f →  coe (ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q)))) (Pm→ ϕ' (f (Pm→ ϕ p)))) (! coe-ap (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q))) ⟩
    -- coe (ap (λ q' → Pm P'' i (Op→ ϕ' (Op→ ϕ (a j (Pm← ψ q'))))) (sym (Pmη ψ' (Pm→ ψ q)))) (Pm→ ϕ' (coe (ap (λ q → Pm P' i (Op→ ϕ (a j q))) (sym (Pmη ψ q))) (Pm→ ϕ p))) ∎

infixr 30 _↝₂·_

_↝₂·l_ : ∀ {ℓ} {I J K : Type ℓ} {P P' : I ↝ J} → P ↝₂ P' → (Q : J ↝ K) → P · Q ↝₂ P' · Q
_↝₂·l_ ϕ Q = ϕ ↝₂· ID Q

_↝₂·r_ : ∀ {ℓ} {I J K : Type ℓ} (P : I ↝ J) {Q Q' : J ↝ K} → Q ↝₂ Q' → P · Q ↝₂ P · Q'
_↝₂·r_ P ψ = ID P ↝₂· ψ

infixr 30 _↝₂·l_
infixr 30 _↝₂·r_

triangle : {I J K : Type₀} (P : I ↝ J) (Q : J ↝ K) →
           assoc P Id Q ·₂ (ID P ↝₂· unit-l Q) ≃₂ unit-r P ↝₂·l Q
Op≃₂ (triangle P Q) (c , a) = refl
Pm≃₂ (triangle P Q) (j , q , .j , refl , p) = refl

pentagon : ∀ {ℓ} {I J K L M : Type ℓ} (P : I ↝ J) (Q : J ↝ K) (R : K ↝ L) (S : L ↝ M) →
           ((assoc P Q R ↝₂·l S) ·₂ assoc P (Q · R) S ·₂ (P ↝₂·r assoc Q R S)) ≃₂ (assoc (P · Q) R S ·₂ assoc P Q (R · S))
Op≃₂ (pentagon P Q R S) (c , a) = refl
Pm≃₂ (pentagon P Q R S) (l , s , k , r , j , q , p) = refl

≃₁-refl : ∀ {ℓ} {I J : Type ℓ} {P : I ↝ J} → P ≃₁ P
≃₁-refl {P = P} = ID P , id-is-equiv

id-to-≃₁ : ∀ {ℓ} {I J : Type ℓ} {P Q : I ↝ J} → P ≡ Q → P ≃₁ Q
id-to-≃₁ refl = ≃₁-refl

_≃₁-·_ : ∀ {ℓ} {I J K : Type ℓ} {P P' : I ↝ J} {Q Q' : J ↝ K} → P ≃₁ P' → Q ≃₁ Q' → (P · Q) ≃₁ (P' · Q')
-- (ϕ , ϕ≃) ≃₁-· (ψ , ψ≃) = ϕ ↝₂· ψ , λ {k} → qinv-to-equiv ({!!} , {!!})
_≃₁-·_ {_} {_} {_} {K} {P} {P'} {Q} {Q'} (ϕ , ϕ≃) (ψ , ψ≃) = ϕ ↝₂· ψ , λ {k} → qinv-to-equiv ({!f!} , {!!})
  where
  f : {k : K} → ⟦ Q' ⟧ (Op P') k → ⟦ Q ⟧ (Op P) k
  f {k} (c , p) = ≃← (equiv (ψ≃ {k})) c , (λ j q → (≃← (equiv (ϕ≃ {j}))) (p j {!!}))

_≃₁·_ : ∀ {ℓ} {I J : Type ℓ} {P Q R : I ↝ J} → P ≃₁ Q → Q ≃₁ R → P ≃₁ R
(ϕ , ϕ≃) ≃₁· (ψ , ψ≃) = ϕ ·₂ ψ , ∘-is-equiv ϕ≃ ψ≃

≃₁-trans = _≃₁·_

Poly-ua-· : ∀ {ℓ} {I J : Type ℓ} {P Q R : I ↝ J} (ϕ : P ≃₁ Q) (ψ : Q ≃₁ R) → Poly-ua (ϕ ≃₁· ψ) ≡ Poly-ua ϕ ∙ Poly-ua ψ
Poly-ua-· ϕ ψ = {!!}

-- cartesian product

infixr 50 _⊕_
_⊕_ : {I I' J J' : Type₀} → I ↝ J → I' ↝ J' → (I ⊔ I') ↝ (J ⊔ J')
Op (P ⊕ Q) (inl j)  = Op P j
Op (P ⊕ Q) (inr j') = Op Q j'
Pm (P ⊕ Q) (inl i)  {inl j}  c = Pm P i c
Pm (P ⊕ Q) (inl i)  {inr j'} c = ⊥
Pm (P ⊕ Q) (inr i') {inl j}  c = ⊥
Pm (P ⊕ Q) (inr i') {inr j'} c = Pm Q i' c

-- _⊕₂_ : {I I' J J' : Type₀} {P Q : I ↝ J} {P' Q' : I' ↝ J'} (ϕ : P ↝₂ Q) (ϕ' : P' ↝₂ Q')  → (P ⊕ P') ↝₂ (Q ⊕ Q')
-- Op→ (ϕ ⊕₂ ϕ') {inl j } c = Op→ ϕ c
-- Op→ (ϕ ⊕₂ ϕ') {inr j'} c = Op→ ϕ' c
-- Pm≃ (ϕ ⊕₂ ϕ') {inl i } {inl i'} = Pm≃ ϕ
-- Pm≃ (ϕ ⊕₂ ϕ') {inl i } {inr j'} = ≃-refl
-- Pm≃ (ϕ ⊕₂ ϕ') {inr j'} {inl i } = ≃-refl
-- Pm≃ (ϕ ⊕₂ ϕ') {inr j } {inr j'} = Pm≃ ϕ'

-- ⊕₂-id : {I I' J J' : Type₀} {P : I ↝ J} {P' : I' ↝ J'} → ID P ⊕₂ ID P' ≃₂ ID (P ⊕ P')
-- Op≃₂ ⊕₂-id {inl j } c = refl
-- Op≃₂ ⊕₂-id {inr j'} c = refl
-- Pm≃₂ ⊕₂-id {inl _} {inl _} p = refl
-- Pm≃₂ ⊕₂-id {inr _} {inr _} p = refl

-- ⊕₂-·₂ : {I I' J J' : Type₀} {P Q R : I ↝ J} {P' Q' R' : I' ↝ J'} (ϕ : P ↝₂ Q) (ψ : Q ↝₂ R) (ϕ' : P' ↝₂ Q') (ψ' : Q' ↝₂ R') →
--         (ϕ ·₂ ψ) ⊕₂ (ϕ' ·₂ ψ') ≃₂ (ϕ ⊕₂ ϕ') ·₂ (ψ ⊕₂ ψ')
-- Op≃₂ (⊕₂-·₂ ϕ ψ ϕ' ψ') {inl _} c = refl
-- Op≃₂ (⊕₂-·₂ ϕ ψ ϕ' ψ') {inr _} c = refl
-- Pm≃₂ (⊕₂-·₂ ϕ ψ ϕ' ψ') {inl _} {inl _} p = refl
-- Pm≃₂ (⊕₂-·₂ ϕ ψ ϕ' ψ') {inr _} {inr _} p = refl

projl : {I J : Type₀} → (I ⊔ J) ↝ I
Op projl i = ⊤
Pm projl (inl i) {i'} tt = i ≡ i'
Pm projl (inr j) {i'} tt = ⊥

projr : {I J : Type₀} → (I ⊔ J) ↝ J
Op projr i = ⊤
Pm projr (inl i) {j'} tt = ⊥
Pm projr (inr j) {j'} tt = j ≡ j'

diag : {I : Type₀} → I ↝ (I ⊔ I)
Op diag i = ⊤
Pm diag i {inl i'} tt = i ≡ i'
Pm diag i {inr i'} tt = i ≡ i'

-- prod-ext : {I J K : Type₀} → (P : I ↝ (J ⊔ K)) → P ≃₁ (diag · (P · projl) ⊕ (P · projr))
-- prod-ext P =
--   record {
--     Op→ = λ { {inl j} c → (tt , (λ { (inl j') refl → c })) , λ i p → tt ; {inr k} c → (tt , (λ { (inr k') refl → c })) , λ i p → tt } ;
--     Pm≃ = λ { {i} {inl j} {c} → (λ p → (inl i) , ((inl j , refl , p) , refl)) , qinv-to-equiv ((λ { (inl i , (inl j , refl , p) , refl) → p }) , ∼-refl , λ { (inl i , (inl j , refl , p) , refl) → refl }) ;
--               {i} {inr k} {c} → (λ p → (inr i) , (((inr k) , (refl , p)) , refl)) , qinv-to-equiv ((λ { (inr i , (inr k , refl , p) , refl) → p }) , ∼-refl , λ { (inr i , (inr k , refl , p) , refl) → refl }) }
--     } ,
--     λ { {inl j} → qinv-to-equiv ((λ { ((tt , a) , b) → a (inl j) refl }) , (λ c → refl) , λ { ((tt , a) , b) → Σ-ext (Σ-ext refl (funext λ { (inl j) → funext λ { refl → refl } ; (inr k) → funext λ { () } })) (funext λ { _ → refl }) }) ; {inr k} → qinv-to-equiv ((λ { ((tt , a) , b) → a (inr k) refl }) , (λ c → refl) , λ { ((tt , a) , b) → Σ-ext (Σ-ext refl (funext (λ { (inl j) → funext λ { () } ; (inr k) → funext λ { refl → refl }}))) (funext λ x → refl) }) }

-- prod-l : {I J K : Type₀} (P : I ↝ J) (Q : I ↝ K) → (diag · (P ⊕ Q)) · projl ≃₁ P
-- prod-l P Q = (record { Op→ = λ { {j} (tt , a) → fst (a (inl j) refl) } ; Pm≃ = λ { {i} {j} {tt , a} → (λ { (inl j , refl , inl i , p , refl) → p }) , qinv-to-equiv ((λ p → inl j , refl , ((inl i) , (p , refl))) , (λ { (inl j , refl , inl i , p , refl) → refl }) , ∼-refl) } }) , λ {j} → qinv-to-equiv ((λ c → tt , (λ { (inl j) refl → c , λ i p → tt})) , (λ { (tt , a) → Σ-ext refl (funext λ { (inl j) → funext λ { refl → refl } ; (inr k) → funext λ () }) }) , λ c → refl)

-- prod-r : {I J K : Type₀} (P : I ↝ J) (Q : I ↝ K) → (diag · (P ⊕ Q)) · projr ≃₁ Q
-- prod-r P Q = (record { Op→ = λ { {k} (tt , a) → fst (a (inr k) refl) } ; Pm≃ = λ { {i} {k} {tt , a} → (λ { (inl j , () , inl i , p , refl) ; (inr k , refl , inl i , () , refl) ; (inr k , refl , inr i , p , refl) → p }) , qinv-to-equiv ((λ q → inr k , refl , ((inr i) , (q , refl))) , (λ { (inr k , refl , inr i , q , refl) → refl }) , ∼-refl) } }) , λ {j} → qinv-to-equiv ((λ c → tt , (λ { (inr k) refl → c , (λ i p → tt) })) , (λ { (tt , a) → Σ-ext refl (funext λ { (inl j) → funext λ () ; (inr k) → funext λ { refl → refl } }) }) , λ c → refl)

-- prod : {I J K : Type₀} → I ↝ (J ⊔ K) ≡ ((I ↝ J) × (I ↝ K))
-- prod = ua (qinv (λ { P → P · projl , P · projr }) (λ { (P , Q) → diag · P ⊕ Q }) (λ { P → Poly-ua (≃₁-sym (prod-ext P)) }) λ { (P , Q) → Σ-ext (Poly-ua (prod-l P Q)) (Poly-ua (≃₁-trans (id-to-≃₁ {!lem P Q!}) (prod-r P Q))) })
--   where
--   -- using this lemma takes lots of time (but is manageable with the abstract in HoTT now
--   -- lem : {I J K : Type₀} (P : I ↝ J) (Q : I ↝ K) → transport (λ v → Poly I K) (Poly-ua (prod-l P Q)) (snd (((λ { ϕ → ϕ · projl , ϕ · projr }) ∘ (λ { (P , Q) → diag · P ⊕ Q })) (P , Q))) ≡ (diag · P ⊕ Q) · projr
--   lem : {I J K : Type₀} (P : I ↝ J) (Q : I ↝ K) → transport (λ v → Poly I K) (Poly-ua (prod-l P Q)) ((diag · P ⊕ Q) · projr) ≡ (diag · P ⊕ Q) · projr
--   lem P Q = transport-cst (Poly-ua (prod-l P Q)) ((diag · P ⊕ Q) · projr)

--- Trying definitions via pairing

module _ {I J K : Type₀} where

  pair : (I ↝ J) → (I ↝ K) → I ↝ (J ⊔ K)
  Op (pair P Q) (inl j) = Op P j
  Op (pair P Q) (inr k) = Op Q k
  Pm (pair P Q) i {inl j} c = Pm P i c
  Pm (pair P Q) i {inr k} c = Pm Q i c

  prod-ext : (P : I ↝ (J ⊔ K)) → P ≃₁ pair (P · projl) (P · projr)
  prod-ext P = (record {
    Op→ = λ { {inl j} c → tt , λ { (inl j) refl → c } ; {inr k} c → tt , (λ { (inr k) refl → c }) } ;
    Pm≃ = λ { {i} {inl j} {c} → qinv (λ p → (inl j) , (refl , p)) (λ { (inl j , refl , p) → p }) (λ p → refl) (λ { (inl j , refl , p) → refl }) ; {i} {inr k} {c} → qinv (λ p → (inr k) , (refl , p)) (λ { (inr k , refl , p) → p }) (λ p → refl) (λ { (inr k , refl , p) → refl }) } }) ,
    (λ { {inl j} → qinv-to-equiv ((λ { (tt , c) → c (inl j) refl }) , (λ p → refl) , λ { (tt , c) → Σ-ext refl (funext2 (λ { (inl j) refl → refl })) }) ; {inr k} → qinv-to-equiv ((λ { (tt , c) → c (inr k) refl }) , (λ c → refl) , λ { (tt , c) → Σ-ext refl (funext2 (λ { (inr k) refl → refl })) }) })

  prod-l : (P : I ↝ J) (Q : I ↝ K) → pair P Q · projl ≃₁ P
  prod-l P Q = (record { Op→ = λ { {j} (tt , c) → c (inl j) refl } ; Pm≃ = λ { {i} {j} {tt , c} → qinv (λ { (inl j , refl , p) → p }) (λ p → inl j , refl , p) (λ { (inl j , refl , p) → refl }) (λ _ → refl)}}) , λ {j} → qinv-to-equiv ((λ c → tt , λ { (inl j) refl → c }) , (λ { (tt , c) → Σ-ext refl (funext2 (λ { (inl j) refl → refl })) }) , λ c → refl)

  prod-r : (P : I ↝ J) (Q : I ↝ K) → pair P Q · projr ≃₁ Q
  prod-r P Q = (record { Op→ = λ { {k} (tt , c) → c (inr k) refl } ; Pm≃ = λ { {i} {k} {tt , c} → qinv (λ { (inr k , refl , p) → p }) (λ p → inr k , refl , p) (λ { (inr k , refl , p) → refl }) λ _ → refl } }) , λ {k} → qinv-to-equiv (((λ c → tt , λ { (inr k) refl → c }) , (λ { (tt , c) → Σ-ext refl (funext2 (λ { (inr k) refl → refl })) }) , λ c → refl))

  prod : I ↝ (J ⊔ K) ≡ ((I ↝ J) × (I ↝ K))
  prod = ua (qinv (λ P → (P · projl) , (P · projr)) (λ { (P , Q) → pair P Q }) (λ P → ! Poly-ua (prod-ext P)) (λ { (P , Q) → ×-ext (Poly-ua (prod-l P Q)) (Poly-ua (prod-r P Q)) }))

-- pair P Q ≃₁ pair (pair P Q · projl) (pair P Q · projr) ≃₁ pair P Q
-- zag : ∀ {I J J' K K' : Type₀} (P : I ↝ (J ⊔ J')) (Q : I ↝ (K ⊔ K')) → ({!prod-ext P!} ≃₁· {!!}) ≡ {!!}
-- zag P Q = {!!}

-- -- TODO: can we define this for not endofunctors?
-- infixr 60 _⊗_
-- _⊗_ : ∀ {ℓ} → {I I' : Type ℓ} → Poly I I → Poly I' I' → Poly (I × I') (I × I')
-- Op (P ⊗ Q) (i , i') = Op P i ⊔ Op Q i'
-- Pm (P ⊗ Q) {i , i'} (inl f) = Pm P f
-- Pm (P ⊗ Q) (inr f') = Pm Q f'
-- St (P ⊗ Q) {i , i'} {inl f} p = St P p , i'
-- St (P ⊗ Q) {i , i'} {inr f'} p = i , St Q p
