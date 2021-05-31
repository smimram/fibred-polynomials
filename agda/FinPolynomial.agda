{-# OPTIONS --without-K --rewriting #-}

-- finite polynomials

module FinPolynomial where

open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import HoTT
open import Polynomial
open import FinType
open import Bij
open ≡-Reasoning

import Bij as 𝔹
open 𝔹 using (𝔹)

finite-groupoid : ∀ {ℓ} (I : Type ℓ) → Type ℓ
finite-groupoid I = (i j : I) → is-finite (i ≡ j)

--- this definition is not very satisfactory: polynomial do not compose without futher assumptions
-- is-finite : ∀ {ℓ} {I J : Type ℓ} (P : I ↝ J) → Type ℓ
-- is-finite {I = I} {J = J} P = (i : I) {j : J} (c : Op P j) → FT.is-finite (Pm P i c)

-- --- note: we need our types to be decidable
-- -- finite-id : {I : Type₀} → is-dec-≡ I → is-finite (Id {I = I})
-- -- finite-id D i {j} c with D i j
-- -- ... | inl y = {!!}
-- -- ... | inr refl = 1 , qinv (λ _ → zero) (λ _ → refl) (λ p → {!!}) (λ { zero → refl })

-- finite-id : {I : Type₀} → finite-groupoid I → is-finite (Id {I = I})
-- finite-id F i {j} tt = F i j

-- finite-comp : {I J K : Type₀} {P : I ↝ J} {Q : J ↝ K} → is-finite P → is-finite Q → is-finite (P · Q)
-- -- finite-comp {I} {J} {K} {P} {Q} FP FQ i c = Σ-is-finite J (λ j → Σ (Pm Q j (fst c)) (λ p → Pm P i (snd c j p))) {!!} (λ j → Σ-is-finite (Pm Q j (fst c)) (λ p → Pm P i (snd c j p)) (FQ j (fst c)) (λ q → FP i (snd c j q)))

is-finite-pol : ∀ {ℓ} {I J : Type ℓ} (P : I ↝ J) → Type ℓ
is-finite-pol {I = I} {J = J} P = {j : J} (c : Op P j) → is-finite (Σ I (λ i → Pm P i c))

_↝f_ : ∀ {ℓ} (I J : Type ℓ) → Type (lsuc ℓ)
I ↝f J = Σ (Poly I J) is-finite-pol

finite-id : {I : Type₀} → is-finite-pol (Id {I = I})
finite-id {j = j} c = is-contr-is-finite ((j , refl) , λ { (i , refl) → refl })

finite-comp :
  {I J K : Type₀} {P : I ↝ J} {Q : J ↝ K} →
  is-finite-pol P → is-finite-pol Q → is-finite-pol (P · Q)
finite-comp {I} {J} {K} {P} {Q} FP FQ (c , a) = transport-≃-finite {A = A} Af (qinv f g g∘f f∘g)
  where
  A : Set
  A = Σ (Σ J (λ j → Pm Q j c)) λ { (j , b ) → Σ I λ i → Pm P i (a j b)}
  Af : is-finite A
  Af = Σ-is-finite (FQ c) (λ { (j , b) → FP (a j b) })
  f : Σ I (λ (i : I) → Pm (P · Q) i (c , a)) → A
  f (i , j , pQ , pP) =  ( j , pQ) , i , pP
  g : A → Σ I (λ (i : I) → Pm (P · Q) i (c , a))
  g (( j , pQ) , i , pP) = (i , j , pQ , pP)
  g∘f : (x : Σ I (λ (i : I) → Pm (P · Q) i (c , a))) → (g (f x) ≡ x)
  g∘f (_ , _ , _ , _) = refl
  f∘g : (x : A) → (f (g x) ≡ x)
  f∘g (( _ , _) , _ , _) = refl

--- the following lemma is wrong
-- inl-is-dec : {A B : Type₀} → is-dec (A ⊔ B) → is-dec A
-- inl-is-dec (inl k) = inl (λ a → k (inl a))
-- inl-is-dec (inr (inl a)) = inr a
-- inl-is-dec (inr (inr b)) = {!!} -- failed :(

-- TODO: we could also use Σ-⊔ along with suitable transports
Σ-Fin-suc : ∀ {ℓ} {n : ℕ} {P : Fin (suc n) → Type ℓ} → Σ (Fin (suc n)) P ≃ (P zero ⊔ Σ (Fin n) (P ∘ suc))
Σ-Fin-suc {_} {n} {P} = qinv f g (λ { (zero , Pi) → refl ; (suc i , Pi) → refl}) (λ { (inl x) → refl ; (inr y) → refl })
  where
  f : Σ (Fin (suc n)) P → (P zero ⊔ Σ (Fin n) (P ∘ suc))
  f (zero ,  Pi) = inl Pi
  f (suc i , Pi) = inr (i , Pi)
  g : (P zero ⊔ Σ (Fin n) (P ∘ suc)) → Σ (Fin (suc n)) P
  g (inl Pz) = zero , Pz
  g (inr (i , Pi)) = (suc i) , Pi

-- decidable subsets of finite sets are finite sets
Fin-sub : {n : ℕ} (P : Fin n → Type₀) → ((i : Fin n) → is-prop (P i)) → ((i : Fin n) → is-dec (P i)) → Σ ℕ (λ k → Σ (Fin n) P ≃ Fin k)
Fin-sub {zero}  P R D = zero , qinv (λ ()) (λ ()) (λ ()) (λ ())
Fin-sub {suc _} P R D with D zero | Fin-sub (P ∘ suc) (λ i → R (suc i)) (λ i → D (suc i))
... | inl ¬Pz | n , F = n ,
  Σ (Fin (suc _)) P ≃⟨ Σ-Fin-suc ⟩
  (P zero ⊔ Σ (Fin _) (P ∘ suc)) ≃⟨ ≃-⊔ (is-empty-≃-⊥ ¬Pz) F ⟩
  (⊥ ⊔ Fin n) ≃⟨ ⊔-unit-l ⟩
  Fin n ≃∎
... | inr Pz  | n , F = (suc n) ,
  Σ (Fin (suc _)) P ≃⟨ Σ-Fin-suc ⟩
  ((P zero) ⊔ (Σ (Fin _) (P ∘ suc))) ≃⟨ ≃-⊔ (is-contr-≃-⊤ (Pz , (λ x → R zero Pz x))) F ⟩
  (⊤ ⊔ Fin n) ≃⟨ ≃-sym (Fin-Suc n) ⟩
  Fin (suc n) ≃∎

ap-Σ-l : ∀ {i j} {A A' : Type i} {B : A → Type j} (p : A' ≡ A) → Σ A B ≡ Σ A' (B ∘ coe p)
ap-Σ-l refl = refl

-- we apparently really need heterogeneous levels for A and A'
-- ≃-Σ-l : ∀ {i i' j} {A : Type i} {A' : Type i'} {B : A → Type j} (e : A ≃ A') → Σ A B ≃ Σ A' (B ∘ ≃← e)
-- ≃-Σ-l {_} {_} {_} {A} {A'} {B} e = qinv f g g-f f-g
--   where
--   f : Σ A B → Σ A' (B ∘ ≃← e)
--   f (a , b) = (≃→ e a) , (transport B (! (≃η e a)) b)
--   g : Σ A' (B ∘ ≃← e) → Σ A B
--   g (a , b) = (≃← e a) , b
--   g-f : (g ∘ f) ∼ id
--   g-f (a , b) = Σ-ext (≃η e a) (begin
--     transport B (≃η e a) (transport B (! (≃η e a)) b) ≡⟨ ! transport-∙ B (! (≃η e a)) (≃η e a) b ⟩
--     transport B (! ≃η e a ∙ ≃η e a) b ≡⟨ ∙-inv-l (≃η e a) |in-ctx (λ p → transport B p b) ⟩
--     b ∎)
--   f-g : (f ∘ g) ∼ id
--   f-g (a , b) = Σ-ext (≃ε e a) (begin
--     transport (B ∘ ≃← e) (≃ε e a) (transport B (! (≃η e (≃← e a))) b) ≡⟨ transport-ap B (≃← e) (≃ε e a) _ ⟩
--     transport B (ap (≃← e) (≃ε e a)) (transport B (! (≃η e (≃← e a))) b) ≡⟨ ! (transport-∙ B (! (≃η e (≃← e a))) (ap (≃← e) (≃ε e a)) b) ⟩
--     transport B (! ≃η e (≃← e a) ∙ ap (≃← e) (≃ε e a)) b ≡⟨ {!!} |in-ctx (λ p → transport B p b) ⟩ -- zig-zag identity
--     b ∎)

-- essentially : Fin-sub ... + transport along f
-- NB : we need ≃-is-finite here which allows transporting finiteness along equivalences of various universes (instead of transport)
finite-sub : ∀ {i} {A : Type i} → is-finite A → (P : A → Type₀) → ((a : A) → is-prop (P a)) → ((a : A) → is-dec (P a)) → is-finite (Σ A P)
finite-sub {_} {A} (n , F) P R D = ∥∥-rec (is-finite-is-prop (Σ A P))
  (λ f → transport-≃-finite (let (k , e) = Fin-sub (P ∘ ≃← f) ((λ i → R (≃← f i))) (λ i → D (≃← f i)) in k ,  ∣ e ∣ ) (≃-sym (Σ-≃-fst (≃-sym f)))) F


--- this is wrong
-- inl-is-finite : (A B : Type₀) → is-finite (A ⊔ B) → is-finite A
-- inl-is-finite A B (n , e) = (∥∥-rec {B = is-finite A} {!!} (λ e → {!lem (λ i → Σ A (λ a → i ≡ ≃→ e (inl a))) ? ?!}) e)

open import Data.Bool

split : ∀ {i} {A B : Type i} → A ⊔ B → Bool
split (inl _) = true
split (inr _) = false

split-ind-l : ∀ {i} {A B : Type i} → A ≃ Σ (A ⊔ B) (λ x → split x ≡ true)
split-ind-l = qinv (λ a → (inl a) , refl) (λ { (inl a , refl) → a }) (λ x → refl) (λ { (inl x , refl) → refl })

inl-is-finite : (A B : Type₀) → (n : ℕ) → (A ⊔ B) ≃ Fin n → is-finite A
inl-is-finite A B n e = fst sub , ∣ ≃-trans split-ind-l (≃-trans (Σ-≃ e eq) (snd sub)) ∣
  where
  P : Fin n → Type₀
  P i = split (≃← e i) ≡ true
  sub : Σ ℕ (λ k → Σ (Fin n) P ≃ Fin k)
  sub = Fin-sub P (λ i → Bool-is-set (split (≃← e i)) true) (λ i → Bool-is-dec-≡ (split (≃← e i)) true)
  eq : (a : A ⊔ B) → (split a ≡ true) ≃ P (≃→ e a)
  eq (inl a) = qinv (λ x → ap split (≃η e (inl a))) (λ _ → refl) (λ x → Bool-is-set true true refl x) (λ x → Bool-is-set _ _ _ _) 
  eq (inr b) = qinv (λ ()) (λ { p → ! ap split (≃η e (inr b)) ∙ p }) (λ ()) (λ x → Bool-is-set _ _ _ _)

Fin-inl : ∀ {i} {A B : Type i} → is-finite (A ⊔ B) → is-finite A
Fin-inl {_} {A} {B} F =
  transport-≃-finite lem  split-ind-l 
  where
  lem : is-finite (Σ (A ⊔ B) (λ x → split x ≡ true))
  lem = finite-sub F (λ x → split x ≡ true) (λ x → Bool-is-set (split x) true) (λ x → Bool-is-dec-≡ (split x) true)

Fin-inr : ∀ {i} {A B : Type i} → is-finite (A ⊔ B) → is-finite B
Fin-inr F = Fin-inl (transport-≃-finite F ⊔-comm)

is-finite-⊔-l : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-finite (Σ (I ⊔ J) P) → is-finite (Σ I (P ∘ inl))
is-finite-⊔-l F = Fin-inl (transport-≃-finite F (≃-sym Σ-⊔))

is-finite-⊔-r : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-finite (Σ (I ⊔ J) P) → is-finite (Σ J (P ∘ inr))
is-finite-⊔-r F = Fin-inr (transport-≃-finite F (≃-sym Σ-⊔))

Σ-⊔-is-finite : ∀ {ℓ} {I J : Type ℓ} {P : (I ⊔ J) → Type ℓ} → is-finite (Σ I (P ∘ inl)) → is-finite (Σ J (P ∘ inr)) → is-finite (Σ (I ⊔ J) P)
Σ-⊔-is-finite FI FJ = transport-≃-finite (⊔-is-finite FI FJ)  Σ-⊔ 

-- ap split (≃η e (inl a))


module _ {I J K : Type₀} where

  Pm-r : (P : (I ⊔ J) ↝f K) {k : K} (c : Op (fst P) k) → FinType
  Pm-r P {k} c = Σ J ((λ i → Pm (fst P) i c) ∘ inr) ,
              is-finite-⊔-r ((snd P) c)  

  op-to-exp : (P : (I ⊔ J) ↝f K) {k : K} (c : Op (fst P) k) → Exp J
  op-to-exp P c = ≃← 𝔹≃FinType (Pm-r P c) ,
                  (λ p → fst (coe (ap fst (≃ε 𝔹≃FinType (Pm-r P c))) p))

  curry : (I ⊔ J) ↝f K → I ↝f (Exp J × K)
  curry (P , Pf) = Q , Qf
    where
    Q : Poly I (Exp J × K)
    Op Q (expj , k) = Σ (Op P k) (λ c → op-to-exp (P , Pf) c ≡ expj)
    Pm Q i {(b , f) , k} (c , e) = Pm P (inl i) c 
    Qf : is-finite-pol Q
    Qf {(b , f) , k} (c , e) = is-finite-⊔-l {I = I} {J = J} (Pf c) 

  uncurry : I ↝f (Exp J × K) → (I ⊔ J) ↝f K
  uncurry (P , Pf) = Q , Qf
    where
    Q : Poly (I ⊔ J) K
    Op Q k = Σ (Exp J) (λ jj → Op P (jj , k))
    Pm Q (inl i) (jj , c) = Pm P i c
    Pm Q (inr j) (jj , c) = Σ (𝔹-to-Fin (fst jj)) (λ p → snd jj p ≡ j)
    Qf : is-finite-pol Q
    Qf ((b , f) , c) = Σ-⊔-is-finite (Pf c) (transport-≃-finite (snd (≃→ 𝔹≃FinType b)) e  )
      where
      e : Σ J (λ j → Σ (𝔹-to-Fin b) (λ p → f p ≡ j)) ≃ 𝔹-to-Fin b
      e = qinv (λ { (.(_) , B , refl) → B }) (λ k → f k , k , refl) (λ { (_ , _ , refl) → refl }) (λ x → refl)

  -- This should work but there is an issue with universe levels?
  -- _↝₂f_ : ∀ {ℓ} (I J : Type ℓ) (P Q : I ↝f J) → Type (lsuc ℓ)
  -- P ↝₂f Q = (fst P) ↝₂ (fst Q)
