{-# OPTIONS --without-K --allow-unsolved-metas #-}

module FinType where

open import HoTT
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (fold ; lift)

open ≡-Reasoning

Fin-is-set : (n : ℕ) → is-set (Fin n)
Fin-is-set (suc _) zero zero refl refl = refl
Fin-is-set (suc n) (suc i) (suc j) p q = begin
  p ≡⟨ ! suc-pred p ⟩
  ap suc (ppred p) ≡⟨ ap (ap suc) (Fin-is-set n i j (ppred p) (ppred q)) ⟩
  ap suc (ppred q) ≡⟨ suc-pred q ⟩
  q ∎
  where
  ppred : {n : ℕ} {i j : Fin n} (p : Fin.suc i ≡ Fin.suc j) → i ≡ j
  ppred refl = refl
  suc-pred : {n : ℕ} {i j : Fin n} (p : suc i ≡ suc j) → ap suc (ppred p) ≡ p
  suc-pred refl = refl

module Bad where
  -- problem: we get a large type...
  -- + we want a property
  -- rem: if n exists it is finite, we can thus avoid truncating everything and keep the Σ
  is-finite : Type₀ → Type₁
  is-finite A = Σ ℕ (λ n → A ≡ Fin n)

  FinType : Type₁
  FinType = Σ Type₀ is-finite

  FinType≃ℕ : FinType ≃ ℕ
  FinType≃ℕ = qinv (λ { (_ , n , _) → n }) (λ n → Fin n , n , refl) (λ { (.(Fin n) , n , refl) → refl }) (λ n → refl)

  ⊥-is-finite : is-finite ⊥
  ⊥-is-finite = 0 , ua (qinv (λ ()) (λ ()) (λ ()) (λ ()))

-- remark: we need an equivalence (as opposed to an equality) here in order to
-- keep the type small (i.e. in Type₀ when the input is in Type₀)
is-finite : ∀ {i} → Type i → Type i
is-finite A = Σ ℕ (λ n → ∥ A ≃ Fin n ∥)

is-finite-is-set : ∀ {i} {A : Type i} → is-finite A → is-set A
is-finite-is-set {A = A} (n , e) = ∥∥-rec (is-set-is-prop A) (λ e → is-set-≃ (≃-sym e) (Fin-is-set n)) e

Fin-is-finite : (n : ℕ) → is-finite (Fin n)
Fin-is-finite n = n , ∣ ≃-refl ∣

module _ where
  Fin0-is-empty : ¬ (Fin 0)
  Fin0-is-empty ()

  Suc : ∀ {i} (A : Type i) → Type i
  Suc A = ⊤ ⊔ A

  -- is there a general explanation for this "homotopical elimination" property?
  ⊔-helim : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (z : A ⊔ B) → ((x : A) → z ≡ inl x → C) → ((y : B) → z ≡ inr y → C) → C
  ⊔-helim (inl x) f g = f x refl
  ⊔-helim (inr y) f g = g y refl

  inspect : ∀ {i} {A : Type i} (x : A) → Σ A (λ y → x ≡ y)
  inspect x = x , refl

  inr-injective : ∀ {i j} {A : Type i} {B : Type j} {y y' : B} → inr {A = A} y ≡ inr y' → y ≡ y'
  inr-injective refl = refl

  Suc-injective : ∀ {i} {A B : Type i} → Suc A ≡ Suc B → A ≡ B
  Suc-injective {i} {A} {B} p = ua (qinv (f p) (f (! p)) (h p) (transport (λ q → (f q ∘ f (! p)) ∼ id) (!-! p) (h (! p))))
    where
    f : {A B : Type i} (p : Suc A ≡ Suc B) → A → B
    ---- bad way since we have to do all the pattern matching by hand which is a pity
    -- f p x = ⊔-helim (coe p (inr x))
      -- (λ { tt q → ⊔-helim (coe p (inl tt))
        -- (λ { tt r → case coe-injective p (inr x) (inl tt) (q ∙ ! r) of λ () })
        -- (λ y _ → y)
      -- })
      -- (λ y _ → y)
    f p x with inspect (coe p (inr x))
    ... | inr y , _ = y
    ... | inl tt , q with inspect (coe p (inl tt))
    ... | inr y , _ = y
    ... | inl tt , r with coe-injective p (q ∙ ! r)
    ... | ()
    coe-inv-l : ∀ {i} {A B : Type i} (p : A ≡ B) (x : A) → coe (! p) (coe p x) ≡ x
    coe-inv-l p x = happly (! (coe-∙ p (! p))) x ∙ (∙-inv-r p |in-ctx λ p → coe p x)
    h : {A B : Type i} (p : Suc A ≡ Suc B) → (f (! p) ∘ f p) ∼ id
    h p x with inspect (coe p (inr x))
    h p x | inl tt , q with inspect (coe p (inl tt))
    h p x | inl tt , q | inl tt , r with coe-injective p (q ∙ ! r)
    h p x | inl tt , q | inl tt , r | ()
    h p x | inl tt , q | inr y , r with inspect (coe (! p) (inr y))
    h p x | inl tt , q | inr y , r | inl tt , q' with inspect (coe (! p) (inl tt))
    h p x | inl tt , q | inr y , r | inl tt , q' | inl tt , r' with coe-injective (! p) (q' ∙ ! r')
    h p x | inl tt , q | inr y , r | inl tt , q' | inl tt , r' | ()
    h p x | inl tt , q | inr y , r | inl tt , q' | inr x' , r' = inr-injective (! r' ∙ ap (coe (! p)) (! q) ∙ coe-inv-l p (inr x))
    h p x | inl tt , q | inr y , r | inr x' , q' with ! q' ∙ ! (ap (coe (! p)) r) ∙ coe-inv-l p (inl tt)
    h p x | inl tt , q | inr y , r | inr x' , q' | ()
    h p x | inr y , q with inspect (coe (! p) (inr y))
    h p x | inr y , q | inl tt , q' with inspect (coe (! p) (inl tt))
    h p x | inr y , q | inl tt , q' | inl tt , r' with coe-injective (! p) (q' ∙ ! r')
    h p x | inr y , q | inl tt , q' | inl tt , r' | ()
    h p x | inr y , q | inl tt , q' | inr x' , r' with ! q' ∙ ! (ap (coe (! p)) q) ∙ coe-inv-l p (inr x)
    h p x | inr y , q | inl tt , q' | inr x' , r' | ()
    h p x | inr y , q | inr x' , q' = inr-injective (! q' ∙ ap (coe (sym p)) (! q) ∙ coe-inv-l p (inr x))

  -- TODO: peut-on simplifier la preuve dans le cas Fin ?? (pigeonhole dans agda-lib)

  Fin-Suc : (n : ℕ) → Fin (suc n) ≃ Suc (Fin n)
  Fin-Suc n = qinv
    (λ { zero → inl tt ; (suc i) → inr i })
    (λ { (inl tt) → zero ; (inr i) → suc i })
    (λ { zero → refl ; (suc i) → refl })
    (λ { (inl tt) → refl ; (inr i) → refl} )

  data bot (A : Type₀) : Type₁ where

  -- injective type constructors are incompatible with univalence
  tconstr-not-inj : ((A B : Type₀) → bot A ≡ bot B → A ≡ B) → ⊥
  tconstr-not-inj f = coe (f ⊤ ⊥ (ua bot⊤≃bot⊥)) tt
    where
    bot⊤≃bot⊥ : bot ⊤ ≃ bot ⊥
    bot⊤≃bot⊥ = qinv (λ ()) (λ ()) (λ ()) (λ ())

  abstract
    Fin-inj : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
    Fin-inj {zero}  {zero}  p = refl
    Fin-inj {zero}  {suc n} p = ⊥-elim (Fin0-is-empty (coe (! p) zero))
    Fin-inj {suc m} {zero}  p = ⊥-elim (Fin0-is-empty (coe p zero))
    Fin-inj {suc m} {suc n} p = ap suc (Fin-inj (Suc-injective (! (ua (Fin-Suc m)) ∙ p ∙ ua (Fin-Suc n))))

  -- Fin-inj' : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
  -- Fin-inj' {m} {n} p with ℕ-is-dec-≡ m n
  -- ... | inl ¬q = {!!}
  -- ... | inr q = q

  is-finite-is-prop : (A : Type₀) → is-prop (is-finite A)
  is-finite-is-prop A (n , e) (n' , e') = Σ-ext p (∥∥-is-prop (transport (λ n → ∥ A ≃ Fin n ∥) p e) e')
    where
    p : n ≡ n'
    p = ∥∥-rec2 (ℕ-is-set n n') (λ f f' → Fin-inj (ua (≃-trans (≃-sym f) f'))) e e'

  is-finite' : Type₀ → Type₀
  is-finite' A = ∥ Σ ℕ (λ n → A ≃ Fin n) ∥

  --
  --  This argument is completely general and could be moved to HLevel:
  --  any time you have propositions P and Q and maps P → Q and Q → P,
  --  then these maps are an equivalence just because P and Q are
  --  propositions ...
  --
  
  is-finite-≃ : (A : Type₀) → is-finite A ≃ is-finite' A
  is-finite-≃ A = prop-equiv
    (is-finite-is-prop A)
    ∥∥-is-prop
    (λ { (n , e) → ∥∥-rec ∥∥-is-prop (λ e → ∣ n , e ∣) e })
    (∥∥-rec (is-finite-is-prop A) (λ { (n , e) → n , ∣ e ∣ }))

---
--- Compatibility with constructions
---

postulate
  -- shown above, this version is generalized to arbitrary universes
  is-finite-is-prop' : ∀ {i} {A : Type i} → is-prop (is-finite A)

⊤-is-finite : is-finite ⊤
⊤-is-finite = 1 , ∣ qinv (λ _ → zero) (λ _ → tt) (λ _ → refl) (λ { zero → refl }) ∣

is-contr-is-finite : ∀ {i} {A : Type i} → is-contr A → is-finite A
is-contr-is-finite (a , p) = 1 , ∣ qinv (λ _ → zero) (λ _ → a) (λ x → p x) (λ { zero → refl }) ∣

open import Data.Nat.Properties

_+ℕ_ = Data.Nat._+_

Fin-× : (m n : ℕ) → (Fin m × Fin n) ≃ Fin (m * n)
Fin-× m n = qinv {!f!} {!!} {!!} {!!}
  where
  f : {m n : ℕ} → Fin m × Fin n → Fin (m * n)
  f {suc m} {n} (zero  , j) = {!!}
  f {suc m} {n} (suc i , j) = {!!}
  g : {m n : ℕ} → Fin (m * n) → (Fin m × Fin n)
  g k = {!!}

×-is-finite : ∀ {i j} {A : Type i} {B : Type j} → is-finite A → is-finite B → is-finite (A × B)
×-is-finite (m , FA) (n , FB) = (m * n) , ∥∥-rec2 ∥∥-is-prop (λ FA FB → ∣ ≃-trans (≃-× FA FB) (Fin-× m n) ∣) FA FB

Σ-is-finite : ∀ {i j} {A : Type i} {B : A → Type j} → is-finite A → ((a : A) → is-finite (B a)) → is-finite (Σ A B)
Σ-is-finite (m , FA) FB = ∥∥-rec is-finite-is-prop' (λ e → (sum λ i → fst (FB (≃← e i))) , ∣ qinv (λ { (a , b) → {!!} }) {!!} {!!} {!!} ∣) FA
  where
  sum : {n : ℕ} → (a : Fin n → ℕ) → ℕ
  sum {zero}  a = 0
  sum {suc n} a = Data.Nat._+_ (a zero) (sum (a ∘ suc))

postulate
  Σ-is-finite' : ∀ {i j} {A : Type i} {B : A → Type j} → is-finite (Σ A B) → ((a : A) → is-finite (B a))
  -- Σ-is-finite' = {!!}

---
--- Finite types
---

FinType : Type₁
FinType = Σ Type₀ is-finite

ft : {A : Type₀} → is-finite A → FinType
ft {A = A} F = A , F

-- cardinal
card : FinType → ℕ
card (A , n , F) = n

is-prop-≡-is-refl : ∀ {i} {A : Type i} (P : is-prop A) (x : A) → P x x ≡ refl
is-prop-≡-is-refl P x = is-prop-is-set P _ _ (P x x) refl

is-finite-is-prop-≡-is-refl : {A : Type₀} (P : is-finite A) → is-finite-is-prop A P P ≡ refl
is-finite-is-prop-≡-is-refl {A} P = is-prop-≡-is-refl (is-finite-is-prop A) P

FinType≡≃ : (X Y : FinType) → (X ≡ Y) ≃ (fst X ≡ fst Y)
FinType≡≃ X Y = qinv
  (ap fst)
  (λ { refl → Σ-ext refl (is-finite-is-prop (fst Y) (snd X) (snd Y)) })
  (λ { refl → transport (λ p → Σ-ext refl p ≡ refl) (! is-finite-is-prop-≡-is-refl (snd X)) refl })
  (λ { refl → begin
    (ap fst (Σ-ext refl (is-finite-is-prop (fst Y) (snd X) (snd Y)))) ≡⟨ is-finite-is-prop (fst X) (snd X) (snd Y) |in-ctx _ ⟩
    (ap fst (Σ-ext refl (is-finite-is-prop (fst Y) (snd Y) (snd Y)))) ≡⟨ is-finite-is-prop-≡-is-refl (snd Y) |in-ctx (λ p → ap fst (Σ-ext refl p)) ⟩
    refl ∎ })

FinType≡ : {X Y : FinType} → fst X ≡ fst Y → X ≡ Y
FinType≡ {X} {Y} = ≃← (FinType≡≃ X Y)

FinType≡-∙ : {X Y Z : FinType} (p : fst X ≡ fst Y) (q : fst Y ≡ fst Z) → FinType≡ {X} {Z} (p ∙ q) ≡ FinType≡ {X} {Y} p ∙ FinType≡ q
FinType≡-∙ {X} {Y} {Z} refl refl = ≃→0inj (FinType≡≃ X Z) (Σ-ext-fst refl _ ∙ ! Σ-ext-fst refl _) ∙ Σ-ext-∙ refl refl (is-finite-is-prop (fst Y) (snd X) (snd Y)) (is-finite-is-prop (fst Z) (snd Y) (snd Z))

FinType-is-groupoid : is-groupoid FinType
FinType-is-groupoid A B = transport is-set (! (ua (FinType≡≃ A B))) (≡-is-set (is-finite-is-set (snd A)) (is-finite-is-set (snd B)))
