{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module FinType where

open import HoTT
open import Data.Nat hiding (_⊔_)

open import Data.Fin hiding (fold ; lift ; _<_ ; _≤_ ; _+_)
open import Data.Fin.Patterns
open import Data.Sum.Base
open import Data.Sum.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

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
-- Rem : if we don't truncate, we don't have a proposition + we are equivalent to ℕ...
is-finite : ∀ {i} → Type i → Type i
is-finite A = Σ ℕ (λ n → ∥ A ≃ Fin n ∥)

is-finite-is-set : ∀ {i} {A : Type i} → is-finite A → is-set A
is-finite-is-set {A = A} (n , e) = ∥∥-rec (is-set-is-prop A) (λ e → is-set-≃ (≃-sym e) (Fin-is-set n)) e

Fin-is-finite : (n : ℕ) → is-finite (Fin n)
Fin-is-finite n = n , ∣ ≃-refl ∣

module _ where
  Fin0-is-empty : ¬ (Fin 0)
  Fin0-is-empty ()

  Fin0≃⊥ : Fin 0 ≃ ⊥
  Fin0≃⊥ = is-empty-≃-⊥ Fin0-is-empty

  Suc : ∀ {i} (A : Type i) → Type i
  Suc A = ⊤ ⊔ A

  -- is there a general explanation for this "homotopical elimination" property?
  ⊔-helim : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (z : A ⊔ B) → ((x : A) → z ≡ inl x → C) → ((y : B) → z ≡ inr y → C) → C
  ⊔-helim (inl x) f g = f x refl
  ⊔-helim (inr y) f g = g y refl

  pinspect : ∀ {i} {A : Type i} (x : A) → Σ A (λ y → x ≡ y)
  pinspect x = x , refl

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
    f p x with pinspect (coe p (inr x))
    ... | inr y , _ = y
    ... | inl tt , q with pinspect (coe p (inl tt))
    ... | inr y , _ = y
    ... | inl tt , r with coe-injective p (q ∙ ! r)
    ... | ()
    coe-inv-l : ∀ {i} {A B : Type i} (p : A ≡ B) (x : A) → coe (! p) (coe p x) ≡ x
    coe-inv-l p x = happly (! (coe-∙ p (! p))) x ∙ (∙-inv-r p |in-ctx λ p → coe p x)
    h : {A B : Type i} (p : Suc A ≡ Suc B) → (f (! p) ∘ f p) ∼ id
    h p x with pinspect (coe p (inr x))
    h p x | inl tt , q with pinspect (coe p (inl tt))
    h p x | inl tt , q | inl tt , r with coe-injective p (q ∙ ! r)
    h p x | inl tt , q | inl tt , r | ()
    h p x | inl tt , q | inr y , r with pinspect (coe (! p) (inr y))
    h p x | inl tt , q | inr y , r | inl tt , q' with pinspect (coe (! p) (inl tt))
    h p x | inl tt , q | inr y , r | inl tt , q' | inl tt , r' with coe-injective (! p) (q' ∙ ! r')
    h p x | inl tt , q | inr y , r | inl tt , q' | inl tt , r' | ()
    h p x | inl tt , q | inr y , r | inl tt , q' | inr x' , r' = inr-injective (! r' ∙ ap (coe (! p)) (! q) ∙ coe-inv-l p (inr x))
    h p x | inl tt , q | inr y , r | inr x' , q' with ! q' ∙ ! (ap (coe (! p)) r) ∙ coe-inv-l p (inl tt)
    h p x | inl tt , q | inr y , r | inr x' , q' | ()
    h p x | inr y , q with pinspect (coe (! p) (inr y))
    h p x | inr y , q | inl tt , q' with pinspect (coe (! p) (inl tt))
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

  Fin-+ : (m n : ℕ) → Fin (m + n) ≃ (Fin m ⊔ Fin n)
  Fin-+ zero    n =
    Fin n ≃⟨ ≃-sym ⊔-unit-l ⟩
    (⊥ ⊔ Fin n) ≃⟨ ≃-⊔ (≃-sym Fin0≃⊥) ≃-refl ⟩
    (Fin zero ⊔ Fin n) ≃∎
  Fin-+ (suc m) n =
    Fin (suc (m + n))     ≃⟨ Fin-Suc (m + n) ⟩
    (⊤ ⊔ (Fin (m + n)))   ≃⟨ ≃-⊔ ≃-refl (Fin-+ m n) ⟩
    (⊤ ⊔ (Fin m ⊔ Fin n)) ≃⟨ ≃-sym ⊔-assoc ⟩
    ((⊤ ⊔ Fin m) ⊔ Fin n) ≃⟨ ≃-⊔ (≃-sym (Fin-Suc m)) ≃-refl ⟩
    (Fin (suc m) ⊔ Fin n) ≃∎

  data bot (A : Type₀) : Type₁ where

  -- injective type constructors are incompatible with univalence
  tconstr-not-inj : ((A B : Type₀) → bot A ≡ bot B → A ≡ B) → ⊥
  tconstr-not-inj f = coe (f ⊤ ⊥ (ua bot⊤≃bot⊥)) tt
    where
    bot⊤≃bot⊥ : bot ⊤ ≃ bot ⊥
    bot⊤≃bot⊥ = qinv (λ ()) (λ ()) (λ ()) (λ ())

  -- it's not obvious because type constructors are not "injective" in Agda by
  -- default (this is incompatible with excluded middle)
  -- NB: this is not the good notion of injectivity, we want the function to induce an equivalence between
  -- the spaces of paths (it *will* become an equivalence for Bij) => "1-injective"?
  -- autre exemple: la troncation prop (ou le foncteur constant) n'est pas injective
  abstract
    Fin-inj : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
    Fin-inj {zero}  {zero}  p = refl
    Fin-inj {zero}  {suc n} p = ⊥-elim (Fin0-is-empty (coe (! p) zero))
    Fin-inj {suc m} {zero}  p = ⊥-elim (Fin0-is-empty (coe p zero))
    Fin-inj {suc m} {suc n} p = ap suc (Fin-inj (Suc-injective (! (ua (Fin-Suc m)) ∙ p ∙ ua (Fin-Suc n))))

  -- Fin-inj' : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
  -- Fin-inj' {m} {n} p with ℕ-is-dec-≡ m n
  -- ... | inl ¬q = ?
  -- ... | inr q = q
  
  is-finite-is-prop : ∀ {i} (A : Type i) → is-prop (is-finite A)
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

≤-is-prop : {x y : ℕ} → is-prop (x Data.Nat.≤ y)
≤-is-prop {x} {y} = ≤-irrelevant

Fin≃ℕ : (n : ℕ) → Fin n ≃ Σ ℕ (λ i → i < n)
Fin≃ℕ n = qinv f g g∘f f∘g
  where
  f : {n : ℕ} → Fin n → Σ ℕ (λ i → i < n)
  f zero    = zero , (s≤s z≤n)
  f (suc i) with f i
  ... | j , j<n = (suc j) , (s≤s j<n)
  g : {n : ℕ} → Σ ℕ (λ i → i < n) → Fin n
  g {suc n} (zero  , i<n) = zero
  g {suc n} (suc i , i<n) with g (i , ≤-pred i<n)
  ... | j = suc j
  g∘f : {n : ℕ} (i : Fin n) → g (f i) ≡ i
  g∘f zero    = refl
  g∘f (suc i) = ap suc (g∘f i)
  f∘g : {n : ℕ} (i : Σ ℕ (λ i → i < n)) → f (g i) ≡ i
  f∘g {suc n} (0 , k<n) = Σ-ext refl (≤-irrelevant _ _)
  f∘g {suc n} (suc k , k<n) with (f∘g (k , ≤-pred k<n))
  ... | x = Σ-ext (ap (λ u → suc (fst u)) x) (≤-irrelevant _ _)


_+ℕ_ = Data.Nat._+_

-- Fin-+ : (m n : ℕ) → (Fin m ⊎ Fin n) ≃ Fin (m +ℕ n)
-- Fin-+ m n = qinv f g (g∘f {m} {n}) (f∘g {m} {n})
--   where
--   f : {m n : ℕ} → Fin m ⊎ Fin n → Fin (m +ℕ n)
--   f {0F} (inr y) = y
--   f {suc m} (inl 0F) = zero
--   f {suc m} (inl (suc x)) = suc (f (inl x))
--   f {suc m} (inr y) = suc (f (inr y))
--   g : {m n : ℕ} → Fin (m +ℕ n) → (Fin m ⊎ Fin n)
--   g {0F} k = inr k
--   g {suc m} 0F = inl zero
--   g {suc m} (suc k)  with (g {m} k)
--   g {suc m} (suc k) | inl x = inl (suc x)
--   g {suc m} (suc k) | inr y = inr y
--   f∘g :  {m n : ℕ} → (x : Fin (m +ℕ n)) → f (g {m} {n} (x)) ≡ x
--   f∘g {0F} x = refl
--   f∘g {suc m} 0F = refl
--   f∘g {suc m} {n} (suc x) with (g {m} x) | inspect (g {m} {n})  x 
--   f∘g {suc m} {n} (suc x) | inl x₁ | [ e ] =  ap suc (subst (λ u → f u ≡ x) e (f∘g {m} {n} x))
--   f∘g {suc m} {n} (suc x) | inr y | [ e ] =  ap suc (subst (λ u → f u ≡ x) e (f∘g {m} {n} x))
--   g∘f : {m n : ℕ} → (x : Fin (m) ⊎ Fin (n)) → g {m} (f {m} {n} x) ≡ x
--   g∘f {0F} (inr y) = refl
--   g∘f {suc m} (inl 0F) = refl
--   g∘f {suc m} {n} (inl (suc x)) with (g {m} {n} (f (inl x))) | inspect ((g {m} {n}) ∘ f ∘ inl ) x
--   ... | inl x₁ | [ eq ] =
--                        ap (inl ∘ suc)
--                                       (inj₁-injective (subst (_≡ inl x) eq (g∘f (inl x))))
--   ... | inr y | [ eq ] with (subst (_≡ inl x) eq (g∘f (inl x)))
--   ... | ()
--   g∘f {suc m} {n} (inr y) with (g {m} {n} (f (inr y))) | inspect ((g {m} {n}) ∘ f ∘ inr ) y
--   g∘f {suc m} {n} (inr y) | inl x | [ eq ] with (subst (_≡ inr y) eq (g∘f (inr y)))
--   ... | () 
--   g∘f {suc m} {n} (inr y) | inr y₁ | [ eq ] = ap inr (inj₂-injective (subst (_≡ inr y) eq (g∘f (inr y))))
  
-- Fin-× : (m n : ℕ) → (Fin m × Fin n) ≃ Fin (m * n)
-- Fin-× m n = qinv f < g₁ , g₂ {m} {n} > (g∘f {m} {n}) (f∘g {m} {n})
  -- where
  -- f : {m n : ℕ} → Fin m × Fin n → Fin (m * n)
  -- f {suc m} {n} (0F , j) = ≃← (Fin-+ n (m * n)) (inl j)
  -- f {suc m} {n} (suc i , j) = ≃← (Fin-+ n (m * n)) (inr (f (i , j)))
  -- g₁ : {m n : ℕ} → Fin (m * n) → Fin m 
  -- g₁ {suc m} {n} k with (≃→ (Fin-+ n (m * n)) k)
  -- g₁ {suc m} {n} k | inl _ = zero
  -- g₁ {suc m} {n} k | inr y = suc (g₁ y)
  -- g₂ : {m n : ℕ} → Fin (m * n) → Fin n
  -- g₂ {suc m} {n} k with (≃→ (Fin-+ n (m * n)) k)
  -- g₂ {suc m} {n} k | inl x = x
  -- g₂ {suc m} {n} k | inr y = g₂ {m} {n} y
  -- f∘g : {m n : ℕ} → (x : Fin (m * n)) → f {m} {n} ( < g₁ , g₂ {m} {n} > x) ≡ x
  -- f∘g {suc m} {n} k with (≃→ (Fin-+ n (m * n)) k) | inspect (≃→ (Fin-+ n (m * n))) k
  -- f∘g {suc m} {n} k | inl x | [ e ] = trans (ap (≃← (Fin-+ n (m * n))) (sym e)) (≃η (Fin-+ n (m * n)) k)
  -- f∘g {suc m} {n} k | inr y | [ e ] =
      -- trans (ap ((≃← (Fin-+ n (m * n))) ∘ inr) (f∘g {m} {n} y) )
       -- (trans ((ap (≃← (Fin-+ n (m * n))) (sym e))) ((≃η (Fin-+ n (m * n)) k)))
  -- g₁∘f : {m n : ℕ} → (x : Fin m × Fin n) → (g₁ (f x) ≡ fst x)
  -- g₁∘f {suc m} {n} x with ((≃→ (Fin-+ n (m * n)) (f x))) | inspect (≃→ (Fin-+ n (m * n))) (f x)
  -- g₁∘f {suc m} {n} (0F , snd₁) | inl x₁ | [ e ] = refl
  -- g₁∘f {suc m} {n} (suc fst₁ , snd₁) | inl x₁ | [ e ] with (trans (sym e) (≃ε (Fin-+ n (m * n)) _ ))
  -- ... | ()
  -- g₁∘f {suc m} {n} (0F , snd₁) | inr y | [ e ] with (trans (sym e) (≃ε (Fin-+ n (m * n)) (inl snd₁)))
  -- ... | () 
  -- g₁∘f {suc m} {n} (suc fst₁ , snd₁) | inr y | [ e ] =
      -- ap suc (trans (ap g₁ (inj₂-injective (trans ((sym e)) (≃ε (Fin-+ n ((m * n))) _)))) (g₁∘f {m} {n} (fst₁ , snd₁)))
  -- g₂∘f : {m n : ℕ} → (x : Fin m × Fin n) → (g₂ {m} {n} (f {m} {n} x) ≡ snd x)
  -- g₂∘f {suc m} {n} x with ((≃→ (Fin-+ n (m * n)) (f x))) | inspect (≃→ (Fin-+ n (m * n))) (f x)
  -- g₂∘f {suc m} {n} (0F , snd₁) | inl x₁ | [ e ] = inj₁-injective (trans (sym e) (≃ε (Fin-+ n (m * n)) _))
  -- g₂∘f {suc m} {n} (suc fst₁ , snd₁) | inl x₁ | [ e ] with (trans (sym e) (≃ε (Fin-+ n (m * n)) _))
  -- ... | () 
  -- g₂∘f {suc m} {n} (0F , snd₁) | inr y | [ e ] with (trans (sym e) (≃ε (Fin-+ n (m * n)) _))
  -- ... | () 
  -- g₂∘f {suc m} {n} (suc fst₁ , snd₁) | inr y | [ e ] = trans (ap (g₂ {m} {n}) (inj₂-injective (trans ((sym e)) ((≃ε (Fin-+ n (m * n)) _))))) (g₂∘f (fst₁ , snd₁))
  -- g∘f : {m n : ℕ} → (x : (Fin m) × (Fin n)) → ((< g₁ , g₂ {m} {n} > ∘ f) x ≡ x)
  -- g∘f {m} {n} x = ×-ext (g₁∘f x) (g₂∘f x)

Fin-× : (m n : ℕ) → (Fin m × Fin n) ≃ Fin (m * n)
Fin-× zero    n =
  (Fin zero × Fin n) ≃⟨ ≃-ap (λ A → A × Fin n) Fin0≃⊥ ⟩
  (⊥ × Fin n)        ≃⟨ ⊥-× ⟩
  ⊥                  ≃⟨ ≃-sym Fin0≃⊥ ⟩
  Fin zero           ≃∎
Fin-× (suc m) n =
  (Fin (suc m) × Fin n) ≃⟨ ≃-ap (λ A → A × Fin n) (Fin-Suc m) ⟩
  ((⊤ ⊔ (Fin m)) × Fin n) ≃⟨ ⊔-× ⟩
  ((⊤ × Fin n) ⊔ (Fin m × Fin n)) ≃⟨ ≃-ap (λ A → A ⊔ (Fin m × Fin n)) ×-unit-l ⟩
  ((Fin n) ⊔ (Fin m × Fin n)) ≃⟨ ≃-ap (λ A → Fin n ⊔ A) (Fin-× m n) ⟩
  ((Fin n) ⊔ (Fin (m * n))) ≃⟨ ≃-sym (Fin-+ n (m * n)) ⟩
  Fin (n + m * n) ≃∎

×-is-finite : ∀ {i j} {A : Type i} {B : Type j} → is-finite A → is-finite B → is-finite (A × B)
×-is-finite (m , FA) (n , FB) = (m * n) , ∥∥-rec2 ∥∥-is-prop (λ FA FB → ∣ ≃-trans (≃-× FA FB) (Fin-× m n) ∣) FA FB

sum : {n : ℕ} → (a : Fin n → ℕ) → ℕ
sum {zero}  a = 0
sum {suc n} a = Data.Nat._+_ (a zero) (sum (a ∘ suc))

Fin-Σ : (n : ℕ) (P : Fin n → ℕ) → (Σ (Fin n) (Fin ∘ P) ≃ Fin (sum P))
Fin-Σ n P = qinv (f {n} {P}) (g {n} {P}) (g∘f {n} {P}) (f∘g {n} {P})
  where
  f : {n : ℕ} {P : Fin n → ℕ} → (Σ (Fin n) (Fin ∘ P)) →  Fin (sum P)
  f {suc n} {P} (0F , iₖ) = ≃← (Fin-+ (P 0F) _) (inl iₖ)
  f {suc n} {P} (suc k , iₖ) = ≃← (Fin-+ (P 0F) (sum (P ∘ suc))) (inr (f ( k , iₖ )))
  g : {n : ℕ} {P : Fin n → ℕ}  →  Fin (sum P) → (Σ (Fin n) (Fin ∘ P))
  g {suc n} {P} x with (≃→ (Fin-+ (P 0F) (sum (P ∘ suc))) x)
  g {suc n} {P} x | inl x₁ =  zero , x₁
  g {suc n} {P} x | inr y with (g {n} y)
  g {suc n} {P} x | inr y | fst₁ , snd₁ = suc fst₁ , snd₁
  f∘g : {n : ℕ} {P : Fin n → ℕ} (x : Fin (sum P)) → (f {n} {P} (g {n} {P}  x) ≡ x)
  f∘g {suc n} {P} x with (≃→ (Fin-+ (P 0F) (sum (λ x₁ → P (suc x₁)))) x) | inspect (≃→ (Fin-+ (P 0F) (sum (λ x₁ → P (suc x₁))))) x
  f∘g {suc n} {P} x | inl x₁ | [ e ] = trans (ap (≃←  (Fin-+ ((P 0F)) (sum (P ∘ suc)))) (sym e)) (≃η (Fin-+ ((P 0F)) ((sum (P ∘ suc)))) x)
  f∘g {suc n} {P} x | inr y | [ e ] with (g {n} {P ∘ suc} y) | inspect (g {n} {P ∘ suc})  y
  ... | c | [ eq ] = trans (ap (≃← (Fin-+ (P 0F) (sum (P ∘ suc)))) (trans (ap inr (trans (ap f (sym eq)) (f∘g {n} {P ∘ suc} y))) (sym e))) (≃η (Fin-+ (P 0F) (sum (P ∘ suc))) x)
  g∘f : {n : ℕ} {P : Fin n → ℕ} (x : Σ (Fin n) (Fin ∘ P)) → (g (f x) ≡ x)
  g∘f {suc n} {P} (k , iₖ) with (≃→ (Fin-+ (P 0F) (sum (λ x → P (suc x)))) (f {suc n} {P} (k , iₖ))) | inspect (≃→ (Fin-+ (P 0F) (sum (λ x → P (suc x))))) (f {suc n} {P} (k , iₖ)) 
  g∘f {suc n} {P} (0F , iₖ) | inl x | [ e ] = Σ-ext refl (inj₁-injective (trans (sym e) (≃ε (Fin-+ _ _) (inl iₖ))))
  g∘f {suc n} {P} (suc k , iₖ) | inl x | [ e ] with (trans (sym e) (≃ε (Fin-+ _ _) (inr (f (k , iₖ)))))
  ... | ()
  g∘f {suc n} {P} (0F , iₖ) | inr y | [ e ] with (trans (sym e) (≃ε (Fin-+ (P 0F) (sum (P ∘ suc))) (inl iₖ)))
  ... | ()
  g∘f {suc n} {P} (suc k , iₖ) | inr y | [ e ] with (g {n} {P ∘ suc} y) | inspect (g {n} {P ∘ suc}) y
  g∘f {suc n} {P} (suc k , iₖ) | inr y | [ e ] | c | [ eq ] =
           trans (ap (λ u → (suc (fst u), snd u)) (sym eq))
             (trans (ap (λ u → suc (proj₁ (g u)) , snd (g {n} u)) (inj₂-injective (trans (sym e) (≃ε (Fin-+ _ _) (inr (f (k , iₖ)))))))
             (ap (λ u → suc (fst u) , snd u) (g∘f (k , iₖ))))


-- This is the axiom of choice for finite sets (it is actually an equivalence)
Fin→∥∥ : ∀ {i} (n : ℕ) (P : Fin n → Type i) →  ((k : Fin n) → ∥ P k ∥) →  ∥ ((k : Fin n) → P k) ∥ 
Fin→∥∥ zero P H = ∣ (λ () ) ∣
Fin→∥∥ (suc n) P H with (Fin→∥∥ n (P ∘ suc) (λ k → H (suc k))) | H zero
... | Hsuc∥∥ | Hzero∥∥ = ∥∥-rec ∥∥-is-prop (λ Hzero → ∥∥-rec ∥∥-is-prop (λ Hsuc → ∣ ( λ { 0F → Hzero ; (suc k) → Hsuc k} ) ∣ ) Hsuc∥∥ ) Hzero∥∥

transport-≃-finite : ∀ {i j} {A : Type i} {B : Type j} (HA : is-finite A) (B≃A : B ≃ A) → is-finite B
transport-≃-finite (n , ∥A≃n∥ ) B≃A = n , ∥∥-rec ∥∥-is-prop  (λ A≃n → ∣ ≃-trans B≃A A≃n ∣ ) ∥A≃n∥

transport-∥≃∥-finite : ∀ {i j} {A : Type i} {B : Type j} (HA : is-finite A) (∥B≃A∥ : ∥ B ≃ A ∥ ) → is-finite B
transport-∥≃∥-finite (n , ∥A≃n∥ ) ∥B≃A∥ = n , ∥∥-rec ∥∥-is-prop  (λ A≃n  →  ∥∥-rec ∥∥-is-prop (λ B≃A → ∣ ≃-trans B≃A A≃n ∣) ∥B≃A∥) ∥A≃n∥


Σ-≃-snd-Set : ∀ {i j} {A : Type i} {B : A → Type j} {B' : A → Set} → ((a : A) → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-≃-snd-Set {B = B} {B' = B'} B≃ = qinv
  (λ { (a , b) → a , (≃→ (B≃ a) b) })
  (λ { (a , b) → a , (≃← (B≃ a) b) })
  (λ { (a , b) → Σ-ext refl (≃η (B≃ a) b) })
  (λ { (a , b) → Σ-ext refl (≃ε (B≃ a) b) })

Fin-Σ-is-finite : ∀ {i} (n : ℕ) (B : Fin n → Type i) → ((k : Fin n) → is-finite (B k)) → (is-finite (Σ (Fin n) B))
Fin-Σ-is-finite n B Bf =   transport-∥≃∥-finite {A = Σ (Fin n) (λ k → Fin (proj₁ (Bf k)))} Af A≃
  where
  Af≃ : ∥ Σ (Fin n) (λ k → Fin (proj₁ (Bf k))) ≃ Fin (sum (λ k → proj₁ (Bf k))) ∥
  Af≃ = ∣ Fin-Σ n (λ k → (proj₁ (Bf k))) ∣
  -- Af≃ with (Fin→∥∥ n _ (λ k → proj₂ (Bf k)))
  -- ... | Bf≃∥∥ = ∥∥-rec ∥∥-is-prop (λ Bf≃ → ∣ Fin-Σ n (λ k → (proj₁ (Bf k))) ∣) Bf≃∥∥
  Af : is-finite (Σ (Fin n) (λ k → Fin (proj₁ (Bf k))))
  Af =  sum (λ k → (proj₁ (Bf k))) , Af≃
  A≃ : ∥ Σ (Fin n) B ≃ Σ (Fin n) (λ k → Fin (proj₁ (Bf k))) ∥
  A≃ with (Fin→∥∥ n _ (λ k → proj₂ (Bf k)))
  ... | ∥Bf≃∥ =  ∥∥-rec ∥∥-is-prop (λ Bf≃ → ∣ Σ-≃-snd-Set Bf≃ ∣) ∥Bf≃∥ 

Σ-is-finite : ∀ {i j} {A : Type i} {B : A → Type j} → is-finite A → ((a : A) → is-finite (B a)) → is-finite (Σ A B)
Σ-is-finite (m , FA) FB = ∥∥-rec is-finite-is-prop' (λ A≃m → transport-≃-finite (Fin-Σ-is-finite m _ (λ k → FB _)) (≃-sym (Σ-≃-fst (≃-sym A≃m)))) FA

⊔-is-finite : ∀ {i} {A B : Type i} → is-finite A → is-finite B → is-finite (A ⊔ B)
⊔-is-finite {_} {A} {B} (nA , FA) (nB , FB) = ∥∥-rec2 (is-finite-is-prop (A ⊔ B)) (λ eA eB → nA + nB , ∣ ≃-trans (≃-⊔ eA eB) (≃-sym (Fin-+ nA nB)) ∣) FA FB

postulate
  Σ-is-finite' : ∀ {i j} {A : Type i} {B : A → Type j} → is-finite (Σ A B) → ((a : A) → is-finite (B a))
  -- Σ-is-finite' = ?

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
  (λ { refl → {!!} })
  -- begin
    -- (ap fst (Σ-ext refl (is-finite-is-prop (fst Y) (snd X) (snd Y)))) ≡⟨ is-finite-is-prop (fst X) (snd X) (snd Y) |in-ctx _ ⟩
    -- (ap fst (Σ-ext refl (is-finite-is-prop (fst Y) (snd Y) (snd Y)))) ≡⟨ is-finite-is-prop-≡-is-refl (snd Y) |in-ctx (λ p → ap fst (Σ-ext refl p)) ⟩
    -- refl ∎ })

FinType≡ : {X Y : FinType} → fst X ≡ fst Y → X ≡ Y
FinType≡ {X} {Y} = ≃← (FinType≡≃ X Y)

-- roughly (p . q, ?) ≡ (p , ?) . (q , ?) where ? is some arbitrary proof of finiteness
FinType≡-∙ : {X Y Z : FinType} (p : fst X ≡ fst Y) (q : fst Y ≡ fst Z) → FinType≡ {X} {Z} (p ∙ q) ≡ FinType≡ {X} {Y} p ∙ FinType≡ q
FinType≡-∙ {X} {Y} {Z} refl refl = ≃→0inj (FinType≡≃ X Z) (Σ-ext-fst refl _ ∙ ! Σ-ext-fst refl _) ∙ Σ-ext-∙ refl refl (is-finite-is-prop (fst Y) (snd X) (snd Y)) (is-finite-is-prop (fst Z) (snd Y) (snd Z))

-- postulate

  -- This is true because equality in a Σ is just equality of the
  -- base and equality of the fiber.  But since the fiber here is
  -- a proposition (is-finite), this second equality is always trivial.
  -- Hence, the space of paths is simply equivalences between the first
  -- components by univalence.
  
  -- FinType≡ : (X Y : FinType) → (X ≡ Y) ≃ (fst X ≡ fst Y)

  -- This is actually true more generally: if X and Y are n-types,
  -- then so is the space of equivalences between them ...
  
  -- ≃-is-set : ∀ {i} {X Y : Type i}
    -- → is-set X
    -- → is-set Y
    -- → is-set (X ≃ Y)
  -- ≃-is-set SX SY = ?

-- Now this next statement can be proved using the two previous statements:
-- since you know the path-types explicitly from univalence, and since being
-- finite implies that you are a set, this means the space of equivalences is
-- also a set, and hence so is the space of equalities between any two finite
-- types. And this says that the type of finite types is a groupoid.

FinType-is-groupoid : is-groupoid FinType
FinType-is-groupoid A B = transport is-set (! (ua (FinType≡≃ A B))) (≡-is-set (is-finite-is-set (snd A)) (is-finite-is-set (snd B)))

-- the following map is not injective
-- ℕ → Type
-- n ↦ Fin n
-- we can obtain FinType by factorizing it as an epi followed by a mono (which is always possible)

FinExp : ∀ {i} → Type i → Type (lmax (lsuc lzero) i)
FinExp I = Σ FinType (λ N → fst N → I)

FinExp' : ∀ {i} → Type i → Type (lmax (lsuc lzero) i)
FinExp' I = Σ (I → Type₀) (λ F → is-finite (Σ I F))

--- The exponential can also be defined as a family
module _ where
  open import Fam

  Exp-Fam : (I : Type₀) → FinExp I ≃ FinExp' I
  Exp-Fam I = qinv
    (λ { ((A , fin) , l) → hfib l , transport is-finite (! ua (El-fib'≃ I l)) fin })
    (λ { (F , fin) → (Σ I F , fin) , El-proj I F })
    (λ { ((A , fin) , l) →
      Σ-ext (Σ-ext (El-fib' I l) (is-finite-is-prop A _ _))
      (transport-ap (λ A → A → I) fst (Σ-ext (El-fib' I l) (is-finite-is-prop A (transport is-finite (El-fib' I l) (transport is-finite (! ua (El-fib'≃ I l)) fin)) fin)) (El-proj I (hfib l)) ∙ ap (λ B → transport (λ A → A → I) B (El-proj I (hfib l))) (Σ-ext-fst (El-fib' I l) _) ∙ El-fib'' I l)
      })
    (λ { (F , fin) → Σ-ext (funext (El-fib I F)) (is-finite-is-prop (Σ I F) _ _) })

