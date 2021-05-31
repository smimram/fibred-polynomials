{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Univalence where

open import HoTT.Base
open import HoTT.Path
open import HoTT.Homotopy
open import HoTT.Equivalence

module _ {i} {A B : Type i} where

  postulate univalence : is-equiv (id-to-equiv {i} {A} {B})

  ue : (A ≡ B) ≃ (A ≃ B)
  ue = equiv univalence

  ua : (A ≃ B) → (A ≡ B)
  ua = ≃← ue

  -- computation principle of univalence
  coe-ua : (e : A ≃ B) → coe (ua e) ≡ ≃→ e
  coe-ua e = ap ≃→ (≃ε ue e)

-- extensionality
ua-refl : ∀ {i} (A : Type i) → ua (≃-refl {A = A}) ≡ refl
ua-refl A = ≃η ue refl

-- by ≃-induction we can suppose that f is ≃-refl
postulate
  ua-trans : ∀ {i} {A B C : Type i} (f : A ≃ B) (g : B ≃ C) → ua (≃-trans f g) ≡ ua f ∙ ua g
-- ua-trans f g = {!!}
  ua-! : ∀ {i} (A B : Type i) (e : A ≃ B) → ! (ua e) ≡ ua (≃-sym e)

ua-is-equiv : ∀ {i} {A B : Type i} → is-equiv (ua {A = A} {B = B})
ua-is-equiv = snd (≃-sym ue)

≃-ap : ∀ {i j} {A B : Type i} (f : Type i → Type j) → A ≃ B → f A ≃ f B
≃-ap f e = id-to-equiv (ap f (ua e))

-- ≃-opt : ∀ {i j} (A : Type i) (B : A → Type j) → ({x : A} → B x) ≃ ((x : A) → B x)
-- ≃-opt A B = qinv (λ f x → f {x}) (λ f {x} → f x) (λ _ → refl) (λ _ → refl)

--- Function extensionality

-- Path : ∀ {i} (A : Type i) → Type i
-- Path A = Σ A λ x → Σ A λ y → x ≡ y

-- Homotopy : ∀ {i} (A B : Type i) → Type i
-- Homotopy A B = Σ (A → B) λ f → Σ (A → B) λ g → f ∼ g

-- Homotopy-Path : ∀ {i} (A B : Type i) → Homotopy A B ≃ Path (A → B)
-- Homotopy-Path {i} A B =
  -- Homotopy A B ≃⟨ qinv (λ { (f , g , p) x → f x , g x , p x }) (λ h → (λ x → fst (h x)) , (λ x → fst (snd (h x))) , λ x → snd (snd (h x))) (λ (f , g , p) → refl) (λ x → refl) ⟩
  -- (A → Path B) ≃⟨ ≃-ap (λ B → A → B) (Path-contr B) ⟩
  -- (A → B) ≃⟨ ≃-sym (Path-contr (A → B)) ⟩
  -- Path (A → B) ≃∎
  -- where
    -- Path-contr : (A : Type i) → Path A ≃ A
    -- Path-contr A = qinv fst (λ x → x , x , refl) (λ { (x , .x , refl) → refl }) (λ x → refl)

postulate function-extensionality : ∀ {i j} {A : Type i} {B : A → Type j} → (f g : (x : A) → B x) → is-equiv (happly {f = f} {g = g})

funext : ∀ {i j} {A : Type i} {B : A → Type j} → {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funext {f = f} {g = g} = ≃← (equiv (function-extensionality f g))

funext-comp : ∀ {i j} {A : Type i} {B : A → Type j} → {f g : (x : A) → B x} (h : (x : A) → f x ≡ g x) (x : A) → happly (funext h) x ≡ h x
funext-comp {f = f} {g = g} h x = happly (≃ε (equiv (function-extensionality f g)) h) x

funext2 : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} → {f g : (a : A) (b : B a) → C a b} → ((a : A) (b : B a) → f a b ≡ g a b) → f ≡ g
funext2 p = funext (λ a → funext (λ b → p a b))

funext3 : ∀ {i j k l} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k} {D : (a : A) (b : B a) (c : C a b) → Type l} → {f g : (a : A) (b : B a) (c : C a b) → D a b c} → ((a : A) (b : B a) (c : C a b) → f a b c ≡ g a b c) → f ≡ g
funext3 p = funext (λ a → funext (λ b → funext (λ c → p a b c)))

postulate funextopt : ∀ {i j} {A : Type i} {B : A → Type j} → {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

postulate
  funext-≡ : ∀ {i j} {A : Type i} {B : A → Type j} → {f g : (x : A) → B x} (p q : f ≡ g) → ((x : A) → happly p x ≡ happly q x) → p ≡ q
  -- funext-≡ p q x = {!!}
