{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

-- Equivalences with hlevels and univalence

module HoTT.Equivalence2 where

open import HoTT.Base
open import HoTT.Path
open import HoTT.Equivalence
open import HoTT.Univalence
open import HoTT.Level

open ≡-Reasoning

--- Laws of equivalence

postulate
  -- 4.2.13
  is-equiv-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → is-prop (is-equiv f)

-- equivalence induction 5.8.5
postulate
  ≃-ind : ∀ {i j} (P : {A B : Type i} → (A ≃ B) → Type j) → ((A : Type i) → P (≃-refl {A = A})) → {A B : Type i} (e : A ≃ B) → P e

-- the simple way of proving equality of ≃
≃-≡ : ∀ {i j} {A : Type i} {B : Type j} {f g : A ≃ B} → ≃→ f ≡ ≃→ g → f ≡ g
≃-≡ {f = f} {g = g} p = Σ-ext p (is-equiv-is-prop (≃→ g) (transport is-equiv p (snd f)) (snd g))

≃-unit-l : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B) → ≃-trans ≃-refl e ≡ e
≃-unit-l e = ≃-≡ refl

≃-unit-r : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B) → ≃-trans e ≃-refl ≡ e
≃-unit-r e = ≃-≡ refl

≃-assoc : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l} (f : A ≃ B) (g : B ≃ C) (h : C ≃ D) → ≃-trans (≃-trans f g) h ≡ ≃-trans f (≃-trans g h)
≃-assoc f g h = ≃-≡ refl

≃-inv-l : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B) → ≃-trans (≃-sym e) e ≡ ≃-refl
≃-inv-l e = ≃-≡ (funext (≃ε e))

≃-inv-r : ∀ {i j} {A : Type i} {B : Type j} (e : A ≃ B) → ≃-trans e (≃-sym e) ≡ ≃-refl
≃-inv-r e = ≃-≡ (funext (≃η e))

--- Alternative definitions of equivalence 

module _ {i j} {A : Type i} {B : Type j} where

  contr-fib-to-equiv : {f : A → B} (c-fib : (b : B) → is-contr (hfib f b)) → is-equiv f
  contr-fib-to-equiv {f} contr = qinv-to-equiv ((λ b → fst (fst (contr b))) , (λ a → ap fst (snd (contr (f a)) (a , refl))) , λ b → snd (fst (contr b)))

  contr-fib : (f : A → B) (cfib : (b : B) → is-contr (hfib f b)) → A ≃ B
  contr-fib f cfib = f , contr-fib-to-equiv cfib

  -- the good definition of injectivity (the HoTT book says being an "embedding")
  is-injective : (f : A → B) → Type (lmax i j)
  is-injective f = (x y : A) → is-equiv (ap f {x} {y})

  is-0-injective : (f : A → B) → Type (lmax i j)
  is-0-injective f = {x y : A} → f x ≡ f y → x ≡ y

  injective-0 : {f : A → B} → is-injective f → is-0-injective f
  injective-0 I {x} {y}  = ≃← (equiv (I x y))

  is-surjective : (f : A → B) → Type (lmax i j)
  is-surjective f = (y : B) → ∥ hfib f y ∥

  is-injective-is-prop : (f : A → B) → is-prop (is-injective f)
  is-injective-is-prop f P Q = funext2 λ x y → is-equiv-is-prop (ap f) (P x y) (Q x y)

  is-surjective-is-prop : (f : A → B) → is-prop (is-surjective f)
  is-surjective-is-prop f P Q = funext λ y → ∥∥-is-prop (P y) (Q y)

  --- Theorem 4.6.3
  bijective-to-equiv : {f : A → B} → is-injective f → is-surjective f → is-equiv f
  bijective-to-equiv {f} inj surj =
    contr-fib-to-equiv
      λ y → ∥∥-rec {A = hfib f y} (is-prop-is-contr (hfib f y))
        (λ { (x , p) → (x , p) , λ { (x' , p') → Σ-ext (≃← (equiv (inj x x')) (p ∙ ! p')) (begin
          transport (λ a → f a ≡ y) (≃← (ap f , inj x x') (p ∙ ! p')) p ≡⟨ {!!} ⟩
          p'
          ∎) }})
        (surj y)
    where open ≡-Reasoning

  bij : (f : A → B) → is-injective f → is-surjective f → A ≃ B
  bij f inj surj = f , bijective-to-equiv inj surj

  is-equiv-is-injective : (f : A → B) → is-equiv f → is-injective f
  is-equiv-is-injective f e x y =
    qinv-to-equiv (
      (λ p → ! (≃η (equiv e) x) ∙ ap (≃← (equiv e)) p ∙ ≃η (equiv e) y) ,
      (λ { refl → ∙-inv-l (≃η (equiv e) x) }) ,
      λ p → begin
        ap f (! ≃η (equiv e) x ∙ ap (≃← (equiv e)) p ∙ ≃η (equiv e) y) ≡⟨ ap-∙ f (! ≃η (equiv e) x) _ ⟩
        ap f (! ≃η (equiv e) x) ∙ ap f (ap (≃← (equiv e)) p ∙ ≃η (equiv e) y) ≡⟨ ap-∙ f (ap (≃← (equiv e)) p) _ |in-ctx (λ p → ap f (! ≃η (equiv e) x) ∙ p) ⟩
        ap f (! ≃η (equiv e) x) ∙ ap f (ap (≃← (equiv e)) p) ∙ ap f (≃η (equiv e) y) ≡⟨ ap-! f (≃η (equiv e) x) |in-ctx (λ p → p ∙ {!ap f (ap (≃← (equiv e)) p) ∙ ap f (≃η (equiv e) y)!}) ⟩
        {!!} ≡⟨ {!!} ⟩
        p ∎
      )
    where open ≡-Reasoning

  is-equiv-is-0-injective : (f : A → B) → is-equiv f → is-0-injective f
  is-equiv-is-0-injective f E = injective-0 (is-equiv-is-injective f E)

module _ {i j} {A : Type i} {B : Type j} (e : A ≃ B) where
  ≃→0inj : is-0-injective (≃→ e)
  ≃→0inj = is-equiv-is-0-injective _ (snd e)

  ≃←0inj : is-0-injective (≃← e)
  ≃←0inj = is-equiv-is-0-injective _ (snd (≃-sym e))

-- is-equiv-is-injective : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → is-equiv f → is-injective f
-- is-equiv-is-injective f e x y = contr-fib-to-equiv (ap f) (λ p → (
  -- ! (≃η (equiv e) x) ∙ ap (≃← (equiv e)) p ∙ ≃η (equiv e) y ,
  -- {!!}) ,
  -- {!!})

--- More funext

funext₂ : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x} (p q : f ≡ g) → ((x : A) → happly p x ≡ happly q x) → p ≡ q
funext₂ {f = f} {g = g} p q r = ≃← (equiv (is-equiv-is-injective happly (function-extensionality f g) p q)) (funext r)

