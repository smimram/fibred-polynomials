{-# OPTIONS --without-K #-}

-- Equivalence between families and types over
-- Traditionally: Set/I ≃ Set^I

module Fam where

open import HoTT
open ≡-Reasoning

module _ {ℓ} (I : Type ℓ) where

  Over : Type (lsuc ℓ)
  Over = Σ (Type ℓ) (λ A → A → I)

  Fam : Type (lsuc ℓ)
  Fam = I → Type ℓ

  El : Fam → Type ℓ
  El a = Σ I a

  El-proj : (a : Fam) → El a → I
  El-proj a (x , i) = x

  El-fib : (a : Fam) (i : I) → hfib (El-proj a) i ≡ a i
  El-fib a i = ua (qinv (λ { ((i , x) , refl) → x }) (λ x → (i , x) , refl) (λ { ((i , x) , refl) → refl }) (λ _ → refl))

  El-fib'≃ : {A : Type ℓ} (f : A → I) → Σ I (hfib f) ≃ A
  El-fib'≃ f = qinv (λ { (i , x , p) → x }) (λ x → (f x) , (x , refl)) (λ { (.(f x) , x , refl) → refl }) (λ _ → refl)

  El-fib' : {A : Type ℓ} (f : A → I) → Σ I (hfib f) ≡ A
  El-fib' f = ua (El-fib'≃ f)

  El-fib'' : {A : Type ℓ} (f : A → I) → transport (λ A → A → I) (El-fib' f) (El-proj (hfib f)) ≡ f
  El-fib'' f = begin
    transport (λ A → A → I) (El-fib' f) (El-proj (hfib f)) ≡⟨ transport-→ (λ A → A) (λ A → I) (El-fib' f) (El-proj (hfib f)) ⟩
    transport (λ A → I) (El-fib' f) ∘ El-proj (hfib f) ∘ transport (λ A → A) (! El-fib' f) ≡⟨ ap2 _∘_ (funext (transport-cst (El-fib' f))) refl ⟩
    El-proj (hfib f) ∘ coe (! El-fib' f) ≡⟨ ap2 _∘_ (lem f) refl ⟩
    f ∘ coe (El-fib' f) ∘ coe (! El-fib' f) ≡⟨ ! coe-∙ (! El-fib' f) (El-fib' f) |in-ctx (λ g → f ∘ g) ⟩
    f ∘ coe (! El-fib' f ∙ El-fib' f) ≡⟨ ∙-inv-l (El-fib' f) |in-ctx (λ p → f ∘ coe p) ⟩
    f ∘ coe refl ≡⟨⟩
    f ∎
    where
    lem : {A : Type ℓ} (f : A → I) → El-proj (hfib f) ≡ f ∘ coe (El-fib' f)
    lem f = funext λ { (.(f x) , x , refl) → ap f (! happly (coe-ua (El-fib'≃ f)) (f x , x , refl)) }
      -- begin
      -- El-proj (hfib f) (f x , x , refl) ≡⟨⟩
      -- f x ≡⟨⟩
      -- (f ∘ (λ { (i , x , p) → x })) (f x , x , refl) ≡⟨ ap f (! happly (coe-ua (El-fib'≃ f)) (f x , x , refl)) ⟩
      -- (f ∘ coe (El-fib' f)) (f x , x , refl) ∎ }

  Over-Fam : Over ≃ Fam
  Over-Fam = qinv
    (λ { (A , f) → hfib f })
    (λ a → El a , El-proj a)
    (λ { (A , f) → Σ-ext (El-fib' f) (El-fib'' f) })
    (λ a → funext λ i → El-fib a i)

module _ {ℓ} {I : Type ℓ} where

  Over-to-Fam : Over I → Fam I
  Over-to-Fam = ≃→ (Over-Fam I)

  Fam-to-Over : Fam I → Over I
  Fam-to-Over = ≃← (Over-Fam I)
