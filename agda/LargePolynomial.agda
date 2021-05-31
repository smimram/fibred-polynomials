{-# OPTIONS --without-K --type-in-type #-}

-- Trying construction without worrying about size issues

module LargePolynomial where

open import HoTT
open import Fam
open import Polynomial

open ≡-Reasoning

--- the large exponential
Exp : Type₀ → Type₁
Exp I = Fam I -- I → Type

module _ {I J K : Type₀} where

  curry : (I ⊔ J) ↝ K → I ↝ (Exp J × K)
  Op (curry P) (jj , k) = Σ (Op P k) (λ c → ((λ j → Pm P (inr j) c) ≡ jj))
  Pm (curry P) i c = Pm P (inl i) (fst c)

  uncurry : I ↝ (Exp J × K) → (I ⊔ J) ↝ K
  Op (uncurry P) k = Σ (Exp J) (λ jj → Op P (jj , k))
  Pm (uncurry P) (inl i) (jj , c) = Pm P i c
  Pm (uncurry P) (inr j) (jj , c) = jj j

  uncurry-curry : (P : (I ⊔ J) ↝ K) → uncurry (curry P) ≃₁ P
  uncurry-curry P = (record { Op→ = op→ ; Pm≃ = pm≃ }) , op→-equiv
    where
    op→ : {k : K} → Σ (Exp J) (λ jj → Σ (Op P k) (λ c → (λ j₁ → Pm P (inr j₁) c) ≡ jj)) → Op P k
    op→ {j} (jj , c , p) = c
    op← : {k : K} → Op P k → Σ (Exp J) (λ jj → Σ (Op P k) (λ c → (λ j → Pm P (inr j) c) ≡ jj))
    op← c = (λ j → Pm P (inr j) c) , c , funext λ j → refl
    pm≃ : {i : I ⊔ J} {k : K} {c : Σ (Exp J) (λ jj → Σ (Op P k) (λ c → (λ j → Pm P (inr j) c) ≡ jj))} → Pm (uncurry (curry P)) i c ≃ Pm P i (op→ c)
    pm≃ {inl i} {k} {.(λ j → Pm P (inr j) c) , c , refl} = ≃-refl
    pm≃ {inr j} {k} {jj , c , p} = id-to-equiv (happly (! p) j)
    op→← : {k : K} → (c : Op P k) → op→ (op← c) ≡ c
    op→← {k} c = begin
      op→ (op← c) ≡⟨⟩
      op→ ((λ j → Pm P (inr j) c) , c , funext λ j → refl) ≡⟨ funext-≡ (funext λ j → refl) refl( λ j → funext-comp (λ j → refl) j) |in-ctx (λ p → op→ ((λ j → Pm P (inr j) c) , c , p)) ⟩
      op→ ((λ j → Pm P (inr j) c) , c , refl) ≡⟨⟩
      c ∎
    op→-equiv : {k : K} → is-equiv (op→ {k})
    op→-equiv {k} = qinv-to-equiv (op← , (λ { (.(λ j → Pm P (inr j) c) , c , refl) → Σ-ext refl (Σ-ext refl (funext-≡ (funext λ j → refl) refl λ j → funext-comp (λ j → refl) j)) }) , op→←)

  curry-uncurry : (P : I ↝ (Exp J × K)) → curry (uncurry P) ≃₁ P
  curry-uncurry P = (record { Op→ = op→ ; Pm≃ = λ {i} {j} {c} → pm≃ {i} {j} {c} }) , op→-equiv
    where
    op→ : {j : Exp J × K} → Σ (Σ (Exp J) (λ jj → Op P (jj , snd j))) (λ c → (λ j₁ → fst c j₁) ≡ fst j) → Op P j
    op→ {jj , k} ((.jj , c) , refl) = c
    op← : {jk : Exp J × K} → Op P jk → Σ (Σ (Exp J) (λ jj → Op P (jj , snd jk))) (λ c → fst c ≡ fst jk)
    op← {jj , k} c = (jj , c) , refl
    op→-equiv : {jk : Exp J × K} → is-equiv (op→ {jk})
    op→-equiv {jk} = qinv-to-equiv (op← , (λ { ((.(fst jk) , c) , refl) → refl }) , λ c → refl)
    pm≃ : {i : I} {j : Exp J × K} {c : Σ (Σ (Exp J) (λ jj → Op P (jj , snd j))) (λ c₁ → (λ j₁ → fst c₁ j₁) ≡ fst j)} → Pm P i (snd (fst c)) ≃ Pm P i (op→ c)
    pm≃ {i} {j} {(.(fst j) , c) , refl} = ≃-refl

  adj : ((I ⊔ J) ↝ K) ≡ (I ↝ (Exp J × K))
  adj = ua (qinv curry uncurry (λ P → Poly-ua (uncurry-curry P)) (λ P → Poly-ua (curry-uncurry P)))
