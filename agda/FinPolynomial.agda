{-# OPTIONS --without-K --allow-unsolved-metas #-}

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

is-finite-pol : ∀ {ℓ} {I J : Type ℓ} (P : I ↝ J) → Type ℓ
is-finite-pol {I = I} {J = J} P = {j : J} (c : Op P j) → is-finite (Σ I (λ i → Pm P i c))

_↝f_ : ∀ {ℓ} (I J : Type ℓ) → Type (lsuc ℓ)
I ↝f J = Σ (Poly I J) is-finite-pol

finite-id : {I : Type₀} → is-finite-pol (Id {I = I})
finite-id {j = j} c = is-contr-is-finite ((j , refl) , λ { (i , refl) → refl })

finite-comp :
  {I J K : Type₀} {P : I ↝ J} {Q : J ↝ K} →
  is-finite-pol P → is-finite-pol Q → is-finite-pol (P · Q)
finite-comp FP FQ (c , a) = {!!}

module _ {I J K : Type₀} where

  curry : (I ⊔ J) ↝f K → I ↝f (Exp J × K)
  curry (P , Pf) = (record { Op = op ; Pm = {!!} }) , {!!}
    where
    op : Exp J × K → Type₀
    op (jj , k) = Σ (Op P k) (λ c → (j : J) → ≃← 𝔹≃FinType (ft (Σ-is-finite' {!Pf c!} (Pm P (inr j) c))) ≡ {!!}) -- 
