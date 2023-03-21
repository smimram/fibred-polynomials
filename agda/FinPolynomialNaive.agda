{-# OPTIONS --rewriting --without-K --type-in-type --allow-unsolved-metas #-}

-- finite polynomials
-- trying the big model on the exponential (based on FinType instead of 𝔹)
-- we thus still need --type-in-type but we should be getting closer

module FinPolynomialNaive where

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties hiding (⊔-comm)
open import Data.Fin hiding (lift ; _+_)
open import HoTT
open import Polynomial
open import FinType
open import Bij
open ≡-Reasoning

import Bij as 𝔹
open 𝔹 using (𝔹)

open import FinPolynomial hiding (curry ; uncurry)

module _ {I J K : Type₀} where

  import LargePolynomial as LP

  Exp' : (I : Type₀) → Type₁
  Exp' I = Σ (I → Type₀) (λ F → is-finite (Σ I F))

  curry : (I ⊔ J) ↝f K → I ↝f (Exp' J × K)
  curry (P , Pf) = record {
      Op = λ { (jj , k) → Σ (Op P k) (λ c → (λ j → Pm P (inr j) c) ≡ fst jj) } ;
      Pm = λ { i {jj , k} c → Pm P (inl i) (fst c) }
    } ,
    (λ c → is-finite-⊔-l (Pf (fst c)))

  uncurry : I ↝f (Exp' J × K) → (I ⊔ J) ↝f K
  uncurry (P , Pf) = (record {
      Op = λ k → Σ (Exp' J) (λ jj → Op P (jj , k)) ;
      Pm = λ {
        (inl i) (jj , c) → Pm P i c ;
        (inr j) (jj , c) → fst jj j
        }
    }) ,
    (λ { (jj , c) → Σ-⊔-is-finite (Pf c) (snd jj) })

  -- the equivalence can be imported from LargePolynomial for the first component
  -- the second component is in prop and does not matter
