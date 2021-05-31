{-# OPTIONS --without-K --rewriting #-}

open import HoTT.Base
open import HoTT.Path
open import HoTT.Univalence
open import HoTT.Level
open import HoTT.Equivalence
open import HoTT.Equivalence2

module HoTT.Level2 where

≃-is-prop : ∀ {i j} {A : Type i} {B : Type j} → is-prop A → is-prop B → is-prop (A ≃ B)
≃-is-prop PA PB = Σ-is-prop (→-is-prop PB) (λ f → is-equiv-is-prop f)

≡-is-prop : ∀ {i} {A B : Type i} → is-prop A → is-prop B → is-prop (A ≡ B)
≡-is-prop PA PB = is-prop-≃ (≃-sym (equiv univalence)) (≃-is-prop PA PB)

≃-is-set : ∀ {i j} {A : Type i} {B : Type j} → is-set A → is-set B → is-set (A ≃ B)
≃-is-set SA SB = Σ-is-set (→-is-set SB) (λ f → is-prop-is-set (is-equiv-is-prop f))

≡-is-set : ∀ {i} {A B : Type i} → is-set A → is-set B → is-set (A ≡ B)
≡-is-set SA SB = is-set-≃ (≃-sym (equiv univalence)) (≃-is-set SA SB)

hProp-is-set : ∀ {i} → is-set (hProp {i})
hProp-is-set (A , PA) (B , PB) = transport is-prop (! ua (Σ-≡ (A , PA) (B , PB))) (Σ-is-prop (≡-is-prop PA PB) (λ p → is-contr-is-prop (hom-prop-is-contr (is-prop-is-prop B) _ PB)))

hSet-is-groupoid : is-groupoid hSet
hSet-is-groupoid (A , SA) (B , SB) = transport is-set (! ua (Σ-≡ (A , SA) (B , SB))) (Σ-is-set (≡-is-set SA SB) (λ p → is-prop-is-set (is-contr-is-prop (hom-prop-is-contr (is-set-is-prop B) _ SB))))
