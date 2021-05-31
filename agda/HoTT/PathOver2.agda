{-# OPTIONS --without-K --rewriting #-}

-- path over with univalence

module HoTT.PathOver2 where

open import HoTT.Base
open import HoTT.Path
open import HoTT.PathOver
open import HoTT.Equivalence
open import HoTT.Univalence
open import HoTT.Level

-- equivalence between pathover and transport
po-≃ : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y) (u : B x) (v : B y) → (transport B p u ≡ v) ≃ (u ≡ v [ B ↓ p ])
po-≃ B refl u v = ≃-refl

po-is-prop : ∀ {i j} {A : Type i} (B : A → Type j) → ((x : A) → is-set (B x)) → {x y : A} (p : x ≡ y) (u : B x) (v : B y) → is-prop (u ≡ v [ B ↓ p ])
po-is-prop B PB {x} {.x} refl u v = PB x u v

po-in-prop : ∀ {i j} {A : Type i} (B : A → Type j) → ((x : A) → is-prop (B x)) → {x y : A} (p : x ≡ y) (u : B x) (v : B y) → (u ≡ v [ B ↓ p ])
po-in-prop B PB {x} {.x} refl u v = PB x u v

po-funext-nd :
  ∀ {i j k} {A : Type i} {B : A → Type j} {B' : A → Type k}
  {a a' : A} (p : a ≡ a') (f : B a → B' a) (g : B a' → B' a') (q : (x : B a) (y : B a') →
  f x ≡ g y [ B' ↓ p ]) → f ≡ g [ (λ a → B a → B' a) ↓ p ]
po-funext-nd refl f g q = funext λ x → q x x

po-funext-≡' :
  ∀ {i j k} {A : Type i} {B : Type j} {B' : A → B → Type k}
  {a a' : A} {p : a ≡ a'} {f : (x : B) → B' a x} {g : (x : B) → B' a' x}
  (q q' : f ≡ g [ (λ a → (x : B) → B' a x) ↓ p ]) →
  ((b : B) → po-happly' q b ≡ po-happly' q' b) →
  q ≡ q'
po-funext-≡' {p = refl} q q' r = funext-≡ q q' r
