{-# OPTIONS --without-K --rewriting #-}

-- path over implemented as transport

module HoTT.PathOverStub where

open import HoTT.Base
open import HoTT.Path

PathOver : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Type j
PathOver B p u v = transport B p u ≡ v

infix 30 PathOver
syntax PathOver B p u v = u ≡ v [ B ↓ p ]

po-cst : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y} {u v : B} (q : u ≡ v) → u ≡ v [ (λ _ → B) ↓ p ]
po-cst {p = refl} q = q

-- ↓-cst-out2
po-cst₂ : ∀ {i j} {A : Type i} {B : Type j} {a a' : A} {b b' : B} {p₀ p₁ : a ≡ a'} {q₀ q₁ : b ≡ b'} {q : p₀ ≡ p₁} → q₀ ≡ q₁ → po-cst {p = p₀} q₀ ≡ po-cst {p = p₁} q₁ [ (λ p → b ≡ b' [ (λ _ → B) ↓ p ]) ↓ q ]
po-cst₂ {p₀ = refl} {p₁ = .refl} {q = refl} k = k

po-trans : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A} {u : B x} {v : B y} {w : B z} {p : x ≡ y} {p' : y ≡ z} (q : u ≡ v [ B ↓ p ]) (q' : v ≡ w [ B ↓ p' ]) → u ≡ w [ B ↓ p ∙ p' ]
po-trans {p = refl} refl q' = q'

po-≡-r : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} {p : x ≡ y} {u : B x} {v v' : B y} (P : u ≡ v [ B ↓ p ]) (Q : v ≡ v') → u ≡ v' [ B ↓ p ]
po-≡-r P refl = P

po-cst-∙ : ∀ {i j} {A : Type i} {B : Type j} {x y z : A} {p : x ≡ y} {p' : y ≡ z} {u v w : B} (q : u ≡ v) (q' : v ≡ w) → po-cst {p = p ∙ p'} (q ∙ q') ≡ po-trans {u = u} (po-cst {p = p} q) (po-cst {p = p'} q')
po-cst-∙ {p = refl} refl q' = refl

apo : ∀ {i j} {A : Type i} {B : A → Type j} (f : (x : A) → B x) {x y : A} (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
apo f refl = refl

po-of-t : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} {p : x ≡ y} {u : B x} {v : B y} → transport B p u ≡ v → u ≡ v [ B ↓ p ]
po-of-t {p = refl} q = q

open import HoTT.Equivalence

po-≃ : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y) (u : B x) (v : B y) → (transport B p u ≡ v) ≃ (u ≡ v [ B ↓ p ])
po-≃ B refl u v = ≃-refl
