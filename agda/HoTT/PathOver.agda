{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module HoTT.PathOver where

open import HoTT.Base
open import HoTT.Path

PathOver : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x ≡ y) (u : B x) (v : B y) → Type j
PathOver B refl u v = (u ≡ v)
-- PathOver B p u v = transport B p u ≡ v

infix 30 PathOver
syntax PathOver B p u v = u ≡ v [ B ↓ p ]

po-cst : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y} {u v : B} (q : u ≡ v) → u ≡ v [ (λ _ → B) ↓ p ]
po-cst {p = refl} q = q

po-cst' : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y} {u v : B} → u ≡ v [ (λ _ → B) ↓ p ] → u ≡ v
po-cst' {p = refl} q = q

po-cst-inv-l : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y} {u v : B} (q : u ≡ v) → po-cst' (po-cst {p = p} q) ≡ q
po-cst-inv-l {p = refl} q = refl

-- ↓-cst-out2
po-cst₂ : ∀ {i j} {A : Type i} {B : Type j} {a a' : A} {b b' : B} {p₀ p₁ : a ≡ a'} {q₀ q₁ : b ≡ b'} {q : p₀ ≡ p₁} → q₀ ≡ q₁ → po-cst {p = p₀} q₀ ≡ po-cst {p = p₁} q₁ [ (λ p → b ≡ b' [ (λ _ → B) ↓ p ]) ↓ q ]
po-cst₂ {p₀ = refl} {p₁ = .refl} {q = refl} k = k

po-trans : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : A} {u : B x} {v : B y} {w : B z} {p : x ≡ y} {p' : y ≡ z} (q : u ≡ v [ B ↓ p ]) (q' : v ≡ w [ B ↓ p' ]) → u ≡ w [ B ↓ p ∙ p' ]
po-trans {p = refl} refl q' = q'

po-≡-r : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} {p : x ≡ y} {u : B x} {v v' : B y} (P : u ≡ v [ B ↓ p ]) (Q : v ≡ v') → u ≡ v' [ B ↓ p ]
po-≡-r P refl = P

po-cst-∙ : ∀ {i j} {A : Type i} {B : Type j} {x y z : A} {p : x ≡ y} {p' : y ≡ z} {u v w : B} (q : u ≡ v) (q' : v ≡ w) → po-cst {p = p ∙ p'} (q ∙ q') ≡ po-trans (po-cst {p = p} q) (po-cst {p = p'} q')
po-cst-∙ {p = refl} refl q' = refl

apo : ∀ {i j} {A : Type i} {B : A → Type j} (f : (x : A) → B x) {x y : A} (p : x ≡ y) → f x ≡ f y [ B ↓ p ]
apo f refl = refl

po-Σ-ext : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B} → (p : fst x ≡ fst y) (q : snd x ≡ snd y [ B ↓ p ]) → x ≡ y
po-Σ-ext refl refl = refl

-- po-Σ-ext-∙ : ∀ {i j} {A : Type i} {B : A → Type j} {x y z : Σ A B} → (p : fst x ≡ fst y) (p' : fst y ≡ fst z) (q : snd x ≡ snd y [ B ↓ p ]) (q' : snd y ≡ snd z [ B ↓ p' ]) →
             -- {!po-Σ-ext (p ∙ p') (q ∙ q')!} ≡ po-trans {B = λ _ → Σ A B} (po-Σ-ext p q) (po-Σ-ext p' q')
-- po-Σ-ext-∙ refl refl refl refl = refl

po-ap : ∀ {i j} {A A' : Type i} (B : A' → Type j) (f : A → A') {x y : A} (p : x ≡ y) (u : B (f x)) (v : B (f y)) →
        (u ≡ v [ B ∘ f ↓ p ]) ≡ (u ≡ v [ B ↓ ap f p ])
po-ap B f refl u v = refl

po-seq : ∀ {i j} {A : Type i} (B : A → A → Type j) {x y : A} {p : x ≡ y} {u₀₀ : B x x} {u₁₀ : B y x} {u₁₁ : B y y} →
         u₀₀ ≡ u₁₀ [ (λ y → B y x) ↓ p ] → u₁₀ ≡ u₁₁ [ (λ x → B y x) ↓ p ] → u₀₀ ≡ u₁₁ [ (λ x → B x x) ↓ p ]
po-seq B {p = refl} refl refl = refl

--- Compatibility with transport

po-to-t : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} {p : x ≡ y} {u : B x} {v : B y} → u ≡ v [ B ↓ p ] → transport B p u ≡ v
po-to-t {p = refl} q = q

po-of-t : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} {p : x ≡ y} {u : B x} {v : B y} → transport B p u ≡ v → u ≡ v [ B ↓ p ]
po-of-t {p = refl} q = q

po-cst-to-t : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {p : x ≡ y} {u v : B} (q : u ≡ v) → po-to-t {p = p} (po-cst q) ≡ transport-cst p u ∙ q
po-cst-to-t {p = refl} q = refl

apo-to-t : ∀ {i j} {A : Type i} {B : A → Type j} (f : (x : A) → B x) {x y : A} (p : x ≡ y) → po-to-t (apo f p) ≡ apd f p
apo-to-t f refl = refl

--- Application

-- case where B is not dependent
po-happly' :
  ∀ {i j k} {A : Type i} {B : Type j} {B' : A → B → Type k}
  {a a' : A} {p : a ≡ a'} {f : (x : B) → B' a x} {g : (x : B) → B' a' x}
  (q : f ≡ g [ (λ a → (x : B) → B' a x) ↓ p ])
  (b : B) → f b ≡ g b [ (λ a → B' a b) ↓ p ]
po-happly' {p = refl} q b = happly q b

-- po-happly :
  -- ∀ {i j k} {A : Type i} {B : A → Type j} {B' : (a : A) → B a → Type k}
  -- {a a' : A} {p : a ≡ a'} {f : (x : B a) → B' a x} {g : (x : B a') → B' a' x}
  -- (q : f ≡ g [ (λ a → (x : B a) → B' a x) ↓ p ])
  -- {b : B a} {b' : B a'} (r : b ≡ b' [ B ↓ p ]) → f b ≡ g b [ (λ a → B' a b) ↓ p ]
-- po-happly = ?
