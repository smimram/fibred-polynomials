{-# OPTIONS --without-K --rewriting #-}

module HoTT.Base where

open import Agda.Primitive renaming (_⊔_ to lmax) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; module ≡-Reasoning) public
open import Function using (case_of_) public
open import Data.Unit using (⊤ ; tt) public
open import Data.Empty public
open import Relation.Nullary using (¬_) public
open import Data.Product using (_×_ ; Σ ; _,_) renaming (proj₁ to fst ; proj₂ to snd) public
open import Data.Sum renaming (_⊎_ to _⊔_ ; inj₁ to inl ; inj₂ to inr) public

{-# BUILTIN REWRITE _≡_ #-}

--- Types

Type : ∀ i → Set (lsuc i)
Type i = Set i

Type₀ = Set
Type₁ = Set₁

record Lift {j} {i} (A : Type i) : Set (lmax i j) where
  constructor lift
  field lower : A

Π : ∀ {i j} (A : Type i) (B : A → Type j) → Type (lmax i j)
Π A B = (x : A) → B x

J : ∀ {i j} {A : Type i} (P : (x y : A) → x ≡ y → Type j) → ((x : A) → P x x refl) → {x y : A} (p : x ≡ y) → P x y p
J P Pr {x = x} refl = Pr x

--- Functions

_∘_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

infixr 20 _∘_

id : ∀ {i} {A : Type i} → A → A
id x = x
