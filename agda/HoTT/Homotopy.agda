{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Homotopy where

open import HoTT.Base
open import HoTT.Path

_∼_ :  ∀ {i j} {A : Type i} {B : A → Type j} (f g : (x : A) → B x) → Type (lmax i j)
_∼_ f g = ∀ x → f x ≡ g x

∼-refl : ∀ {i j} {A : Type i} {B : A → Type j} {f : (x : A) → B x} → f ∼ f
∼-refl x = refl

∼-trans : ∀ {i j} {A : Type i} {B : A → Type j} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
∼-trans r s x = trans (r x) (s x)

∼-natural : ∀ {i j} {A : Type i} {B : Type j} {x y : A} {f g : A → B} (h : f ∼ g) (p : x ≡ y) → h x ∙ ap g p ≡ ap f p ∙ h y
∼-natural h refl = ∙-unit-r _

∼-natural-toid : ∀ {i} {A : Type i} {f : A → A} (h : f ∼ id) (x : A) → ap f (h x) ≡ h (f x)
∼-natural-toid {f = f} h x = begin
  ap f (h x) ≡⟨ sym (∙-unit-r _) ⟩
  ap f (h x) ∙ refl ≡⟨ ap2 _∙_ refl (sym (∙-inv-r (h x))) ⟩
  ap f (h x) ∙ (h x ∙ ! h x) ≡⟨ sym (∙-assoc (ap f (h x)) _ _) ⟩
  (ap f (h x) ∙ h x) ∙ ! h x ≡⟨ ap2 _∙_ (sym (∼-natural h (h x))) refl ⟩
  (h (f x) ∙ ap id (h x)) ∙ ! h x ≡⟨ ap2 _∙_ (ap2 _∙_ refl (ap-id (h x))) (refl {x = sym (h x)}) ⟩
  (h (f x) ∙ h x) ∙ ! h x ≡⟨ ∙-assoc (h (f x)) _ _ ⟩
  h (f x) ∙ (h x ∙ ! h x) ≡⟨ ap2 _∙_ refl (∙-inv-r (h x)) ⟩
  h (f x) ∙ refl ≡⟨ ∙-unit-r _ ⟩
  h (f x) ∎
  where open ≡-Reasoning
