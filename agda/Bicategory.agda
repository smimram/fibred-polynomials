{-# OPTIONS --without-K #-}

-- really a (2,1)-bicategory

module Bicategory where

open import HoTT hiding (id)

record Bicategory {lobj larrow} : Type (lsuc (lmax lobj larrow)) where
  infixr 40 _⊗_
  field
    obj       : Type lobj
    hom       : obj → obj → Type larrow
    _⊗_       : {a b c : obj} (f : hom a b) (g : hom b c) → hom a c
    assoc     : {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d) →
                (f ⊗ g) ⊗ h ≡ f ⊗ (g ⊗ h)
    id        : {a : obj} → hom a a
    unit-l    : {a b : obj} (f : hom a b) → id ⊗ f ≡ f
    unit-r    : {a b : obj} (f : hom a b) → f ⊗ id ≡ f
    pentagon  : {a b c d e : obj} (f : hom a b) (g : hom b c) (h : hom c d) (i : hom d e) →
                ap (λ f → f ⊗ i) (assoc f g h) ∙ assoc f (g ⊗ h) i ∙ ap (λ i → f ⊗ i) (assoc g h i) ≡ assoc (f ⊗ g) h i ∙ assoc f g (h ⊗ i)
    triangle  : {a b c : obj} (f : hom a b) (g : hom b c) →
                assoc f id g ∙ ap (λ g → f ⊗ g) (unit-l g) ≡ ap (λ f → f ⊗ g) (unit-r f)
    homs-gpd  : (a b : obj) → is-groupoid (hom a b)

module _ {ℓ ℓ'} (C : Bicategory {ℓ} {ℓ'}) where
  open Bicategory C

  _⊗₂_ : {a b c : obj} {f f' : hom a b} {g g' : hom b c} (ϕ : f ≡ f') (ψ : g ≡ g')→
         f ⊗ g ≡ f' ⊗ g'
  _⊗₂_ refl refl = refl

  ⊗₂-xch : {a b c : obj} {f f' f'' : hom a b} {g g' g'' : hom b c}
           (ϕ : f ≡ f') (ϕ' : f' ≡ f'') (ψ : g ≡ g') (ψ' : g' ≡ g'') →
           (ϕ ∙ ϕ') ⊗₂ (ψ ∙ ψ') ≡ (ϕ ⊗₂ ψ) ∙ (ϕ' ⊗₂ ψ')
  ⊗₂-xch refl refl refl refl = refl
