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
  is-eq : {a b : obj} (f : hom a b) → Type larrow
  is-eq {a} {b} f = Σ (hom b a) (λ g → Σ (hom b a) (λ g' → (f ⊗ g ≡ id) × (g' ⊗ f ≡ id)))
  id-is-eq : {a : obj} → is-eq (id {a})
  id-is-eq = id , id , unit-l id , unit-l id
  _≃ᵇ_ : (a b : obj) → Type larrow
  a ≃ᵇ b = Σ (hom a b) is-eq
  id-to-eq : {a b : obj} → a ≡ b → a ≃ᵇ b
  id-to-eq p = J (λ a b p → a ≃ᵇ b) (λ a → id , id-is-eq) p
  field
    univ : {a b : obj} → is-equiv (id-to-eq {a} {b})

module _ {ℓ ℓ'} (C : Bicategory {ℓ} {ℓ'}) where
  open Bicategory C

  _⊗₂_ : {a b c : obj} {f f' : hom a b} {g g' : hom b c} (ϕ : f ≡ f') (ψ : g ≡ g')→
         f ⊗ g ≡ f' ⊗ g'
  _⊗₂_ refl refl = refl

  ⊗₂-xch : {a b c : obj} {f f' f'' : hom a b} {g g' g'' : hom b c}
           (ϕ : f ≡ f') (ϕ' : f' ≡ f'') (ψ : g ≡ g') (ψ' : g' ≡ g'') →
           (ϕ ∙ ϕ') ⊗₂ (ψ ∙ ψ') ≡ (ϕ ⊗₂ ψ) ∙ (ϕ' ⊗₂ ψ')
  ⊗₂-xch refl refl refl refl = refl

  record Cartesian : Type (lsuc (lmax ℓ ℓ')) where
    field
      _⊕_ : obj  → obj → obj
      proj-l : {a b : obj} → hom (a ⊕ b) a
      proj-r : {a b : obj} → hom (a ⊕ b) b
    split : {a b c : obj} → hom a (b ⊕ c) → hom a b × hom a c
    split f = (f ⊗ proj-l) , (f ⊗ proj-r)
    field
      prod : {a b c : obj} → is-equiv (split {a} {b} {c})
      t : obj
      term : {a : obj} → hom a t ≡ Lift ⊤
