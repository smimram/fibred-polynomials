{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Equivalence where

open import HoTT.Base
open import HoTT.Path
open import HoTT.Homotopy

record is-equiv {i j} {A : Type i} {B : Type j} (f : A → B) : Type (lmax i j) where
  field
    g  : B → A
    g' : B → A
    g-f : (a : A) → g (f a) ≡ a
    f-g' : (b : B) → f (g' b) ≡ b

is-qinv : ∀ {i j} {A : Type i} {B : Type j} → (A → B) → Type (lmax i j)
is-qinv {A = A} {B = B} f = Σ (B → A) (λ g → (g ∘ f) ∼ id × (f ∘ g) ∼ id)

-- Investigate
-- https://lists.chalmers.se/pipermail/agda/2019/011004.html
qinv-to-equiv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} → is-qinv f → is-equiv f
-- qinv-to-equiv {A = A} {B = B} {f = f} (g , g-f , f-g') = record { g = g ; g-f = g-f ; f-g = f-g ; f-g-f = f-g-f }
  -- where
    -- f-g : (b : B) → f (g b) ≡ b
    -- f-g b = sym (ap (f ∘ g) (f-g' b)) ∙ ap f (g-f (g b)) ∙ f-g' b
    -- -- the following definition is abstract otherwise the typechecker sometimes takes too much time...
    -- abstract
      -- f-g-f : (a : A) → ap f (g-f a) ≡ f-g (f a)
      -- f-g-f a = begin
        -- ap f (g-f a) ≡⟨ ∙-unit-l _ ⟩
        -- refl ∙ ap f (g-f a) ≡⟨ ap2 _∙_ (sym (∙-inv-l (f-g' (f (g (f a)))))) refl ⟩
        -- (sym (f-g' (f (g (f a)))) ∙ f-g' (f (g (f a)))) ∙ ap f (g-f a) ≡⟨ ∙-assoc (sym (f-g' (f (g (f a))))) _ _ ⟩
        -- sym (f-g' (f (g (f a)))) ∙ f-g' (f (g (f a))) ∙ ap f (g-f a) ≡⟨ ap2 _∙_ (ap sym (sym (∼-natural-toid f-g' (f a)))) refl ⟩
        -- sym (ap (f ∘ g) (f-g' (f a))) ∙ f-g' (f (g (f a))) ∙ ap f (g-f a) ≡⟨ ap2 _∙_ (refl {x = sym (ap (λ z → f (g z)) (f-g' (f a)))}) (∼-natural (λ x → f-g' (f x)) (g-f a)) ⟩
        -- sym (ap (f ∘ g) (f-g' (f a))) ∙ ap (f ∘ (g ∘ f)) (g-f a) ∙ f-g' (f a) ≡⟨ ap2 _∙_ (refl {x = sym (ap (λ z → f (g z)) (f-g' (f a)))}) (ap2 _∙_ (ap-∘ (g ∘ f) f (g-f a)) (refl {x = f-g' (f a)})) ⟩
        -- sym (ap (f ∘ g) (f-g' (f a))) ∙ ap f (ap (g ∘ f) (g-f a)) ∙ f-g' (f a) ≡⟨ ap2 _∙_ (refl {x = sym (ap (f ∘ g) (f-g' (f a)))}) (ap2 _∙_ (ap (ap f) (∼-natural-toid g-f a)) refl) ⟩
        -- sym (ap (f ∘ g) (f-g' (f a))) ∙ ap f (g-f (g (f a))) ∙ f-g' (f a) ≡⟨ refl ⟩
        -- f-g (f a) ∎
        -- where open ≡-Reasoning
qinv-to-equiv (g , g-f , f-g) = record { g = g ; g' = g ; g-f = g-f ; f-g' = f-g }

id-is-equiv : ∀ {i} {A : Type i} → is-equiv (id {i} {A})
id-is-equiv = qinv-to-equiv (id , (λ x → refl) , (λ x → refl))

coe-is-equiv : ∀ {i} {A B : Type i} (p : A ≡ B) → is-equiv (coe p)
coe-is-equiv refl = id-is-equiv

∘-is-equiv : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C} → is-equiv f → is-equiv g → is-equiv (g ∘ f)
-- ∘-is-equiv {A = A} {C = C} {f = f} {g = g} f≃ g≃ = qinv-to-equiv (is-equiv.g f≃ ∘ is-equiv.g g≃ , (λ x → ap (is-equiv.g f≃) (is-equiv.g-f g≃ (f x)) ∙ is-equiv.g-f f≃ x) , λ x → ap g (is-equiv.f-g f≃ (is-equiv.g g≃ x)) ∙ is-equiv.f-g g≃ x)
  -- -- record { g = f' ∘ g' ; g-f = g-f ; f-g = f-g ; f-g-f = f-g-f }
  -- -- where
  -- -- f' = is-equiv.g f≃
  -- -- g' = is-equiv.g g≃
  -- -- g-f : (a : A) → f' (g' (g (f a))) ≡ a
  -- -- g-f a = ap f' (is-equiv.g-f g≃ (f a)) ∙ is-equiv.g-f f≃ a
  -- -- f-g : (c : C) → g (f (f' (g' c))) ≡ c
  -- -- f-g c = ap g (is-equiv.f-g f≃ (g' c)) ∙ is-equiv.f-g g≃ c
  -- -- f-g-f : (a : A) → ap (g ∘ f) (g-f a) ≡ f-g ((g ∘ f) a)
  -- -- f-g-f a = begin
    -- -- ap (g ∘ f) (g-f a) ≡⟨ refl ⟩
    -- -- ap (g ∘ f) (ap f' (is-equiv.g-f g≃ (f a)) ∙ is-equiv.g-f f≃ a) ≡⟨ ap-∙ (g ∘ f) (ap f' (is-equiv.g-f g≃ (f a))) (is-equiv.g-f f≃ a) ⟩
    -- -- ap (g ∘ f) (ap f' (is-equiv.g-f g≃ (f a))) ∙ ap (g ∘ f) (is-equiv.g-f f≃ a) ≡⟨ {!!} ⟩ -- g f f' g' g f
    -- -- ap (g ∘ f) (ap f' (is-equiv.g-f g≃ (f a))) ∙ ap (g ∘ f) (is-equiv.g-f f≃ a) ≡⟨ {!!} ⟩
    -- -- f-g ((g ∘ f) a) ∎
    -- -- where open ≡-Reasoning
∘-is-equiv F G = record { g = g F ∘ g G ; g' = g' F ∘ g' G ; g-f = {!!} ; f-g' = {!!} }
  -- η : g F (g G (g ∘ f)) ∼ id
  -- η = ?
  where open is-equiv

-- ≃-is-prop : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → is-prop (is-equiv f)
-- ≃-is-prop f = ?

_≃_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A ≃ B = Σ (A → B) is-equiv

equiv : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} (e : is-equiv f) → A ≃ B
equiv {f = f} e = f , e

≃→ : ∀ {i j} {A : Type i} {B : Type j} → A ≃ B → A → B
≃→ (f , _) = f

≃← : ∀ {i j} {A : Type i} {B : Type j} → A ≃ B → B → A
≃← (_ , e) = is-equiv.g e

≃η : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) (x : A) → ≃← E ((≃→ E) x) ≡ x
≃η (_ , e) = is-equiv.g-f e

≃ε : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) (x : B) → ≃→ E ((≃← E) x) ≡ x
≃ε (_ , e) = {!!}
-- is-equiv.f-g e

≃c : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) (x : A) → ap (≃→ E) (≃η E x) ≡ ≃ε E (≃→ E x)
≃c (_ , e) = {!!}
-- is-equiv.f-g-f e

≃→-inj : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) {x y : A} → ≃→ E x ≡ ≃→ E y → x ≡ y
≃→-inj E {x} {y} p = ! ≃η E x ∙ ap (≃← E) p ∙ ≃η E y

≃←-inj : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) {x y : B} → ≃← E x ≡ ≃← E y → x ≡ y
≃←-inj E p = ! ≃ε E _ ∙ ap (≃→ E) p ∙ ≃ε E _

-- ≃d : ∀ {i j} {A : Type i} {B : Type j} (E : A ≃ B) (x : B) → ap (≃← E) (≃ε E x) ≡ ≃η E (≃← E x)
-- ≃d (_ , e) = {!!}

≃-refl : ∀ {i} {A : Type i} → A ≃ A
≃-refl = equiv id-is-equiv

≃-trans : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → A ≃ B → B ≃ C → A ≃ C
≃-trans (f , f≃) (g , g≃) = (g ∘ f) , (∘-is-equiv f≃ g≃)

infix  15 _≃∎
infixr 10 _≃⟨_⟩_

_≃⟨_⟩_ : ∀ {i j k} (A : Type i) {B : Type j} {C : Type k} → A ≃ B → B ≃ C → A ≃ C
A ≃⟨ e ⟩ e' = ≃-trans e e'

_≃∎ : ∀ {i} (A : Type i) → A ≃ A
_ ≃∎ = ≃-refl

≃η-trans : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (E : A ≃ B) (F : B ≃ C) (x : A) → ≃η (≃-trans E F) x ≡ trans (ap (≃← E) (≃η F (≃→ E x))) (≃η E x)
≃η-trans E F x = refl

qinv : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) (g : B → A) → (g ∘ f) ∼ id → (f ∘ g) ∼ id → A ≃ B
qinv f g η ε = f , (qinv-to-equiv (g , η , ε))

≃-sym : ∀ {i j} {A : Type i} {B : Type j} → A ≃ B → B ≃ A
≃-sym E = qinv (≃← E) (≃→ E) (≃ε E) (≃η E)

≃-sym-refl : ∀ {i} {A : Type i} → ≃-sym (≃-refl {A = A}) ≡ ≃-refl
≃-sym-refl = refl

id-to-equiv : ∀ {i} {A B : Type i} → (A ≡ B) → (A ≃ B)
id-to-equiv p = coe p , coe-is-equiv p

id-to-equiv-∙ : ∀ {i} {A B C : Type i} (p : A ≡ B) (q : B ≡ C) → id-to-equiv (p ∙ q) ≡ ≃-trans (id-to-equiv p) (id-to-equiv q)
id-to-equiv-∙ refl refl = refl

≃-× : ∀ {i i' j j'} {A : Type i} {A' : Type i'} {B : Type j} {B' : Type j'} → A ≃ A' → B ≃ B' → (A × B) ≃ (A' × B')
≃-× f g = qinv (λ { (a , b) → (≃→ f a) , (≃→ g b)}) (λ { (a' , b') → (≃← f a') , (≃← g b')}) (λ { (a , b) → Σ-ext (≃η f a) {!!}}) {!!}

×-≃ : ∀ {i j} {A : Type i} {B : Type j} (x y : A × B) → (x ≡ y) ≃ ((fst x ≡ fst y) × (snd x ≡ snd y))
×-≃ x y = qinv f g (λ { refl → refl }) (λ { (refl , refl) → refl })
  where
  f : (x ≡ y) → ((fst x ≡ fst y) × (snd x ≡ snd y))
  f refl = refl , refl
  g : (fst x ≡ fst y) × (snd x ≡ snd y) → (x ≡ y)
  g (refl , refl) = refl

⊥-× : ∀ {i} {A : Type i} → (⊥ × A) ≃ ⊥
⊥-× = qinv (λ ()) (λ ()) (λ ()) λ ()

×-unit-l : ∀ {i} {A : Type i} → (⊤ × A) ≃ A
×-unit-l = qinv snd (λ a → tt , a) (λ { (tt , a) → refl }) λ _ → refl

≃-⊔ : ∀ {i j k l} {A : Type i} {A' : Type j} {B : Type k} {B' : Type l} → A ≃ A' → B ≃ B' → (A ⊔ B) ≃ (A' ⊔ B')
≃-⊔ ea eb = {!!}

⊔-unit-l : ∀ {i} {A : Type i} → (⊥ ⊔ A) ≃ A
⊔-unit-l {_} {A} = qinv f inr (λ { (inr x) → refl }) λ x → refl
  where
  f : ⊥ ⊔ A → A
  f (inr x) = x

⊔-assoc : ∀ {i} {A B C : Type i} → ((A ⊔ B) ⊔ C) ≃ (A ⊔ (B ⊔ C))
⊔-assoc {_} {A} {B} {C} = qinv f g (λ { (inl (inl a)) → refl ; (inl (inr b)) → refl ; (inr c) → refl}) λ { (inl a) → refl ; (inr (inl b)) → refl ; (inr (inr c)) → refl }
  where
  f : (A ⊔ B) ⊔ C → A ⊔ (B ⊔ C)
  f (inl (inl a)) = inl a
  f (inl (inr b)) = inr (inl b)
  f (inr c) = inr (inr c)
  g : A ⊔ (B ⊔ C) → (A ⊔ B) ⊔ C
  g (inl a) = inl (inl a)
  g (inr (inl b)) = inl (inr b)
  g (inr (inr c)) = inr c

⊔-comm : ∀ {i} {A B : Type i} → (A ⊔ B) ≃ (B ⊔ A)
⊔-comm = qinv f f (λ { (inl x) → refl ; (inr y) → refl }) (λ { (inl x) → refl ; (inr y) → refl })
  where
  f : ∀ {i} {A B : Type i} → (A ⊔ B) → (B ⊔ A)
  f (inl a) = inr a
  f (inr b) = inl b

⊔-× : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → ((A ⊔ B) × C) ≃ (A × C ⊔ B × C)
⊔-× {_} {_} {_} {A} {B} {C} = qinv f g (λ { (inl a , c) → refl ; (inr b , c) → refl }) λ { (inl (a , c)) → refl ; (inr (b , c)) → refl }
  where
  f : ((A ⊔ B) × C) → (A × C ⊔ B × C)
  f (inl a , c) = inl (a , c)
  f (inr b , c) = inr (b , c)
  g : (A × C ⊔ B × C) → ((A ⊔ B) × C)
  g (inl (a , c)) = (inl a) , c
  g (inr (b , c)) = (inr b) , c

Σ-⊔ : ∀ {i j} {A A' : Type i} {B : (A ⊔ A') → Type j} → Σ (A ⊔ A') B ≃ (Σ A (B ∘ inl) ⊔ Σ A' (B ∘ inr))
Σ-⊔ {_} {_} {A} {A'} {B} = qinv f g (λ { (inl a , b) → refl ; (inr a , b) → refl }) (λ { (inl (a , b)) → refl ; (inr (a , b)) → refl })
  where
  f : Σ (A ⊔ A') B → (Σ A (B ∘ inl) ⊔ Σ A' (B ∘ inr))
  f (inl a , b) = inl (a , b)
  f (inr a , b) = inr (a , b)
  g : (Σ A (B ∘ inl) ⊔ Σ A' (B ∘ inr)) → Σ (A ⊔ A') B
  g (inl (a , b)) = (inl a) , b
  g (inr (a , b)) = (inr a) , b

Σ-≡ : ∀ {i j} {A : Type i} {B : A → Type j} (x y : Σ A B) → (x ≡ y) ≃ (Σ (fst x ≡ fst y) (λ p → transport B p (snd x) ≡ snd y))
Σ-≡ {B = B} x y = qinv f g (λ { refl → refl }) (λ { (refl , refl) → refl })
  where
  f : (x ≡ y) → (Σ (fst x ≡ fst y) (λ p → transport B p (snd x) ≡ snd y))
  f refl = refl , refl
  g : (Σ (fst x ≡ fst y) (λ p → transport B p (snd x) ≡ snd y)) → (x ≡ y)
  g (refl , refl) = refl

-- TODO: is there a simpler formulation?
-- Σ-≡-ext : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B} → (p q : x ≡ y) (P : ap fst p ≡ ap fst q) → transport-ap B fst q (snd x) ∙ ! (ap (λ p → transport B p (snd x)) P) ∙ ! transport-ap B fst p (snd x) ∙ apd snd p ≡ apd snd q → p ≡ q
-- Σ-≡-ext refl q P Q = {!!}

Σ-≡-ext : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B} (p q : x ≡ y) (L : fst (≃→ (Σ-≡ x y) p) ≡ fst (≃→ (Σ-≡ x y) q)) (R : transport (λ p → transport B p (snd x) ≡ snd y) L (snd (≃→ (Σ-≡ x y) p)) ≡ snd (≃→ (Σ-≡ x y) q)) → p ≡ q
Σ-≡-ext {x = x} {y = y} p q L R = lem (Σ-ext L R)
  where
  lem : ≃→ (Σ-≡ x y) p ≡ ≃→ (Σ-≡ x y) q → p ≡ q
  lem P = ≃→-inj (Σ-≡ x y) P

-- Σ-≡₂ : ∀ {i j} {A : Type i} {B : A → Type j} {x y : Σ A B} (p q : x ≡ y) → (p ≡ q) ≃ Σ (≃→ (Σ-≡ x y) p ≡ ≃→ (Σ-≡ x y) q) {!(≃→ (Σ-≡ x y) p ≡ ≃→ (Σ-≡ x y) q)!}
-- Σ-≡₂ p q = {!!}

open ≡-Reasoning

Σ-≃-fst : ∀ {i j k} {A : Type i} {A' : Type j} {B : A' → Type k} (A≃ : A ≃ A') → Σ A (B ∘ (≃→ A≃)) ≃ Σ A' B
Σ-≃-fst {A = A} {B = B} A≃ = qinv
  (λ { (a , b) → ≃→ A≃ a , b })
  (λ { (a' , b) → ≃← A≃ a' , transport B (sym (≃ε A≃ a')) b })
  (λ { (a , b) → Σ-ext (≃η A≃ a) (
    begin
    transport (B ∘ ≃→ A≃) (≃η A≃ a) (transport B (sym (≃ε A≃ (≃→ A≃ a))) b) ≡⟨ transport-ap B (≃→ A≃) (≃η A≃ a) _ ⟩
    transport B (ap (≃→ A≃) (≃η A≃ a)) (transport B (sym (≃ε A≃ (≃→ A≃ a))) b) ≡⟨ sym (transport-∙ B (sym (≃ε A≃ (≃→ A≃ a))) (ap (≃→ A≃) (≃η A≃ a)) b) ⟩
    transport B (sym (≃ε A≃ (≃→ A≃ a)) ∙ ap (≃→ A≃) (≃η A≃ a)) b ≡⟨ ap (λ p → transport B p b) (zz a b) ⟩
    transport B refl b ≡⟨ refl ⟩
    b ∎
  ) })
  (λ { (a' , b) → Σ-ext (≃ε A≃ a') (
    begin
    transport B (≃ε A≃ a') (transport B (sym (≃ε A≃ a')) b) ≡⟨ sym (transport-∙ B (sym (≃ε A≃ a')) (≃ε A≃ a') b) ⟩
    transport B (sym (≃ε A≃ a') ∙ ≃ε A≃ a') b ≡⟨ ap (λ p → transport B p b) (∙-inv-l (≃ε A≃ a')) ⟩
    transport B refl b ≡⟨ refl ⟩
    b ∎
  ) })
  where
    zz : (a : A) (b : B (≃→ A≃ a)) → sym (≃ε A≃ (≃→ A≃ a)) ∙ ap (≃→ A≃) (≃η A≃ a) ≡ refl
    zz a b = begin
      sym (≃ε A≃ (≃→ A≃ a)) ∙ ap (≃→ A≃) (≃η A≃ a) ≡⟨ ap2 _∙_ refl (≃c A≃ a) ⟩
      sym (≃ε A≃ (≃→ A≃ a)) ∙ ≃ε A≃ (≃→ A≃ a) ≡⟨ ∙-inv-l (≃ε A≃ (≃→ A≃ a)) ⟩
      refl ∎

Σ-≃-snd : ∀ {i j} {A : Type i} {B : A → Type j} {B' : A → Type j} → ((a : A) → B a ≃ B' a) → Σ A B ≃ Σ A B'
Σ-≃-snd {B = B} {B' = B'} B≃ = qinv
  (λ { (a , b) → a , (≃→ (B≃ a) b) })
  (λ { (a , b) → a , (≃← (B≃ a) b) })
  (λ { (a , b) → Σ-ext refl (≃η (B≃ a) b) })
  (λ { (a , b) → Σ-ext refl (≃ε (B≃ a) b) })

Σ-≃ : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j} (A≃ : A ≃ A') (B≃ : (a : A) → B a ≃ B' (≃→ A≃ a)) → Σ A B ≃ Σ A' B'
Σ-≃ {B = B} {B' = B'} A≃ B≃ = ≃-trans (Σ-≃-snd B≃) (Σ-≃-fst A≃)

-- Σ-≃→ : ∀ {i j} {A A' : Type i} {B : A → Type j} {B' : A' → Type j} (A≃ : A ≃ A') (B≃ : (a : A) → B a ≃ B' (≃→ A≃ a)) → ≃→ (Σ-≃ A≃ B≃) ≡ λ { (a , b) → ≃→ A≃ a , ≃→ (B≃ a) b }
-- Σ-≃→ A≃ B≃ = refl

Σ-≃-swap : ∀ {i j k} {A : Type i} {A' : Type j} {B : A → A' → Type k} → (Σ A λ a → Σ A' λ a' → B a a') ≃ (Σ A' λ a' → Σ A λ a → B a a')
Σ-≃-swap = qinv (λ { (a , a' , b) → a' , a , b }) (λ { (a' , a , b) → a , a' , b }) (λ _ → refl) (λ _ → refl)

Lift-≃ : ∀ {i j} {A : Type i} → A ≃ Lift {j} A
Lift-≃ = qinv lift (λ { (lift x) → x }) (λ _ → refl) (λ _ → refl)
