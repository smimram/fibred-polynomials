{-# OPTIONS --without-K --allow-unsolved-metas --rewriting #-}

module HoTT.Path where

open import HoTT.Base

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

infixl 40 ap
syntax ap f p = p |in-ctx f

ap-id : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → ap id p ≡ p
ap-id refl = refl

ap-cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) {x y : A} (p : x ≡ y) → ap (λ _ → b) p ≡ refl
ap-cst b refl = refl

ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ f g refl = refl

ap2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → B → C) {a a' b b'} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
ap2 f refl refl = refl

happly : ∀ {i j} {A : Type i} {B : A → Type j} {f g : (x : A) → B x} (p : f ≡ g) (x : A) → f x ≡ g x
happly refl x = refl

happly-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {f f' : A → B} (g : B → C) (p : f ≡ f') (x : A) → happly (ap (λ f → g ∘ f) p) x ≡ ap g (happly p x)
happly-ap g refl x = refl

happly-ap' : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {g g' : B → C} (p : g ≡ g') (f : A → B) (x : A) → happly (ap (λ g → g ∘ f) p) x ≡ happly p (f x)
happly-ap' refl f x = refl

transport : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) → x ≡ y → B x → B y
transport B refl b = b

transport2-nd : ∀ {i j k} {A : Type i} {B : Type j} {a a' : A} {b b' : B} (C : A → B → Type k) → a ≡ a' → b ≡ b' → C a b → C a' b'
transport2-nd {a' = a'} {b = b} C p q c = transport (λ b → C a' b) q (transport (λ a → C a b) p c)

transport3-nd : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {a a' : A} {b b' : B} {c c' : C} (D : A → B → C → Type l) → a ≡ a' → b ≡ b' → c ≡ c' → D a b c → D a' b' c'
transport3-nd {a' = a'} {b = b} {b' = b'} {c = c} D p q r d = transport (λ c → D a' b' c) r (transport (λ b → D a' b c) q (transport (λ a → D a b c) p d))

transport2 : ∀ {i j k} {A : Type i} {B : A → Type j} {a a' : A} {b : B a} {b' : B a'} (C : (a : A) → B a → Type k) (p : a ≡ a') → transport B p b ≡ b' → C a b → C a' b'
transport2 C refl refl c = c

transport-cst : ∀ {i j} {A : Type i} {x y : A} {B : Type j} (p : x ≡ y) (b : B) → transport (λ _ → B) p b ≡ b
transport-cst refl b = refl

transport-ap : ∀ {i i' j} {A : Type i} {A' : Type i'} {x y : A} (B : A' → Type j) (f : A → A') (p : x ≡ y) (t : B (f x)) → transport (B ∘ f) p t ≡ transport B (ap f p) t
transport-ap B f refl t = refl

transport-ap-ext : ∀ {i i' j} {A : Type i} {A' : Type i'} {x y : A} (B : A' → Type j) (f : A → A') (p : x ≡ y) → transport (B ∘ f) p ≡ transport B (ap f p)
transport-ap-ext B f refl = refl

transport-nat : ∀ {i j k} {A : Type i} {a a' : A} (B : A → Type j) (B' : A → Type k) (f : {a : A} → B a → B' a) (p : a ≡ a') (x : B a) → transport B' p (f x) ≡ f (transport B p x)
transport-nat B B' f refl x = refl

coe : ∀ {i} {A B : Type i} → A ≡ B → A → B
coe p = transport (λ A → A) p

coe-ap : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y) → coe (ap B p) ≡ transport B p
coe-ap B refl = refl


coe-injective : ∀ {i} {A B : Type i} (p : A ≡ B) {x y : A} → coe p x ≡ coe p y → x ≡ y
coe-injective refl q = q

transport-arg : ∀ {i j} {A A' : Type i} {B : Type j} (p : A ≡ A') (f : A → B) → transport (λ A → A → B) p f ≡ λ x → f (coe (sym p) x)
transport-arg refl f = refl

infixr 80 _∙_

_∙_ : ∀ {i} {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
_∙_ = trans

infix 100 !_

!_ : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → y ≡ x
!_ = sym

!-! : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → ! ! p ≡ p
!-! refl = refl

∙-unit-l : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
∙-unit-l p = refl

∙-unit-r : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
∙-unit-r refl = refl

∙-inv-l : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → ! p ∙ p ≡ refl
∙-inv-l refl = refl

∙-inv-r : ∀ {i} {A : Type i} {x y : A} (p : x ≡ y) → p ∙ ! p ≡ refl
∙-inv-r refl = refl

∙-sym : ∀ {i} {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ! (p ∙ q) ≡ ! q ∙ ! p
∙-sym p refl = ap sym (∙-unit-r p)

∙-assoc : ∀ {i} {A : Type i} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
∙-assoc refl q r = refl

ap-∙ : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f refl q = refl

ap-! : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A} (p : x ≡ y) → ap f (! p) ≡ (! ap f p)
ap-! f refl = refl

coe-∙! : ∀ {i} {A B : Type i} (e : A ≡ B) (x : B) → (coe e (coe (! e) x) ≡ x)
coe-∙! refl x = refl
coe-!∙ : ∀ {i} {A B : Type i} (p : B ≡ A) (x : B) → coe (! p) (coe p x) ≡ x
coe-!∙ refl x = refl

sym-ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A} (p : x ≡ y) → sym (ap f p) ≡ ap f (sym p)
sym-ap f refl = refl

transport-∙ : ∀ {i j} {A : Type i} {x y z : A} (B : A → Type j) (p : x ≡ y) (q : y ≡ z) (b : B x) → transport B (p ∙ q) b ≡ transport B q (transport B p b)
transport-∙ B refl refl b = refl


transport-∙-ext : ∀ {i j} {A : Type i} {x y z : A} (B : A → Type j) (p : x ≡ y) (q : y ≡ z) → transport B (p ∙ q) ≡ (transport B q) ∘ (transport B p)
transport-∙-ext B refl refl = refl

coe-∙ : ∀ {i} {A B C : Type i} (p : A ≡ B) (q : B ≡ C) → coe (p ∙ q) ≡ coe q ∘ coe p
coe-∙ refl q = refl

transport-≡-ap : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x) → transport (λ x → f x ≡ g x) p q ≡ ! ap f p ∙ q ∙ ap g p
transport-≡-ap f g refl q = ! ∙-unit-r q

transport-≡-l : ∀ {i} {A : Type i} {x y : A} (a : A) (p : x ≡ y) (q : x ≡ a) → transport (λ x → x ≡ a) p q ≡ ! p ∙ q
transport-≡-l a refl refl = ! ∙-inv-r refl

transport-≡-r : ∀ {i} {A : Type i} {x y : A} (a : A) (p : x ≡ y) (q : a ≡ x) → transport (λ x → a ≡ x) p q ≡ q ∙ p
transport-≡-r a refl refl = refl

-- 2.9.4
transport-→ : ∀ {i j k} {X : Type i} (A : X → Type j) (B : X → Type k) {x y : X} (p : x ≡ y) (f : A x → B x) → transport (λ x → A x → B x) p f ≡ (transport B p) ∘ f ∘ (transport A (! p))
transport-→ A B refl f = refl

transport-inv : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y) (b : B y) → transport B p (transport B (! p) b) ≡ b
transport-inv B p b = ! transport-∙ B (! p) p b ∙ ap (λ q → transport B q b) (∙-inv-l p)

transport-inv' : ∀ {i j} {A : Type i} {x y : A} (B : A → Type j) (p : x ≡ y) (b : B x) → transport B (! p) (transport B p b) ≡ b
transport-inv' B p b = ! transport-∙ B p (! p) b ∙ ap (λ q → transport B q b) (∙-inv-r p)

-- 2.9.5
transport-Π : ∀ {i j k} {X : Type i} (A : X → Type j) (B : (x : X) → A x → Type k) {x y : X} (p : x ≡ y) (f : (a : A x) → B x a) → transport (λ x → (a : A x) → B x a) p f ≡ λ a → transport2 B p (transport-inv A p a) (f (transport A (! p) a))
transport-Π A B refl f = refl

×-ext : ∀ {i j} {A : Type i} {B : Type j} {x y : A × B} (p : fst x ≡ fst y) (q : snd x ≡ snd y) → x ≡ y
×-ext refl refl = refl

module _  {i j} {A : Type i} {B : A → Type j} where
  Σ-ext : {x y : Σ A B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → x ≡ y
  Σ-ext refl refl = refl

  Σ-ext-∙ : {x y z : Σ A B} → (p : fst x ≡ fst y) (p' : fst y ≡ fst z) (q : transport B p (snd x) ≡ snd y) (q' : transport B p' (snd y) ≡ snd z) →
            Σ-ext (p ∙ p') (transport-∙ B p p' (snd x) ∙ ap (transport B p') q ∙ q') ≡ Σ-ext p q ∙ Σ-ext p' q'
  Σ-ext-∙ refl refl refl refl = refl

  Σ-ext-fst : {x y : Σ A B} → (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → ap fst (Σ-ext p q) ≡ p
  Σ-ext-fst refl refl = refl

  Σ-ext-! : {x y : Σ A B} (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → ! (Σ-ext p q)  ≡ Σ-ext (! p) ((ap (transport B (! p)) (! q)) ∙ (transport-inv' B p (snd x))) 
  Σ-ext-! refl refl = refl

  -- Σ-ext-snd : {x y : Σ A B} → (p : fst x ≡ fst y) (q : transport B p (snd x) ≡ snd y) → {!Σ-ext p q!} ≡ q
  -- Σ-ext-snd refl refl = refl

  Σ-ext-ext : {x y : Σ A B} {p p' : fst x ≡ fst y} {q : transport B p (snd x) ≡ snd y} {q' : transport B p' (snd x) ≡ snd y} (P : p ≡ p') (Q : transport (λ p → transport B p (snd x) ≡ snd y) P q ≡ q') →
              Σ-ext p q ≡ Σ-ext p' q'
  Σ-ext-ext refl refl = refl

  --- 2.3.2
  Σ-lift : {x y : A} (b : B x) (p : x ≡ y) → (x , b) ≡ (y , transport B p b)
  Σ-lift b p = Σ-ext p refl

--- 2.7.4
transport-Σ :
  ∀ {i j k} {X : Type i} (A : X → Type j) (B : (x : X) → A x → Type k) {x y : X} (p : x ≡ y) (u : Σ (A x) (B x)) →
  transport (λ x → Σ (A x) (B x)) p u ≡ ((transport A p (fst u)) , transport2 B p refl (snd u))
transport-Σ A B refl u = refl

-- transport-Σ-fst :
  -- ∀ {i j k} {X : Type i} (A : X → Type j) (B : (x : X) → A x → Type k) {x y : X} (p : x ≡ y) (u : Σ (A x) (B x)) →
  -- ap fst (transport-Σ A B p u) ≡ {!!}
-- transport-Σ-fst = {!!}

apd : ∀ {i j} {A : Type i} {B : A → Type j} {x y : A} (f : (x : A) → B x) (p : x ≡ y) → transport B p (f x) ≡ f y
apd f refl = refl

-- Lemma 2.3.8
apd-nd : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B) (p : x ≡ y) → apd f p ≡ transport-cst p (f x) ∙ ap f p
apd-nd f refl = refl

apnd : ∀ {i j} {A : Type i} {B : Type j} {x y : A} (f : A → B) (p : x ≡ y) → ap f p ≡ ! transport-cst p (f x) ∙ apd f p
apnd f refl = refl

ap-transport-cst : ∀ {i j k} {A : Type i} {x y : A} {B : Type j} {B' : Type k} (f : B → B') (p : x ≡ y) (b : B) → ap f (transport-cst p b) ≡ ! transport-nat (λ _ → B) (λ _ → B') f p b ∙ transport-cst p (f b)
ap-transport-cst f refl b = refl

--- Equivalences

hfib : ∀ {i j} {A : Type i} {B : Type j} → (f : A → B) → B → Type (lmax i j)
hfib {A = A} f b = Σ A (λ a → f a ≡ b)

⊔-ext : ∀ {i j} {A A' : Type i} {B B' : Type j} → A ≡ A' → B ≡ B' → (A ⊔ B) ≡ (A' ⊔ B')
⊔-ext refl refl = refl
