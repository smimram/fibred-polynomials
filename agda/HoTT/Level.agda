{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT.Base
open import HoTT.Path
open import HoTT.Univalence
open import HoTT.Equivalence

open ≡-Reasoning

module HoTT.Level where

is-empty-≃-⊥ : ∀ {i} {A : Type i} → ¬ A → A ≃ ⊥
is-empty-≃-⊥ ¬A = qinv ¬A (λ ()) (λ x → ⊥-elim (¬A x)) λ ()

--- Contr

is-contr : ∀ {i} (A : Type i) → Type i
is-contr A = Σ A (λ a₀ → (a₁ : A) → a₀ ≡ a₁)

⊤-is-contr : is-contr ⊤
⊤-is-contr = tt , (λ { tt → refl })

is-contr-≃-⊤ : ∀ {i} {A : Type i} → is-contr A → A ≃ ⊤
is-contr-≃-⊤ (a , p) = qinv (λ x → tt) (λ { tt → a }) (λ x → p x) λ { tt → refl }

--- Prop

is-prop : ∀ {i} (A : Type i) → Type i
is-prop A = (x y : A) → x ≡ y

⊤-is-prop : is-prop ⊤
⊤-is-prop tt tt = refl

×-is-prop : ∀ {i j} {A : Type i} {B : Type j} → is-prop A → is-prop B → is-prop (A × B)
×-is-prop PA PB (x , y) (x' , y') = ≃← (×-≃ _ _) (PA x x' , PB y y')

Σ-is-prop : ∀ {i j} {A : Type i} {B : A → Type j} → is-prop A → ((x : A) → is-prop (B x)) → is-prop (Σ A B)
Σ-is-prop {B = B} AP BP (a , b) (a' , b') = Σ-ext (AP a a') (BP a' (transport B (AP a a') b) b')

→-is-prop : ∀ {i j} {A : Type i} {B : Type j} → (is-prop B) → is-prop (A → B)
→-is-prop P f g = funext λ x → P (f x) (g x)

Π-is-prop : ∀ {i j} {A : Type i} {B : A → Type j} → ((x : A) → is-prop (B x)) → is-prop (Π A B)
Π-is-prop P f g = funext λ x → P x (f x) (g x)

hProp : ∀ {i} → Type (lsuc i)
hProp {i} = Σ (Type i) is-prop

is-contr-is-prop : ∀ {i} {A : Type i} → is-contr A → is-prop A
is-contr-is-prop (x , p) y z = ! p y ∙ p z

is-prop-≃ : ∀ {i j} {A : Type i} {B : Type j} → (A ≃ B) → is-prop A → is-prop B
-- is-prop-≃ e PA x y = ! ≃ε e x ∙ ap (≃→ e) (PA (≃← e x) (≃← e y)) ∙ ≃ε e y
is-prop-≃ e PA x y = ≃←-inj e (PA (≃← e x) (≃← e y))

--- Set

is-set : ∀ {i} (A : Type i) → Type i
is-set A = (x y : A) → is-prop (x ≡ y)

is-prop-is-set : ∀ {i} {A : Type i} → is-prop A → is-set A
is-prop-is-set {A = A} P x y p q = lem x p ∙ ! (lem x q)
  where
  lem : (z : A) (p : x ≡ y) → p ≡ P x z ∙ ! (P y z)
  lem z refl = ! (∙-inv-r (P x z))

is-prop-is-contr : ∀ {i} (A : Type i) → is-prop (is-contr A)
is-prop-is-contr A (x , p) (y , q) = Σ-ext (p y) (funext λ z → is-prop-is-set (is-contr-is-prop (x , p)) y z _ (q z))

is-prop-is-prop : ∀ {i} (A : Type i) → is-prop (is-prop A)
is-prop-is-prop A P Q = funext2 λ x y → is-prop-is-set P x y (P x y) (Q x y)

hom-prop-is-contr : ∀ {i} {A : Type i} → is-prop A → (x y : A) → is-contr (x ≡ y)
hom-prop-is-contr PA x y = (PA x y) , (λ p → is-prop-is-set PA x y _ p)

is-dec : ∀ {i} (A : Type i) → Type i
is-dec A = ¬ A ⊔ A

is-dec-≡ : ∀ {i} (A : Type i) → Type i
is-dec-≡ A = (x y : A) → is-dec (x ≡ y)

postulate
  hedberg : ∀ {i} (A : Type i) → is-dec-≡ A → is-set A
-- hedberg A = {!!}

open import Data.Bool

Bool-is-dec-≡ : is-dec-≡ Bool
Bool-is-dec-≡ false false = inr refl
Bool-is-dec-≡ false true  = inl λ ()
Bool-is-dec-≡ true  false = inl λ ()
Bool-is-dec-≡ true  true  = inr refl

Bool-is-set : is-set Bool
Bool-is-set false false refl refl = refl
Bool-is-set false true ()
Bool-is-set true false ()
Bool-is-set true true refl refl = refl

open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties using (suc-injective)

ℕ-is-dec-≡ : is-dec-≡ ℕ
ℕ-is-dec-≡ zero zero = inr refl
ℕ-is-dec-≡ zero (suc n) = inl λ ()
ℕ-is-dec-≡ (suc m) zero = inl λ ()
ℕ-is-dec-≡ (suc m) (suc n) with ℕ-is-dec-≡ m n
... | inl d = inl λ p → d (suc-injective p)
... | inr d = inr (ap suc d)

-- ℕ-is-set : is-set ℕ
-- ℕ-is-set = hedberg ℕ ℕ-is-dec-≡

ℕ-is-set : is-set ℕ
ℕ-is-set zero zero refl refl = refl
ℕ-is-set (suc m) (suc n) p q =
  p                  ≡⟨ ! lem p ⟩
  ap suc (ap pred p) ≡⟨ ap (ap suc) (ℕ-is-set m n (ap pred p) (ap pred q)) ⟩
  ap suc (ap pred q) ≡⟨ lem q ⟩
  q                  ∎
  where
    open ≡-Reasoning
    lem : {m n : ℕ} (p : suc m ≡ suc n) → ap suc (ap pred p) ≡ p
    lem refl = refl

×-is-set : ∀ {i j} {A : Type i} {B : Type j} → is-set A → is-set B → is-set (A × B)
×-is-set SA SB x y = transport is-prop (! ua (×-≃ x y)) (×-is-prop (SA _ _) (SB _ _))

Σ-is-set : ∀ {i j} {A : Type i} {B : A → Type j} → is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
Σ-is-set {A = A} {B = B} AS BS (a , b) (a' , b') p q = Σ-≡-ext p q
  (AS a a' (fst (≃→ (Σ-≡ (a , b) (a' , b')) p)) (fst (≃→ (Σ-≡ (a , b) (a' , b')) q)))
  (BS a' _ b' (transport (λ p₁ → transport B p₁ b ≡ b') (AS a a' (fst (≃→ (Σ-≡ (a , b) (a' , b')) p)) (fst (≃→ (Σ-≡ (a , b) (a' , b')) q))) (snd (≃→ (Σ-≡ (a , b) (a' , b')) p))) (snd (≃→ (Σ-≡ (a , b) (a' , b')) q)))

→-is-set : ∀ {i j} {A : Type i} {B : Type j} → is-set B → is-set (A → B)
→-is-set S f g p q = funext-≡ p q λ x → S (f x) (g x) (happly p x) (happly q x)

-- 7.1.9
Π-is-set : ∀ {i j} {A : Type i} {B : A → Type j} → ((x : A) → is-set (B x)) → is-set (Π A B)
Π-is-set S f g p q = funext-≡ p q λ x → S x (f x) (g x) (happly p x) (happly q x)

is-set-≃ : ∀ {i j} {A : Type i} {B : Type j} → (A ≃ B) → is-set A → is-set B
is-set-≃ e S x y p q = P₅
  where
  P₁ : ap (≃← e) p ≡ ap (≃← e) q
  P₁ = S _ _ (ap (≃← e) p) (ap (≃← e) q)
  P₂ : ap (≃→ e) (ap (≃← e) p) ≡ ap (≃→ e) (ap (≃← e) q)
  P₂ = (ap (ap (≃→ e)) P₁)
  P₃ : ap ((≃→ e) ∘ (≃← e)) p ≡ ap ((≃→ e) ∘ (≃← e)) q
  P₃ = ap-∘ _ _ p ∙ P₂ ∙ ! ap-∘ _ _ q
  P₄ : ap id p ≡ ap id q
  P₄ = transport (λ f → ap f p ≡ ap f q) (funext (λ b → ≃ε e b)) P₃
  P₅ : p ≡ q
  P₅ = transport (λ f → f p ≡ f q) (funext (λ p → ap-id p)) P₄

is-set-is-prop : ∀ {i} (A : Type i) → is-prop (is-set A)
is-set-is-prop A P Q = funext2 λ x y → is-prop-is-prop (x ≡ y) (P x y) (Q x y)

prop-equiv : ∀ {i j} {A : Type i} {B : Type j} → is-prop A → is-prop B → (A → B) → (B → A) → A ≃ B
prop-equiv PA PB f g = qinv f g (λ x → PA (g (f x)) x) (λ y → PB (f (g y)) y)

hSet : Type₁
hSet = Σ Type₀ is-set

hSet≡ : {A B : hSet} → (fst A ≡ fst B) → A ≡ B
hSet≡ {A} {B} p = Σ-ext p (is-set-is-prop (fst B) (transport is-set p (snd A)) (snd B))

hSet≡-refl : {A : hSet} → hSet≡ {A = A} {B = A} refl ≡ refl
hSet≡-refl {A} = Σ-ext-ext refl (is-prop-is-set (is-set-is-prop (fst A)) (transport is-set refl (snd A)) (snd A) _ refl)

hSet≡-≡ : {A B : hSet} {p q : fst A ≡ fst B} → p ≡ q → hSet≡ {A = A} {B = B} p ≡ hSet≡ q
hSet≡-≡ refl = refl

postulate
  hSet≡-∙ : {A B C : hSet} (p : fst A ≡ fst B) (q : fst B ≡ fst C) → hSet≡ {A = A} {B = C} (p ∙ q) ≡ hSet≡ {B = B} p ∙ hSet≡ q
-- hSet≡-∙ refl refl = {!hSet≡ (refl ∙ refl) ≡⟨ ? ⟩ hSet≡ refl ∙ hSet≡ refl ∎!}
-- hSet≡-∙ {A} {.(fst A) , s} {.(fst A) , t} refl refl with is-set-is-prop (fst A) (snd A) s | is-set-is-prop (fst A) (snd A) t
-- ... | refl | refl = {!hSet≡ (refl ∙ refl) ≡⟨ ? ⟩ hSet≡ refl ∙ hSet≡ refl ∎!}

--- Groupoid

is-groupoid : ∀ {i} (A : Type i) → Type i
is-groupoid A = (x y : A) → is-set (x ≡ y)

Σ-is-groupoid : ∀ {i j} {A : Type i} {B : A → Type j} → is-groupoid A → ((x : A) → is-groupoid (B x)) → is-groupoid (Σ A B)
Σ-is-groupoid GA GB (a , b) (a' , b') = transport is-set (! ua (Σ-≡ (a , b) (a' , b'))) (Σ-is-set (GA a a') (λ p → GB a' _ b'))

is-set-is-groupoid : ∀ {i} {A : Type i} → is-set A → is-groupoid A
is-set-is-groupoid S x y = is-prop-is-set (S x y)

is-prop-is-groupoid : ∀ {i} {A : Type i} → is-prop A → is-groupoid A
is-prop-is-groupoid = is-set-is-groupoid ∘ is-prop-is-set

is-groupoid-is-prop : ∀ {i} (A : Type i) → is-prop (is-groupoid A)
is-groupoid-is-prop A P Q = funext2 λ x y → is-set-is-prop (x ≡ y) (P x y) (Q x y)

-- 7.1.9
Π-is-groupoid : ∀ {i j} {A : Type i} {B : A → Type j} → ((x : A) → is-groupoid (B x)) → is-groupoid (Π A B)
Π-is-groupoid G f g = transport is-set (! ua (equiv (function-extensionality f g))) (Π-is-set (λ x → G x (f x) (g x)))

→-is-groupoid : ∀ {i j} {A : Type i} {B : Type j} → (is-groupoid B) → is-groupoid (A → B)
→-is-groupoid GB = Π-is-groupoid (λ _ → GB)

--- Propositional truncation

postulate
  ∥_∥ : ∀ {i} → Type i → Type i
  ∥∥-is-prop : ∀ {i} {A : Type i} → is-prop ∥ A ∥
  ∣_∣ : ∀ {i} {A : Type i} → A → ∥ A ∥
  ∥∥-rec : ∀ {i j} {A : Type i} {B : Type j} → is-prop B → (A → B) → ∥ A ∥ → B
  ∥∥-comp : ∀ {i j} {A : Type i} {B : Type j} (P : is-prop B) (f : A → B) (x : A) → ∥∥-rec P f ∣ x ∣ ≡ f x
  ∥∥-eta : ∀ {i} {A : Type i} (P : is-prop A) (x : ∥ A ∥) → ∣ ∥∥-rec P id x ∣ ≡ x

∥∥-rec2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → is-prop C → (A → B → C) → ∥ A ∥ → ∥ B ∥ → C
∥∥-rec2 {B = B} {C = C} P f = ∥∥-rec (→-is-prop P) λ x → ∥∥-rec P (f x)

{-# REWRITE ∥∥-comp #-}
{-# REWRITE ∥∥-eta #-}
