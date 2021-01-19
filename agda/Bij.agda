{-# OPTIONS --without-K --rewriting --allow-unsolved-meta #-}

--
--  The type of finite types and bijections
--

module Bij where

open import HoTT
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import FinType
open PathOver

open ≡-Reasoning

postulate
  𝔹 : Type₀

  obj : ℕ → 𝔹
  hom : {m n : ℕ} (α : Fin m ≃ Fin n) → obj m ≡ obj n

  id-coh : (n : ℕ) → hom {n = n} ≃-refl ≡ refl 
  comp-coh : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom (≃-trans α β) ≡ hom α ∙ hom β

  -- TODO: we should be able to prove this one by uniqueness of inverses
  inv-coh : {m n : ℕ} (α : Fin m ≃ Fin n) → hom (≃-sym α) ≡ ! hom α

  𝔹-is-groupoid : is-groupoid 𝔹

  𝔹-ind : ∀ {i} (P : 𝔹 → Type i)
    → (is-grp : (b : 𝔹) → is-groupoid (P b))
    → (obj* : (n : ℕ) → P (obj n))
    → (hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → obj* m ≡ obj* n [ P ↓ hom α ])
    → (id-coh* : (n : ℕ) → hom* ≃-refl ≡ refl [ (λ p → obj* n ≡ obj* n [ P ↓ p ]) ↓ id-coh n ])
    → (comp-coh* : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom* (≃-trans α β) ≡ po-trans (hom* α) (hom* β) [ (λ p → obj* m ≡ obj* o [ P ↓ p ]) ↓ comp-coh α β ])
    → (b : 𝔹) → P b

-- non-dependent version
𝔹-rec : ∀ {i} (P : Type i)
  → (is-grp : is-groupoid P)
  → (obj* : (n : ℕ) → P)
  → (hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → obj* m ≡ obj* n)
  → (id-coh* : (n : ℕ) → hom* {n = n} ≃-refl ≡ refl)
  → (comp-coh* : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom* (≃-trans α β) ≡ hom* α ∙ hom* β)
  → (b : 𝔹) → P
𝔹-rec P is-grp obj* hom* id-coh* comp-coh* b =
  𝔹-ind
    (λ _ → P)
    (λ _ → is-grp)
    obj*
    (λ α → po-cst (hom* α))
    (λ n → po-cst₂ (id-coh* n))
    (λ α β → po-≡-r (po-cst₂ (comp-coh* α β)) (po-cst-∙ {p = hom α} {p' = hom β} (hom* α) (hom* β)))
    b

--
--  Rewrites for computation rules....
-- 

postulate
  𝔹-obj-comp : ∀ {i} (P : 𝔹 → Type i)
    → (is-grp : (b : 𝔹) → is-groupoid (P b))
    → (obj* : (n : ℕ) → P (obj n))
    → (hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → obj* m ≡ obj* n [ P ↓ hom α ])
    → (id-coh* : (n : ℕ) → hom* ≃-refl ≡ refl [ (λ p → obj* n ≡ obj* n [ P ↓ p ]) ↓ id-coh n ])
    → (comp-coh* : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom* (≃-trans α β) ≡ po-trans (hom* α) (hom* β) [ (λ p → obj* m ≡ obj* o [ P ↓ p ]) ↓ comp-coh α β ])
    → (n : ℕ)
    → 𝔹-ind P is-grp obj* hom* id-coh* comp-coh* (obj n) ≡ obj* n

  {-# REWRITE 𝔹-obj-comp #-}

  𝔹-hom-comp : ∀ {i} (P : 𝔹 → Type i)
    → (is-grp : (b : 𝔹) → is-groupoid (P b))
    → (obj* : (n : ℕ) → P (obj n))
    → (hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → obj* m ≡ obj* n [ P ↓ hom α ])
    → (id-coh* : (n : ℕ) → hom* ≃-refl ≡ refl [ (λ p → obj* n ≡ obj* n [ P ↓ p ]) ↓ id-coh n ])
    → (comp-coh* : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom* (≃-trans α β) ≡ po-trans (hom* α) (hom* β) [ (λ p → obj* m ≡ obj* o [ P ↓ p ]) ↓ comp-coh α β ])
    → {m n : ℕ}
    → (α : Fin m ≃ Fin n)
    → apo (𝔹-ind P is-grp obj* hom* id-coh* comp-coh*) (hom α) ≡ hom* α

  {-# REWRITE 𝔹-hom-comp #-}

  -- TODO: prove this from 𝔹-hom-comp
  𝔹-hom-comp-nd : ∀ {i} (P : Type i)
    → (is-grp : is-groupoid P)
    → (obj* : (n : ℕ) → P)
    → (hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → obj* m ≡ obj* n)
    → (id-coh* : (n : ℕ) → hom* ≃-refl ≡ refl)
    → (comp-coh* : {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) → hom* (≃-trans α β) ≡ hom* α ∙ hom* β)
    → {m n : ℕ}
    → (α : Fin m ≃ Fin n)
    → ap (𝔹-rec P is-grp obj* hom* id-coh* comp-coh*) (hom α) ≡ hom* α
-- 𝔹-hom-comp-nd P is-grp obj* hom* id-coh* comp-coh* α = ! po-cst-inv-l (hom* α) ∙ ap po-cst' (𝔹-hom-comp (λ _ → P) (λ _ → is-grp) obj* (λ α → po-cst (hom* α)) (λ n → po-cst₂ (id-coh* n)) (λ α β → po-≡-r (po-cst₂ (comp-coh* α β)) (po-cst-∙ {p = hom α} {p' = hom β} (hom* α) (hom* β))) α) ∙ po-cst-inv-l (hom* α)

  --- TODO: adding this as rewriting rule makes typechecking loop
  -- {-# REWRITE 𝔹-hom-comp-nd #-}

--
--  Encode/Decode
--

-- right action of equivalences
≃-act-r : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (r : B ≃ C) → (A ≃ B) ≃ (A ≃ C)
≃-act-r r = qinv
  (λ e → ≃-trans e r)
  (λ e → ≃-trans e (≃-sym r))
  (λ e → ≃-assoc e r (≃-sym r) ∙ ap (≃-trans e) (≃-inv-r r) ∙ ≃-unit-r e)
  (λ e → ≃-assoc e (≃-sym r) r ∙ ap (≃-trans e) (≃-inv-l r) ∙ ≃-unit-r e)

≃-act-r-refl : ∀ {i j} {A : Type i} {B : Type j} → ≃-act-r {A = A} {B = B} ≃-refl ≡ ≃-refl
≃-act-r-refl = ≃-≡ (funext ≃-unit-r)

≃-act-r-trans : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l} (r : B ≃ C) (s : C ≃ D) → ≃-act-r {A = A} (≃-trans r s) ≡ ≃-trans (≃-act-r r) (≃-act-r s)
≃-act-r-trans r s = ≃-≡ (funext λ e → ! ≃-assoc e r s)

Fin-hom : (m n : ℕ) → hSet
Fin-hom m n = Fin m ≃ Fin n , ≃-is-set (Fin-is-set m) (Fin-is-set n)

Fin-hom≃ : (m : ℕ) {n o : ℕ} (e : Fin n ≃ Fin o) → Fin-hom m n ≡ Fin-hom m o
Fin-hom≃ m e = hSet≡ (ua (≃-act-r e))

Fin-hom≃-refl : (m n : ℕ) → Fin-hom≃ m {n = n} ≃-refl ≡ refl
Fin-hom≃-refl m n = hSet≡-≡ (ap ua ≃-act-r-refl ∙ ua-refl (Fin m ≃ Fin n)) ∙ hSet≡-refl

Fin-hom≃-comp : (m : ℕ) {n o p : ℕ} (α : Fin n ≃ Fin o) (β : Fin o ≃ Fin p) → Fin-hom≃ m (≃-trans α β) ≡ Fin-hom≃ m α ∙ Fin-hom≃ m β
Fin-hom≃-comp m α β = hSet≡-≡ (ap ua (≃-act-r-trans α β) ∙ ua-trans (≃-act-r α) (≃-act-r β)) ∙ hSet≡-∙ (ua (≃-act-r α)) (ua (≃-act-r β))

-- encoding of a path obj m ≡ b as an isomorphism of Fin m ≃ Fin n
Code : ℕ → 𝔹 → hSet
Code m = 𝔹-rec
  hSet
  hSet-is-groupoid
  (λ n → Fin-hom m n) -- the group of endomorphisms of Fin n
  (Fin-hom≃ m)      -- equiv by composition (group acts on itself)
  (Fin-hom≃-refl m) -- this action preserves identity
  (Fin-hom≃-comp m) -- compatible with composition

-- encode a path
encode : {n : ℕ} {b : 𝔹} → obj n ≡ b → fst (Code n b)
encode {n} p = transport (fst ∘ (Code n)) p ≃-refl

transport-Code : (n : ℕ) {n' n'' : ℕ} (α : Fin n' ≃ Fin n'') (e : Fin n ≃ Fin n') → transport (λ b → fst (Code n b)) (hom α) e ≡ ≃-trans e α
transport-Code n α e = begin
  transport (fst ∘ (Code n)) (hom α) e ≡⟨ transport-ap fst (Code n) (hom α) e ⟩
  transport fst (ap (Code n) (hom α)) e ≡⟨ 𝔹-hom-comp-nd _ _ _ _ _ _ _ |in-ctx (λ p → transport fst p e) ⟩
  transport fst (Fin-hom≃ n α) e ≡⟨⟩
  transport fst (hSet≡ (ua (≃-act-r α))) e ≡⟨ happly (transport-fst-hSet≡ (ua (≃-act-r α))) e ⟩
  coe (ua (≃-act-r α)) e ≡⟨ happly (coe-ua (≃-act-r α)) e ⟩
  ≃→ (≃-act-r α) e ≡⟨⟩
  ≃-trans e α ∎
  where
  transport-fst-hSet≡ : {A B : hSet} (p : fst A ≡ fst B) → transport {A = hSet} {x = A} {y = B} fst (hSet≡ p) ≡ coe p 
  transport-fst-hSet≡ {A , SA} {A , SA'} refl = begin
    transport fst (hSet≡ refl) ≡⟨ funext (transport-ap id fst (hSet≡ refl)) ⟩
    coe (ap fst (hSet≡ refl)) ≡⟨ ap coe (Σ-ext-fst refl (is-set-is-prop A SA SA')) ⟩
    coe refl ∎

decode : (n : ℕ) (b : 𝔹) → fst (Code n b) → obj n ≡ b
decode n = 𝔹-ind
  (λ b → fst (Code n b) → obj n ≡ b)
  (λ b → is-set-is-groupoid (Π-is-set λ e → 𝔹-is-groupoid (obj n) b))
  obj*
  hom*
  refl*
  comp*
  where
  obj* : (n' : ℕ) → Fin n ≃ Fin n' → obj n ≡ obj n'
  obj* n' e = hom e
  hom* : {m' n' : ℕ} (α : Fin m' ≃ Fin n') → obj* m' ≡ obj* n' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ hom α ]
  hom* {n'} {n''} α =
    po-of-t (funext λ e → begin
    transport (λ b → fst (Code n b) → obj n ≡ b) (hom α) (obj* n') e ≡⟨ happly (transport-→ (λ b → fst (Code n b)) (λ b → obj n ≡ b) (hom α) (obj* n n')) e ⟩
    transport (λ b → obj n ≡ b) (hom α) (obj* n' (transport (λ b → fst (Code n b)) (! hom α) e)) ≡⟨ transport-≡-r (obj n) (hom α) _ ⟩
    obj* n' (transport (λ b → fst (Code n b)) (! hom α) e) ∙ hom α ≡⟨⟩
    hom (transport (λ b → fst (Code n b)) (! hom α) e) ∙ hom α ≡⟨ ! inv-coh α |in-ctx (λ p → hom (transport (λ b → fst (Code n b)) p e) ∙ hom α) ⟩
    hom (transport (λ b → fst (Code n b)) (hom (≃-sym α)) e) ∙ hom α ≡⟨ transport-Code n (≃-sym α) e |in-ctx (λ β → hom β ∙ hom α) ⟩
    hom (≃-trans e (≃-sym α)) ∙ hom α ≡⟨ comp-coh e (≃-sym α) |in-ctx (λ p → p ∙ hom α) ⟩
    (hom e ∙ hom (≃-sym α)) ∙ hom α ≡⟨ inv-coh α |in-ctx (λ p → (hom e ∙ p) ∙ hom α) ⟩
    (hom e ∙ ! hom α) ∙ hom α ≡⟨ ∙-assoc (hom e) (! hom α) (hom α) ⟩
    hom e ∙ (! hom α ∙ hom α) ≡⟨ ∙-inv-l (hom α) |in-ctx (λ p → hom e ∙ p) ⟩
    hom e ∙ refl ≡⟨ ∙-unit-r (hom e) ⟩
    hom e ≡⟨⟩
    obj* n'' e ∎)
  refl* : (n' : ℕ) → hom* ≃-refl ≡ refl [ (λ p → obj* n' ≡ obj* n' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ p ]) ↓ id-coh n' ]
  refl* n' = po-in-prop _ (λ p → po-is-prop _ (λ b → →-is-set (𝔹-is-groupoid (obj n) b)) p (obj* n') (obj* n')) (id-coh n') (hom* ≃-refl) refl
  comp* : {n' : ℕ} {n'' : ℕ} {n''' : ℕ} (α : Fin n' ≃ Fin n'') (β : Fin n'' ≃ Fin n''') → hom* (≃-trans α β) ≡ po-trans (hom* α) (hom* β) [ (λ p → obj* n' ≡ obj* n''' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ p ]) ↓ comp-coh α β ]
  comp* {n'} {n''} {n'''} α β = po-in-prop _ (λ p → po-is-prop _ (λ b → →-is-set (𝔹-is-groupoid (obj n) b)) p (obj* n') (obj* n''')) (comp-coh α β) (hom* (≃-trans α β)) (po-trans (hom* α) (hom* β))

decode-encode : {n : ℕ} {b : 𝔹} (p : obj n ≡ b) → decode n b (encode p) ≡ p
decode-encode {n} refl = id-coh n

--- encoding homs
encode-decode' : {m n : ℕ} (α : Fin m ≃ Fin n) → encode (hom α) ≡ α
encode-decode' {m} {n} α = begin
  encode (hom α) ≡⟨⟩
  transport (fst ∘ (Code m)) (hom α) ≃-refl ≡⟨ transport-Code m α ≃-refl ⟩
  ≃-trans ≃-refl α ≡⟨ ≃-unit-l α ⟩
  α ∎

--- we have an equivalence on homs, otherwise said the encoding function is univalent
equiv-hom : {m n : ℕ} → (obj m ≡ obj n) ≃ (Fin m ≃ Fin n)
equiv-hom {m} {n} = qinv (encode {m} {obj n}) hom decode-encode encode-decode'

--- we can for instance deduce that obj is 0-injective
obj-is-0-injective : ∀ {m n : ℕ} → obj m ≡ obj n → m ≡ n
obj-is-0-injective p = Fin-inj (ua (≃→ equiv-hom p))

ℕ-to-FinType : ℕ → FinType
ℕ-to-FinType n = Fin n , n , ∣ ≃-refl ∣

𝔹-to-FinType : 𝔹 → FinType
𝔹-to-FinType = 𝔹-rec
  FinType
  FinType-is-groupoid
  ℕ-to-FinType
  (λ α → FinType≡ (ua α))
  (λ n → ap FinType≡ (ua-refl (Fin n)) ∙ ≃η (FinType≡≃ (ℕ-to-FinType n) (ℕ-to-FinType n)) refl)
  (λ α β → ap FinType≡ (ua-trans α β) ∙ FinType≡-∙ (ua α) (ua β))

𝔹-to-FinType-ap' : {m n : ℕ} (α : Fin m ≃ Fin n) → ap 𝔹-to-FinType (hom α) ≡ FinType≡ (ua α)
𝔹-to-FinType-ap' α = 𝔹-hom-comp-nd _ _ _ _ _ _ α

𝔹-to-FinType-ap : {m n : ℕ} (p : obj m ≡ obj n) → ap 𝔹-to-FinType p ≡ FinType≡ (ua (encode p))
𝔹-to-FinType-ap p = begin
  ap 𝔹-to-FinType p ≡⟨ ! decode-encode p |in-ctx ap 𝔹-to-FinType ⟩
  ap 𝔹-to-FinType (hom (encode p)) ≡⟨ 𝔹-to-FinType-ap' (encode p) ⟩
  FinType≡ (ua (encode p)) ∎

𝔹-to-FinType-ap-is-equiv : {m n : ℕ} → is-equiv (ap 𝔹-to-FinType {x = obj m} {y = obj n})
𝔹-to-FinType-ap-is-equiv {m} {n} = transport is-equiv (! funext 𝔹-to-FinType-ap) (∘-is-equiv {f = ua ∘ encode} {g = FinType≡} ue-eq (snd (≃-sym (FinType≡≃ _ _))))
  where
  postulate
    -- TODO: this is typing but thypechecking loops
    ue-eq : is-equiv (ua ∘ (encode {n = m} {b = obj n}))
    -- ue-eq = ∘-is-equiv (snd equiv-hom) ua-is-equiv

𝔹-to-FinType-is-injective : (b₀ b₁ : 𝔹) → is-equiv (ap 𝔹-to-FinType {x = b₀} {y = b₁})
𝔹-to-FinType-is-injective = 𝔹-ind
  (λ b₀ → (b₁ : 𝔹) → is-equiv (ap 𝔹-to-FinType {x = b₀} {y = b₁}))
  (λ b₀ → Π-is-groupoid λ b₁ → is-prop-is-groupoid (is-equiv-is-prop _)) -- easy level calc
  (λ m → 𝔹-ind
    (λ b₁ → is-equiv (ap 𝔹-to-FinType {x = obj m} {y = b₁}))
    (λ b₁ → is-prop-is-groupoid (is-equiv-is-prop _)) -- easy level calc
    (λ n → 𝔹-to-FinType-ap-is-equiv) -- the main theorem
    (λ α → {!po-in-prop (λ _ → is-equiv (ap 𝔹-to-FinType)) (λ _ → is-equiv-is-prop (ap 𝔹-to-FinType)) (hom α) 𝔹-to-FinType-ap-is-equiv 𝔹-to-FinType-ap-is-equiv!})  -- because is-equiv is a prop [should work but loops...]
    (λ n → {!po-in-prop (λ p → 𝔹-to-FinType-ap-is-equiv ≡ 𝔹-to-FinType-ap-is-equiv [ (λ _ → is-equiv (ap 𝔹-to-FinType)) ↓ p ]) (λ p → po-is-prop (λ _ → is-equiv (ap 𝔹-to-FinType)) (λ _ → is-prop-is-set (is-equiv-is-prop (ap 𝔹-to-FinType))) p 𝔹-to-FinType-ap-is-equiv 𝔹-to-FinType-ap-is-equiv) (id-coh n) _ _!}) -- because "path-over" in a prop is a prop [works but slows down everything]
    (λ α β → {!po-in-prop (λ p → 𝔹-to-FinType-ap-is-equiv ≡ 𝔹-to-FinType-ap-is-equiv [ (λ _ → is-equiv (ap 𝔹-to-FinType)) ↓ p ]) (λ p → po-is-prop ? p ? ?) (comp-coh α β) _ _!})) -- path-over in a prop
  (λ α → po-in-prop (λ _ → (_ : 𝔹) → is-equiv (ap 𝔹-to-FinType)) (λ _ → Π-is-prop λ _ → is-equiv-is-prop (ap 𝔹-to-FinType)) (hom α) _ _) -- path-over in a prop
  (λ n → po-in-prop _ (λ p → po-is-prop _ (λ _ → is-prop-is-set (Π-is-prop λ _ → is-equiv-is-prop (ap 𝔹-to-FinType))) p _ _) (id-coh n) _ _) -- path-over in a prop
  (λ α β → po-in-prop _ (λ p → po-is-prop _ (λ _ → Π-is-set λ _ → is-prop-is-set (is-equiv-is-prop (ap 𝔹-to-FinType))) p _ _) (comp-coh α β) _ _) -- path-over in a prop

𝔹-to-FinType-is-surjective : is-surjective 𝔹-to-FinType
𝔹-to-FinType-is-surjective (A , n , F) = ∥∥-rec ∥∥-is-prop (λ e → ∣ obj n , FinType≡ (! ua e) ∣) F

𝔹≃FinType : 𝔹 ≃ FinType
𝔹≃FinType = bij 𝔹-to-FinType 𝔹-to-FinType-is-injective 𝔹-to-FinType-is-surjective

𝔹-to-Fin : 𝔹 → Type₀
𝔹-to-Fin = fst ∘ 𝔹-to-FinType

--- The free symmetric monoid (small definition)
Exp : Type₀ → Type₀
Exp A = Σ 𝔹 (λ b → 𝔹-to-Fin b → A)
