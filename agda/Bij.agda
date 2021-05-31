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
-- encode n .(obj n) refl = ≃-refl
encode {n} p = transport (fst ∘ (Code n)) p ≃-refl

--- NOTE: in this version we used Fin-inj for constructing the object which is a
--- very bad idea: it sends every automorphism to refl since Nat is a set (this
--- is not the right version of injectivity in HoTT). The right way consists in
--- using aut, generalized to different endpoints (and should be renamed to hom).

-- lem-aut : {m n : ℕ} (α : Fin m ≡ Fin n) → ap obj (Fin-inj α) ≡ aut α
-- lem-aut α with Fin-inj α
-- ... | refl = {!!}

-- decode : (n : ℕ) (b : 𝔹) → fst (Code n b) → obj n ≡ b
-- decode n = 𝔹-ind
  -- (λ b → fst (Code n b) → obj n ≡ b)
  -- (λ b → is-set-is-groupoid (Π-is-set λ e → 𝔹-is-groupoid (obj n) b))
  -- obj* -- Fin is injective
  -- path*
  -- {!!}
  -- (λ {n'} α β → {!!})
  -- where
  -- obj* : (n' : ℕ) → Fin n ≃ Fin n' → obj n ≡ obj n'
  -- obj* n' e = ap obj (Fin-inj (ua e))
  -- path* : {m' n' : ℕ} (α : Fin m' ≡ Fin n') → obj* m' ≡ obj* n' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ aut α ]
  -- path* {n'} {n''} α = po-of-t ({!!} ∙ ! transport-ap (λ b → fst (Code n b) → obj n ≡ b) obj (Fin-inj α) (obj* n') ∙ apd obj* (Fin-inj α))
  -- -- po-of-t (funext λ e → begin
    -- -- transport (λ b → fst (Code n b) → obj n ≡ b) (aut α) (obj* n') e ≡⟨ happly (transport-→ (λ b → fst (Code n b)) (λ b → obj n ≡ b) (aut α) (obj* n n')) e ⟩
    -- -- transport (λ b → obj n ≡ b) (aut α) (obj* n' (transport (λ b → fst (Code n b)) (! aut α) e)) ≡⟨ transport-≡-r (obj n) (aut α) _ ⟩
    -- -- obj* n' (transport (λ b → fst (Code n b)) (! aut α) e) ∙ aut α ≡⟨ {!!} ⟩
    -- -- {!!} ≡⟨ {!!} ⟩
    -- -- obj* n'' e ∎)
  -- -- po-of-t (begin
    -- -- transport (λ b → fst (Code n b) → obj n ≡ b) (aut α) (obj* n') ≡⟨ transport-→ (λ b → fst (Code n b)) (λ b → obj n ≡ b) (aut α) (obj* n') ⟩
    -- -- transport (λ b → obj n ≡ b) (aut α) ∘ obj* n' ∘ transport (λ b → fst (Code n b)) (! aut α) ≡⟨ {!!} ⟩
    -- -- obj* n'' ∎)
  -- -- apo (λ b e → {!!}) (aut α)
  -- -- apo obj* (Fin-inj α)
  -- -- = po-of-t (funext λ e → {!!})
    -- -- (begin
    -- -- transport (λ b → fst (Code n b) → obj n ≡ b) (aut α) (obj* n') ≡⟨ {!!} ⟩
    -- -- obj* n' ∎)
  -- -- refl* : (n' : ℕ) → path* refl ≡ refl [ (λ p → PathOver (λ b → fst (Code n b) → obj n ≡ b) p (λ e → ap obj (Fin-inj (ua e))) (λ e → ap obj (Fin-inj (ua e)))) ↓ id-coh n' ]
  -- -- refl* n' = {!!}

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
  -- po-of-t (begin
    -- transport (λ b → fst (Code n b) → obj n ≡ b) (hom α) (obj* n') ≡⟨ transport-→ (λ b → fst (Code n b)) (λ b → obj n ≡ b) (hom α) (obj* n') ⟩
    -- transport (λ b → obj n ≡ b) (hom α) ∘ obj* n' ∘ transport (λ b → fst (Code n b)) (! hom α) ≡⟨ ap2 _∘_ (funext (transport-≡-r (obj n) (hom α))) refl ⟩
    -- (λ q → q ∙ hom α) ∘ obj* n' ∘ transport (λ b → fst (Code n b)) (! hom α) ≡⟨ ap2 _∘_ (refl {x = λ q → q ∙ hom α}) (ap2 _∘_ refl (ap (transport (λ b → fst (Code n b))) (! inv-coh α))) ⟩
    -- (λ q → q ∙ hom α) ∘ obj* n' ∘ transport (λ b → fst (Code n b)) (hom (≃-sym α)) ≡⟨ {!!} ⟩
    -- obj* n'' ∎)
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
    -- po-of-t
    -- (funext-≡
      -- (transport (λ p → obj* n' ≡ obj* n' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ p ]) (id-coh n') (hom* ≃-refl))
      -- refl
      -- λ e → 𝔹-is-groupoid
        -- (obj n) (obj n')
        -- (obj* n' e) (obj* n' e)
        -- (happly (transport (λ p → obj* n' ≡ obj* n' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ p ]) (id-coh n') (hom* ≃-refl)) e)
        -- refl)
  comp* : {n' : ℕ} {n'' : ℕ} {n''' : ℕ} (α : Fin n' ≃ Fin n'') (β : Fin n'' ≃ Fin n''') → hom* (≃-trans α β) ≡ po-trans (hom* α) (hom* β) [ (λ p → obj* n' ≡ obj* n''' [ (λ b → fst (Code n b) → obj n ≡ b) ↓ p ]) ↓ comp-coh α β ]
  comp* {n'} {n''} {n'''} α β = po-in-prop _ (λ p → po-is-prop _ (λ b → →-is-set (𝔹-is-groupoid (obj n) b)) p (obj* n') (obj* n''')) (comp-coh α β) (hom* (≃-trans α β)) (po-trans (hom* α) (hom* β))
  -- po-of-t
    -- (≃→-inj (≃-sym (po-≃ (λ b → fst (Code n b) → obj n ≡ b) (hom α ∙ hom β) (obj* n') (obj* n''')))
      -- (funext-≡ t {!!} (λ e → 𝔹-is-groupoid (obj n) (obj n''') (transport (λ b → fst (Code n b) → obj n ≡ b) (trans (hom α) (hom β)) (obj* n') e) (hom e) {!!} {!!})))
    -- where
    -- t : transport (λ b → fst (Code n b) → obj n ≡ b) (hom α ∙ hom β) (obj* n') ≡ obj* n'''
    -- t = {!!}

decode-encode : {n : ℕ} {b : 𝔹} (p : obj n ≡ b) → decode n b (encode p) ≡ p
decode-encode {n} refl = id-coh n
  -- begin
  -- decode n (obj n) (encode n (obj n) refl) ≡⟨⟩
  -- -- decode n (obj n) (transport (λ b → fst (Code n b)) refl ≃-refl) ≡⟨⟩
  -- decode n (obj n) ≃-refl ≡⟨⟩
  -- hom ≃-refl ≡⟨ id-coh n ⟩
  -- refl ∎

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

-- -- TODO: this one would be very convenient but I think it does not hold because
-- -- we cannot chose the path in a continuous way...
-- obj-is-surjective : (b : 𝔹) → Σ ℕ (λ n → obj n ≡ b)
-- obj-is-surjective = 𝔹-ind
  -- (λ b → Σ ℕ (λ n → obj n ≡ b))
  -- (λ b → Σ-is-groupoid (is-set-is-groupoid ℕ-is-set) λ n → is-set-is-groupoid (𝔹-is-groupoid (obj n) b))
  -- (λ n → n , refl)
  -- -- (λ {m} {n} α →
    -- -- po-of-t (Σ-ext
    -- -- (ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ∙ transport-cst (hom α) m ∙ Fin-inj (ua α))
    -- -- -- (begin
    -- -- -- fst (transport (λ b → Σ ℕ (λ n → obj n ≡ b)) (hom α) (m , refl)) ≡⟨ ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ⟩
    -- -- -- -- fst (transport (λ _ → ℕ) (hom α) m , transport2 (λ b n → obj n ≡ b) (hom α) refl refl) ≡⟨⟩
    -- -- -- transport (λ _ → ℕ) (hom α) m ≡⟨ transport-cst (hom α) m ⟩
    -- -- -- m ≡⟨ Fin-inj (ua α) ⟩
    -- -- -- n ∎)
    -- -- (begin
      -- -- -- transport (λ n' → obj n' ≡ obj n) (ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ∙ transport-cst (hom α) m ∙ Fin-inj (ua α)) (snd (transport (λ b → Σ ℕ (λ n → obj n ≡ b)) (hom α) (m , refl))) ≡⟨ {!transport-ap!} ⟩
      -- -- -- transport (λ n' → n' ≡ obj n) (ap obj (ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ∙ transport-cst (hom α) m ∙ Fin-inj (ua α))) (snd (transport (λ b → Σ ℕ (λ n → obj n ≡ b)) (hom α) (m , refl))) ≡⟨ {!transport-≡-l!} ⟩
      -- -- -- ! (ap obj (ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ∙ transport-cst (hom α) m ∙ Fin-inj (ua α))) ∙ snd (transport (λ b → Σ ℕ (λ n → obj n ≡ b)) (hom α) (m , refl)) ≡⟨ {!!} ⟩
      -- -- -- ! (ap obj (ap fst (transport-Σ (λ _ → ℕ) (λ b n → obj n ≡ b) (hom α) (m , refl)) ∙ transport-cst (hom α) m ∙ Fin-inj (ua α))) ∙ snd (transport (λ b → Σ ℕ (λ n → obj n ≡ b)) (hom α) (m , refl)) ≡⟨ {!!} ⟩
      -- -- refl ∎)
    -- -- )
  -- -- )
  -- hom*
  -- (λ n → po-of-t (Σ-is-set ℕ-is-set (λ n → 𝔹-is-groupoid (obj n) _) (n , refl) (n , refl) _ refl))
  -- (λ {m} {n} {o} α β → po-of-t {!!})
    -- where
    -- hom* : {m n : ℕ} (α : Fin m ≃ Fin n) → (m , refl) ≡ (n , refl) [ (λ b → Σ ℕ (λ n → obj n ≡ b)) ↓ hom α ]
    -- -- hom* {m} {n} α with Fin-inj (ua α)
    -- -- ... | refl = {!!}
    -- hom*  {m} {n} α = {!!}

--- The following seems to be quite involved to prove directly. Fortunately, we
--- should have a simpler way to prove it based on the above lemmas.
-- --- we should have an equivalence between Fin and B but the direction below
-- --- seems to be quite tedious to prove...
-- encode-decode : (n : ℕ) (b : 𝔹) (e : fst (Code n b)) → encode n b (decode n b e) ≡ e
-- encode-decode n = 𝔹-ind
  -- (λ b → (e : fst (Code n b)) → encode n b (decode n b e) ≡ e)
  -- (λ b → Π-is-groupoid (λ e → {!!}))
  -- obj*
  -- hom*
  -- refl*
  -- {!!}
  -- where
  -- obj* : (n' : ℕ) (e : fst (Code n (obj n'))) → encode n (obj n') (decode n (obj n') e) ≡ e
  -- obj* n' e = transport-Code n e ≃-refl ∙ ≃-unit-l e
    -- -- begin
    -- -- encode n (obj n') (decode n (obj n') e) ≡⟨⟩
    -- -- encode n (obj n') (hom e) ≡⟨⟩
    -- -- transport (fst ∘ (Code n)) (hom e) ≃-refl ≡⟨ transport-Code n e ≃-refl ⟩
    -- -- ≃-trans ≃-refl e ≡⟨ ≃-unit-l e ⟩
    -- -- e ∎)
  -- hom* : {n' : ℕ} {n'' : ℕ} (α : Fin n' ≃ Fin n'') → obj* n' ≡ obj* n'' [ (λ b → (e : fst (Code n b)) → encode n b (decode n b e) ≡ e) ↓ hom α ]
  -- hom* {n'} {n''} α = po-of-t (funext λ e → begin
    -- -- transport (λ b → (e : fst (Code n b)) → encode n b (decode n b e) ≡ e) (hom α) (λ e → obj* n' e) e ≡⟨ happly (transport-Π (λ b → fst (Code n b)) (λ b e → encode n b (decode n b e) ≡ e) (hom α) (λ e → obj* n n' e)) e ⟩
    -- transport2 (λ b e → encode n b (decode n b e) ≡ e) (hom α) (transport-inv (λ b → fst (Code n b)) (hom α) e) (obj* n' (transport (λ b → fst (Code n b)) (! hom α) e)) ≡⟨⟩
    -- transport2 (λ b e → encode n b (decode n b e) ≡ e) (hom α) (transport-inv (λ b → fst (Code n b)) (hom α) e) (obj* n' (transport (λ b → fst (Code n b)) (! hom α) e)) ≡⟨ {!!} ⟩
    -- transport-Code n e ≃-refl ∙ ≃-unit-l e ∎)
  -- refl* : (n' : ℕ) → hom* ≃-refl ≡ refl [ (λ p → obj* n' ≡ obj* n' [ (λ b → (e : fst (Code n b)) → encode n b (decode n b e) ≡ e) ↓ p ]) ↓ id-coh n' ]
  -- refl* n' = po-of-t (funext-≡ {!!} refl (λ e → {!!}))

-- postulate

  -- decode-is-equiv : (n : ℕ) (b : 𝔹) → is-equiv (decode n b)


-- TODO: shouldn't we have an action of the path here? namely, an equality A ≡ A
-- does not seem to induce a loop in 𝔹, i.e. we loose the paths...
-- we should transport obj n along some hom induced by e...
-- FinType-to-𝔹 : FinType → 𝔹
-- FinType-to-𝔹 (A , n , e) = obj n

ℕ-to-FinType : ℕ → FinType
ℕ-to-FinType n = Fin n , n , ∣ ≃-refl ∣

-- TODO: injectif par encode-decode'
-- + montrer que c'est surjectif
𝔹-to-FinType : 𝔹 → FinType
-- 𝔹-to-FinType = 𝔹-rec FinType FinType-is-groupoid
  -- ℕ-to-FinType
  -- (λ {m} {n} α → ≃← (FinType≡ (ℕ-to-FinType m) (ℕ-to-FinType n)) α)
  -- (λ n → ≃η (FinType≡ (ℕ-to-FinType n) (ℕ-to-FinType n)) refl)
  -- (λ {n} α β → FinType≡-∙ α β)
𝔹-to-FinType = 𝔹-rec
  FinType
  FinType-is-groupoid
  ℕ-to-FinType
  -- (λ {m} {n} α → Σ-ext (ua (encode (hom α))) (is-finite-is-prop (Fin n) _ _))
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
