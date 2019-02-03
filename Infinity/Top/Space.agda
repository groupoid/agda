{-# OPTIONS --cubical --safe #-}

module Infinity.Top.Space where

open import Infinity.Proto
open import Infinity.Sigma
open import Infinity.Path
open import Infinity.NType
open import Infinity.Inductive.Either
open import Infinity.Inductive.Empty
open import Infinity.Inductive.One
open import Infinity.Inductive.Two
open import Infinity.Inductive.Fin

open import Infinity.Top.Predicate

record Space : Set₂ where
  constructor space
  field
    C            : Set
    Open         : Pred (Pred C)
    none         : Open (λ _ → ⇑ ⊥)
    all          : Open (λ _ → ⇑ ⊤)
    union        : {A : Set} (f : A → ∃ Open) → Union (π⃐ ∘ f) ∈ Open
    intersection : ∀ {n} (f : Fin n → ∃ Open) → Intersection (π⃐ ∘ f) ∈ Open

  Neighborhood : C → Pred (Pred C)
  Neighborhood x = λ V → ∃ (λ U → (Open U) × (U ⊆ V) × (x ∈ U))

  Closed : Pred (Pred C)
  Closed P = ∀ x → x ∉ P → ∃ (λ U → Neighborhood x U → Disjoint P U)

  Clopen : Pred (Pred C)
  Clopen P = Open P × Closed P


  none-Clopen : Clopen (λ _ → ⇑ ⊥)
  none-Clopen = none , (λ x x∉P → (λ _ → ⇑ ⊤) , (λ N a a∈Empty a∈All → ↓ a∈Empty))

  all-Clopen : Clopen (λ _ → ⇑ ⊤)
  all-Clopen = all , (λ x x∉P → (λ _ → ⇑ ⊥) , (λ N a a∈All a∈Empty → ↓ a∈Empty))

  Complement-closes : ∀ {U : Pred C} → Open U → Closed (Complement U)
  Complement-closes {U} U-open = λ x x∉U → U , (λ N a a∈CU a∈U → a∈CU a∈U)

open Space

preimage : ∀ {A B : Set} → (f : A → B) → Pred B → Pred A
preimage f B = λ a → B (f a)

Continuous : ∀ {{X Y : Space}} → (f : (C X) → (C Y)) → Set₁
Continuous {{X}} {{Y}} f = ∀ B → (Open Y) B → (Open X) (preimage f B)

Discrete : ∀ (A : Set) → Space
Discrete A = space A (λ _ → ⇑ ⊤) (↑ unit) (↑ unit) (λ {A₁} f → ↑ unit) λ {n} f → ↑ unit

stable : ∀ {ℓ} → Set ℓ → Set ℓ
stable A = ¬ ¬ A → A

dec : ∀ {ℓ} → Set ℓ → Set ℓ
dec A = A ⊎ (¬ A)

discrete : ∀ {ℓ} → Set ℓ → Set ℓ
discrete A = (x y : A) → dec (x ≡ y)

Discrete-Clopen : ∀ {A : Set} → ∀ S → Clopen (Discrete A) S
Discrete-Clopen S = ↑ unit , (λ x x∉S → Complement S , (λ N a a∈S a∈CS → a∈CS a∈S))

dec→stable : ∀ {ℓ} (A : Set ℓ) → dec A → stable A
dec→stable A (inl x) = λ _ → x
dec→stable A (inr x) = λ f → ⊥-elim (f x)

dNot : ∀ {l} → (A : Set l) → (a : A) → ¬ ¬ A
dNot A a p = p a

lem : ∀ {ℓ} {A : Set ℓ} {a b : A} (f : (x : A) → a ≡ x → a ≡ x) (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
lem {a = a} f p = J (λ y q → PathP (λ i → a ≡ q i) (f a refl) (f y q)) refl p

stable-path→isSet : ∀ {ℓ} {A : Set ℓ} → (st : ∀ (a b : A) → stable (a ≡ b)) → isSet A
stable-path→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (dNot _ p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (dNot _ p) (dNot _ q) i)
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → lem f p i k
                    ; (j = i1) → lem f q i k }) a

-- Hedberg's theorem
discrete→isSet : ∀ {ℓ} {A : Set ℓ} → discrete A → isSet A
discrete→isSet d = stable-path→isSet (λ x y → dec→stable (x ≡ y) (d x y))

