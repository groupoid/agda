{-# OPTIONS --cubical #-}

module Infinity.Cohesion.Bundle where
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

-- best introduction to modern constructive algebraic topology
-- (с) @felixwellen http://www.math.kit.edu/iag3/~wellen/media/diss.pdf
-- single page by @5HT

-- TOC: Prelude
--      Path types
--      Abstract homogeneous structure
--      Shape (fundamental infinity Groupoid)
--      Surjections
--      Pullback
--      Image
--      Étale Maps
--      Automorphism
--      Manifold
--      G-sets (Covering Spaces)
--      Fiber Bundle (4 definitions)

-- $ brew install agda
-- $ agda bundle.agda
-- Checking bundle (bundle.agda).
-- Finished bundle.

-- Prelude

U : (i : Level) → Set (lsuc i)
U i = Set i
U₀ = U lzero
U₁ = U (lsuc lzero)
𝒰₀ = U₀
𝒰₁ = U₁
𝒰 = U
Type = 𝒰

data 𝟙 : 𝒰₀ where
     ∗ : 𝟙

infixl 4 _≃_
infixl 60 _$≃_
infix 5 _≈_
infix 60 _×_
infix 20 _,_
infix 20 _⇒_
infix 30 _∘_
infix 60 _⁻¹ -- \^-\^1

record ∑ {i j} {A : 𝒰 i} (P : A → 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor _,_
  field
    a : A
    p : P a

Σ : ∀ {i j} → (A : Type i) (P : A → Type j) → Type _
Σ _ P = ∑ P

∑π₁ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j}  → ∑ P → A
∑π₁ (a , _) = a

∑π₁-from_ : ∀ {i} {j} {A : 𝒰 i} (P : A → 𝒰 j) → ∑ P → A
∑π₁-from P = ∑π₁

_×_ : ∀ {i j} → (A : 𝒰 i) → (B : 𝒰 j) → 𝒰 (i ⊔ j)
A × B = ∑ (λ (a : A) → B)

π₁ : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} → A × B → A
π₁ (a , b) = a

π₂ : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} → A × B → B
π₂ (a , b) = b

id : ∀ {i} {A : 𝒰 i} → A → A
id a = a

identity-on : (A : 𝒰₀) → A → A
identity-on A = (λ (x : A) → x)

Π : ∀ {i j} → {A : 𝒰 i} → (P : A → 𝒰 j) → 𝒰 (i ⊔ j)
Π {_} {_} {A} P = (a : A) → P a

_∘_ : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

-- Path types

data _≈_ {i} {A : U i} (a : A) : A → U i where
    refl : a ≈ a

_∼_ : ∀ {i j} {A : U i} {B : U j} → (f g : A → B) → U (i ⊔ j)
_∼_ {_} {_} {A} {_} f g = (a : A) → f a ≈ g a

_⇒_ : ∀ {i j} {A : U i} {B : U j} → (f g : A → B) → U (i ⊔ j)
f ⇒ g = f ∼ g

_⁻¹ : ∀ {i} {A : U i} {x y : A} → x ≈ y → y ≈ x
refl ⁻¹ = refl

transport : ∀ {i j} {A : U i}  {x y : A} → (P : A → U j) → (γ : x ≈ y) → (P x → P y)
transport P refl = id

record _is-an-equivalence {i j} {A : U i} {B : U j} (f : A → B) : U (i ⊔ j) where
    constructor has-left-inverse_by_and-right-inverse_by_
    field
      left-inverse : B → A
      unit : left-inverse ∘ f ⇒ id
      right-inverse : B → A
      counit : id ⇒ f ∘ right-inverse

record _≃_  {i j} (A : U i) (B : U j) : U (i ⊔ j) where
    constructor _is-an-equivalence-because_
    field
      the-equivalence : A → B
      proof-of-invertibility : the-equivalence is-an-equivalence

_left-inverse-of_ : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (g : B → A) → U j
f left-inverse-of g =  (f ∘ g) ∼ id

_right-inverse-of_ : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (g : B → A) → U i
f right-inverse-of g = id ∼ (g ∘ f)

_is-quasiinverse-of_ : ∀ {i j} {A : U i} {B : U j} → (g : B → A) → (f : A → B) → U (i ⊔ j)
g is-quasiinverse-of f = (g left-inverse-of f) × (g right-inverse-of f)

_$≃_ : ∀ {i} {j} {A : U i} {B : 𝒰 j} → (f : A ≃ B) → A → B
(f is-an-equivalence-because _) $≃ a = f a

data #∥_∥ {i} (A : U i) : U i where
     #∣_∣ : A → #∥ A ∥

record fiber-of {i j} {X : U i} {Y : U j} (f : X → Y) (y₀ : Y) : U (i ⊔ j) where
    constructor _is-in-the-fiber-by_
    field
      x : X
      γ : f(x) ≈ y₀

fiber-of_at_ : ∀ {i} {j} {X : U i} {Y : U j} → (f : X → Y) → (y₀ : Y) → U (i ⊔ j)
fiber-of f at y₀ = fiber-of f y₀

∥_∥ : ∀ {i} (A : U i) → U i
∥ A ∥ = #∥ A ∥

-- Abstract homogeneous structure

record homogeneous-structure-on_ (A : 𝒰₀) : 𝒰₀ where
    field
      e : A
      ψ : (x : A) → (A ≃ A)
      is-translation-to : (x : A) → ((ψ x) $≃ e) ≈ x

const : {X Y : 𝒰₀} → Y → (X → Y)
const y₀ = λ _ → y₀

mutual
  _is-discrete : ∀ (A : 𝒰₀) → 𝒰₀
  A is-discrete = const {𝔸} {A} is-an-equivalence

  postulate
    𝔸 : 𝒰₀
    𝔸′ : homogeneous-structure-on 𝔸
    𝔸-nullfies-discrete-types : ∀ (A : 𝒰₀) → A is-discrete ≃ const {𝔸} {A} is-an-equivalence

origin-of-𝔸 : 𝔸
origin-of-𝔸 =
    let
      open homogeneous-structure-on_ 𝔸′
    in e

-- Shape (fundamental infinity Groupoid)

private
    data #ʃ (A : 𝒰₀) : 𝒰₀ where
      #σ : A → #ʃ A
      #κ  : (𝔸 → #ʃ A) → #ʃ A
      #κ′ : (𝔸 → #ʃ A) → #ʃ A

-- Surjections

_is-surjective : ∀ {i} {j} {A : U i} {B : U j} → (A → B) → U (i ⊔ j)
_is-surjective {_} {_} {A} {B} f = (b : B) → ∥ fiber-of f at b ∥

_is-a-proposition : ∀ {i} (A : U i) → U i
A is-a-proposition = (x y : A) → x ≈ y

_is-injective′ : ∀ {i} {A B : U i} → (f : A → B) → U i
f is-injective′ = (x y : _) → f x ≈ f y → x ≈ y

_is-injective : ∀ {i} {j} {A : U i} {B : U j} → (f : A → B) → U (i ⊔ j)
f is-injective = Π (λ b → (fiber-of f at b) is-a-proposition)

record _↠_ {i} {j} (A : U i) (B : U j) : U (i ⊔ j) where
    constructor _is-surjective-by_
    field
      morphism : A → B
      proof-that-it-is-surjective : morphism is-surjective

underlying-map-of-the-surjection : ∀ {i} {j} {A : U i} {B : U j} → (f : A ↠ B) → (A → B)
underlying-map-of-the-surjection (morphism is-surjective-by proof-that-it-is-surjective) = morphism

_$↠_ : ∀ {A B : 𝒰₀} → (f : A ↠ B) → A → B
f $↠ a = (underlying-map-of-the-surjection f) a

-- Pullback

record pullback {i} {A B C : U i} (f : A → C) (g : B → C) : U i where
    constructor _and_are-in-the-same-fiber-by_
    field
      a : A
      b : B
      γ : f(a) ≈ g(b)

p₁ : ∀ {A B C : 𝒰₀} {f : A → C} {g : B → C} → pullback f g → A
p₁ (a and b are-in-the-same-fiber-by γ) = a

p₂ : ∀ {A B C : 𝒰₀} {f : A → C} {g : B → C} → pullback f g → B
p₂ (a and b are-in-the-same-fiber-by γ) = b

p-homotopy : ∀ {A B C : 𝒰₀} {f : A → C} {g : B → C} → (x : pullback f g) → f(p₁ x) ≈ g(p₂ x)
p-homotopy (a and b are-in-the-same-fiber-by γ) = γ

p₁-of-pullback : ∀ {A B C : 𝒰₀} (f : A → C) (g : B → C) → pullback f g → A
p₁-of-pullback f g = p₁ {_} {_} {_} {f} {g}

p₂-of-pullback : ∀ {A B C : 𝒰₀} (f : A → C) (g : B → C) → pullback f g → B
p₂-of-pullback f g = p₂ {_} {_} {_} {f} {g}

induced-map-to-pullback :
    ∀ {i} {Z A B C : U i} {f : A → C} {g : B → C}
    → (z₁ : Z → A) → (z₂ : Z → B) → (γ : f ∘ z₁ ⇒ g ∘ z₂)
    → (Z → pullback f g)
induced-map-to-pullback z₁ z₂ γ z =
    (z₁ z) and (z₂ z) are-in-the-same-fiber-by γ z

record pullback-square {i} {Z A B C : U i} (f : A → C)  (g : B → C)
                                      (z₁ : Z → A) (z₂ : Z → B)  : U i where
    constructor the-square-commuting-by_and-inducing-an-equivalence-by_
    field
      γ : f ∘ z₁ ⇒ g ∘ z₂
      proof : (induced-map-to-pullback {f = f} {g = g}  z₁ z₂ γ) is-an-equivalence

record is-a-pullback-square {i} {Z A B C : U i}
    (f : A → C)  (g : B → C)
    (z₁ : Z → A) (z₂ : Z → B) (γ : f ∘ z₁ ⇒ g ∘ z₂) : U i where
    constructor the-induced-map-is-an-equivalence-by_
    field
      proof : (induced-map-to-pullback {_} {_} {_} {_} {_} {f} {g}  z₁ z₂ γ) is-an-equivalence

the-square-with-right_bottom_top_left_commuting-by_is-a-pullback-square :
    ∀ {Z A B C : 𝒰₀} (f : A → C)  (g : B → C) (z₁ : Z → A) (z₂ : Z → B) → (γ : f ∘ z₁ ⇒ g ∘ z₂) → 𝒰₀
the-square-with-right f bottom g top z₁ left z₂ commuting-by γ is-a-pullback-square =
    is-a-pullback-square f g z₁ z₂ γ

-- Image

the-image-of_contains : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (B → U (i ⊔ j))
the-image-of f contains b = ∥ ∑ (λ a → f(a) ≈ b) ∥

image : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → U (i ⊔ j)
image f = ∑ (λ b → the-image-of f contains b)

-- upper-left-vertex-of : ∀ {Z A B C : 𝒰₀} {f : A → C}  {g : B → C} {z₁ : Z → A} {z₂ : Z → B}
--                       → pullback-square f g z₁ z₂ → 𝒰₀
-- upper-left-vertex-of {Z} {_} {_} {_} {_} {_} {_} {_} _ = Z

-- _*_ : ∀ {E B B′ : 𝒰₀} → (f : B′ → B) → (φ : E → B) → 𝒰₀
-- f * φ = upper-left-vertex-of (complete-to-pullback-square φ f)

-- Etale Maps

  -- X --→ ℑ X
  -- |      |
  -- f      ℑf
  -- ↓      ↓
  -- Y --→ ℑ Y


postulate
    ℑ : ∀ {i} → 𝒰 i → 𝒰 i
    ℑ-unit : ∀ {i} {A : 𝒰 i} → A → ℑ A

_is-coreduced : ∀ {i} → 𝒰 i → 𝒰 i
A is-coreduced = ℑ-unit {_} {A} is-an-equivalence

ℑ-unit-at : ∀ {i} → (A : 𝒰 i) → (A → ℑ A)
ℑ-unit-at A = ℑ-unit {_} {A}

postulate
    ℑ-is-coreduced :
      ∀ {i}
      → (A : 𝒰 i)
      → (ℑ A) is-coreduced
    ℑ-induction :
      ∀ {i} {A : 𝒰₀} {B : ℑ A → 𝒰 i}
      → (∀ (a : ℑ A) → B(a) is-coreduced)
      → ((a : A) → B(ℑ-unit a))
      → ((a : ℑ A) → B(a))
    ℑ-compute-induction :
      ∀ {A : 𝒰₀} {B : ℑ A → 𝒰₀}
      → (coreducedness : ∀ (a : ℑ A) → B(a) is-coreduced)
      → (f : (a : A) → B(ℑ-unit a))
      → (a : A) → (ℑ-induction coreducedness f) (ℑ-unit a) ≈ f a

ℑ-recursion : ∀ {i} {A : 𝒰₀} {B : 𝒰 i} → B is-coreduced → (f : A → B) → (ℑ A → B)
ℑ-recursion coreducedness f = ℑ-induction (λ a → coreducedness) (λ a → f a)

ℑ-compute-recursion : ∀ {A B : 𝒰₀} → (coreducedness : B is-coreduced)
     → (f : A → B) → (a : A) → (ℑ-recursion coreducedness f) (ℑ-unit a) ≈ f a
ℑ-compute-recursion coreducedness f = ℑ-compute-induction (λ a → coreducedness) f

apply-ℑ-to-map : ∀ {A B : 𝒰₀} → (A → B) → (ℑ A → ℑ B)
apply-ℑ-to-map {_} {B} f = ℑ-recursion (ℑ-is-coreduced B) (ℑ-unit-at B ∘ f)

apply-ℑ : ∀ {A B : 𝒰₀} → (A → B) → (ℑ A → ℑ B)
apply-ℑ f = apply-ℑ-to-map f

ℑ→ = apply-ℑ

naturality-of-ℑ-unit : ∀ {A B : 𝒰₀} → (f : A → B) → (a : A) → (ℑ→ f(ℑ-unit-at A a) ≈ ℑ-unit-at B (f a))
naturality-of-ℑ-unit {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (f z))

im₁ = image

the-induced-map-from-the-image-of_to-the-codomain : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (image f → B)
the-induced-map-from-the-image-of f to-the-codomain (b , x) = b

ι-im₁ = the-induced-map-from-the-image-of_to-the-codomain

-- the-square-with-right_bottom_top_left_commuting-by_is-a-pullback-square :
--    ∀ {Z A B C : 𝒰₀} (f : A → C)  (g : B → C) (z₁ : Z → A) (z₂ : Z → B) → (γ : f ∘ z₁ ⇒ g ∘ z₂) → 𝒰₀
-- the-square-with-right f bottom g top z₁ left z₂ commuting-by γ is-a-pullback-square =
--    is-a-pullback-square f g z₁ z₂ γ

_is-an-étale-map : ∀ {X Y : 𝒰₀} (f : X → Y) → 𝒰₀
f is-an-étale-map =
    the-square-with-right (apply-ℑ-to-map f) -- f
      bottom ℑ-unit -- g
      top ℑ-unit -- z1
      left f -- z2
      commuting-by (naturality-of-ℑ-unit f) -- gamma
     is-a-pullback-square

_─ét→_ : (A B : 𝒰₀) → 𝒰₀
A ─ét→ B = ∑ (λ (f : A → B) → f is-an-étale-map)

underlying-map-of : ∀ {A B : 𝒰₀} → (A ─ét→ B) → (A → B)
underlying-map-of (f , _) = f

_ét→ : ∀ {A B : 𝒰₀} → (A ─ét→ B) → (A → B)
f ét→ = underlying-map-of f

_$ét_ : ∀ {A B : 𝒰₀} → (A ─ét→ B) → A → B
f $ét x = (f ét→) x

-- Automorphism

BAut : (A : 𝒰₀) → U₁
BAut A = image {_} {_} {𝟙} {𝒰₀} (λ ∗ → A)

ι-BAut : (A : 𝒰₀) → BAut A → 𝒰₀
ι-BAut A = ι-im₁ (λ ∗ → A)

postulate
  univalence : ∀ {i} {A B : U i} → A ≃ B → A ≈ B
  fiber-of-a-∑ :
    ∀ {i} {j} {A : U i} {P : A → U j}
    → (a : A) → fiber-of ∑π₁-from P at a ≃ P a

the-proposition_is-equivalence-invariant-by-univalence_ : ∀ {i} (P : U i → U i) {A A′ : U i} → (A ≃ A′) → P A → P A′
the-proposition P is-equivalence-invariant-by-univalence e = transport _ (univalence e)

postulate
  -1-truncated : ∀ {i} {A : U i} → (a a′ : ∥ A ∥) → a ≈ a′
  switch-inverses : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} {f : A → B} {g : B → A}
                → f is-an-equivalence → g ∘ f ⇒ id → f ∘ g ⇒ id --  g∼gfh ○ gfh∼h -> g∼h -> fg∼fh ○ fh∼1

reverse-homotopy : ∀ {i j} {A : U i} {B : U j} {f g : A → B} → f ∼ g → g ∼ f
reverse-homotopy {_} {_} {A} {B} {f} {g} H = λ (a : A) → H a ⁻¹

∥-∥-is-truncation : ∀ {i} (A : U i) → ∥ A ∥ is-a-proposition
∥-∥-is-truncation A = λ a a′ → -1-truncated a a′

infix 80 _⁻¹≃
_⁻¹≃ : ∀ {i j} {A : 𝒰 i} {B : 𝒰 j} → A ≃ B → B ≃ A
(the-equivalence is-an-equivalence-because reason) ⁻¹≃ with reason
... | (has-left-inverse
          left-inverse by unit
         and-right-inverse
          right-inverse by counit)
      = left-inverse is-an-equivalence-because
                 (has-left-inverse
                   the-equivalence by switch-inverses reason unit
                     and-right-inverse
                     the-equivalence by reverse-homotopy unit)

ι-im₁-is-injective : ∀ {i} {j} {A : U i} {B : U j} (f : A → B) → ι-im₁ f is-injective
ι-im₁-is-injective f b = (the-proposition (λ (A : _) → A is-a-proposition)
                            is-equivalence-invariant-by-univalence (fiber-of-a-∑ b ⁻¹≃))
                             (∥-∥-is-truncation (∑ (λ a → f a ≈ b)))

ι-BAut-is-injective : ∀ {A : 𝒰₀} → (ι-BAut A) is-injective
ι-BAut-is-injective {A} = ι-im₁-is-injective (λ ∗₃ → A)

universal-family-over-BAut′_ : (F : 𝒰₀) → (BAut F → 𝒰₀)
(universal-family-over-BAut′ F) (F′ , p) = F′

universal-family-over-BAut_ : (F : 𝒰₀) → 𝒰₁
universal-family-over-BAut F = ∑ (universal-family-over-BAut′ F)

-- the 'unit', i.e. 'refl {e-BAut A}' is the unit of 'Aut A'

postulate
  e-BAut : (A : 𝒰₀) → BAut A
-- e-BAut A = (A , ∣ (∗ , refl) ∣ )

-- Manifold

_is-infinitesimally-close-to_ : {X : 𝒰₀} → (x x′ : X) → 𝒰₀
x is-infinitesimally-close-to x′ = ℑ-unit x ≈ ℑ-unit x′

_is-close-to_ : {X : 𝒰₀} → (x x′ : X) → 𝒰₀
_is-close-to_ = _is-infinitesimally-close-to_

formal-disk-at_ : ∀ {X : 𝒰₀} → (x : X) → 𝒰₀
formal-disk-at x = ∑ (λ x′ → x is-close-to x′)

formal-disk-of : ∀ {V : 𝒰₀} → (structure-on-V : homogeneous-structure-on V) → 𝒰₀
formal-disk-of structure-on-V = formal-disk-at (homogeneous-structure-on_.e structure-on-V)

record _-manifold {V′ : 𝒰₀} (V : homogeneous-structure-on V′) : 𝒰₁ where
    field
      M : 𝒰₀
      W : 𝒰₀
      w : W ─ét→ M
      w-covers : (w ét→) is-surjective
      v : W ─ét→ V′

-- G-sets (Covering Spaces)

record groups-over-structure-group-of_ {V : 𝒰₀}
    (structure-on-V : homogeneous-structure-on V) : 𝒰₁ where
    field
      BG : 𝒰₀
      Be : BG
      Bφ : BG → BAut (formal-disk-of structure-on-V)
      path-between-units : Bφ(Be) ≈ e-BAut (formal-disk-of structure-on-V)

module G-structures-on-V-manifolds
    {V′ : 𝒰₀} -- (w : U ─ét→ M) (v : U ─ét→ V′)
    (V : homogeneous-structure-on V′)
    (reduction : groups-over-structure-group-of V)
    (M′ : V -manifold) where

    open homogeneous-structure-on_ V
    open _-manifold M′
    open groups-over-structure-group-of_ reduction

    𝔻ₑ = formal-disk-at e
    postulate
      χ : M → BAut 𝔻ₑ
--    χ = the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism V M′

    G-structures : U₁
    G-structures = ∑ (λ (φ : M → BG) → Bφ ∘ φ ⇒ χ)

-- Fiber Bundle

-- Definition (1)
record _is-a_-fiber-bundle {B : 𝒰₀} (φ : B → 𝒰₀) (F : 𝒰₀) : 𝒰₁ where
    field
      all-fibers-are-merely-equivalent : ∀ (b : B) → ∥ φ b ≃ F ∥

    canonical-cover′ : B → 𝒰₀
    canonical-cover′ b = φ b ≃ F

    canonical-cover : ∑ canonical-cover′ → B
    canonical-cover (F′ , _) = F′

equivalence-of_and_over_ : ∀ {i} {A′ : 𝒰₀} {A : 𝒰 i} (E′ : A′ → 𝒰₀) (E : A → 𝒰₀) (f : A′ → A) → 𝒰₀
equivalence-of E′ and E over f = (x : _) → E′(x) ≃ E(f x)

-- Definition (2)
record _is-a″_-fiber-bundle″ {B : 𝒰₀} (φ : B → 𝒰₀) (F : 𝒰₀) : 𝒰₁ where 
    field
      V : 𝒰₀
      v : V ↠ B
      pullback-trivializes : (x : V) → φ(v $↠ x) ≃ F

-- Definition (3)
record _is-a′_-fiber-bundle′ {E B : 𝒰₀} (p : E → B) (F : 𝒰₀) : 𝒰₁ where
    field
      χ : B → BAut F
      classyfies : equivalence-of (λ b → fiber-of p at b) and (universal-family-over-BAut′ F) over χ

pullback-square-with-right_bottom_top_left_ : ∀ {Z A B C : 𝒰₀} (f : A → C)  (g : B → C) (z₁ : Z → A) (z₂ : Z → B) → 𝒰₀
pullback-square-with-right f bottom g top z₁ left z₂ = pullback-square f g z₁ z₂

_is-a-product-with-projections_and_ : ∀ {A B : 𝒰₀} (Z : 𝒰₀) (z₁ : Z → A) (z₂ : Z → B) → 𝒰₀
Z is-a-product-with-projections z₁ and z₂ = pullback-square-with-right (λ a → ∗) bottom (λ b → ∗) top z₁ left z₂

-- Definition (4)
record _is-a‴_-fiber-bundle‴ {E B : 𝒰₀} (φ : E → B) (F : 𝒰₀) : 𝒰₁ where
    field
      V : 𝒰₀
      v : V ↠ B
      v′ : V × F → E
      □ : pullback-square-with-right φ
            bottom (underlying-map-of-the-surjection v)
            top v′
            left π₁

