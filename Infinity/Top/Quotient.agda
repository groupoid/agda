{-# OPTIONS --cubical #-}

module Phenomenology.Inf.Quotient where

-- open import Cubical.Core.Prelude
open import Phenomenology.Inf.Proto

Reflexive : ∀ {ℓ} {A : Set ℓ} → (A → A → Set ℓ) → Set _
Reflexive _∼_ = ∀ x → x ∼ x

module Quot {ℓ} (A : Set ℓ) (_∼_ : A → A → Set ℓ) (∼-refl : Reflexive _∼_) where
  data Q : Set ℓ where
    point : A → Q
    quot : {x y : A} → x ∼ y → point x ≡ point y
    trunc : {x y : Q} → (p q : x ≡ y) → p ≡ q

  module _ {ℓ} {P : Q → Set ℓ}
    (point* : ∀ x → P (point x))
    (quot* : ∀ {x y} eq → PathP (λ i → P (quot {x} {y} eq i)) (point* x) (point* y))
    (trunc* : ∀ {x y} {p q : x ≡ y} → ∀ {fx : P x} {fy : P y} (eq₁ : PathP (λ i → P (p i)) fx fy) (eq₂ : PathP (λ i → P (q i)) fx fy) → PathP (λ i → PathP (λ j → P (trunc p q i j)) fx fy) eq₁ eq₂)
    where
    Q-elim : ∀ x → P x
    Q-elim (point x) = point* x
    Q-elim (quot eq i) = quot* eq i
    Q-elim (trunc {x} {y} p q i j) = trunc* (cong Q-elim p) (cong Q-elim q) i j

Rel : ∀ {ℓ} → Set ℓ → Set _
Rel {ℓ} A = A → A → Set ℓ


rel-pair : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (_∼_ : Rel A) (_≈_ : Rel B) → Rel (A × B)
rel-pair _∼_ _≈_ = λ { (x , y) (x′ , y′) → x ∼ x′ × y ≈ y′ }

refl-pair : ∀ {ℓ₁ ℓ₂} {A B} (∼ ≈) →
   Reflexive {ℓ₁} {A} ∼ → Reflexive {ℓ₂} {B} ≈ → Reflexive (rel-pair ∼ ≈)
refl-pair _ _ ∼-refl ≈-refl = λ { (x , y) → (∼-refl x , ≈-refl y) }

module Quot² {ℓ₁ ℓ₂} {A₁ _∼_} (∼-refl : Reflexive {ℓ₁} {A₁} _∼_) {A₂ _≈_} (≈-refl : Reflexive {ℓ₂} {A₂} _≈_) where
  open Quot A₁ _∼_ ∼-refl renaming (Q to Q₁; Q-elim to Q₁-elim) hiding (quot; point; trunc)
  open Quot A₂ _≈_ ≈-refl renaming (Q to Q₂; Q-elim to Q₂-elim) hiding (quot; point; trunc)
  open Quot (A₁ × A₂) (rel-pair _∼_ _≈_) (refl-pair _∼_ _≈_ ∼-refl ≈-refl)
  open import Utils

  module _ where
    fromPair : Q₁ → Q₂ → Q
    fromPair = Q₁-elim
      (λ x → Q₂-elim
        (λ y → point (x , y))
        (λ {y} {y′} y≈y′ → quot (∼-refl x , y≈y′))
        trunc)
      (λ {x} {y} eq₁ i → Q₂-elim
        (λ a → quot (eq₁ , ≈-refl a) i)
        (λ {a} {b} eq₂ j → lemma eq₁ eq₂ i j)
        trunc)
      (λ {x} {y} {p} {q} {x,} {y,} eq₁ eq₂ i → funExt λ a → λ j → trunc {x, a} {y, a} (ap eq₁ a) (ap eq₂ a) i j)
      where
        lemma : ∀ {x y : A₁} {a b : A₂} → (x ∼ y) → (a ≈ b) → I → I → Q
        lemma {x} {y} {a} {b} eq₁ eq₂ i j = surface i j
          where
            X Y : Q₁
            X = Quot.point x
            Y = Quot.point y

            A B : Q₂
            A = Quot.point a
            B = Quot.point b

            XA = point (x , a)
            XB = point (x , b)
            YA = point (y , a)
            YB = point (y , b)

            p : X ≡ Y
            p = Quot.quot eq₁

            q : A ≡ B
            q = Quot.quot eq₂

            p₀ : XA ≡ YA
            p₀ = quot (eq₁ , ≈-refl _)

            p₁ : XB ≡ YB
            p₁ = quot (eq₁ , ≈-refl _)

            q₀ : XA ≡ XB
            q₀ = quot (∼-refl _ , eq₂)

            q₁ : YA ≡ YB
            q₁ = quot (∼-refl _ , eq₂)

            qᵢ : ∀ i → p₀ i ≡ p₁ i
            qᵢ = slidingLid p₀ p₁ q₀

            left : qᵢ i0 ≡ q₀
            left = refl

            right : qᵢ i1 ≡ q₁
            right = trunc (qᵢ i1) q₁

            surface : PathP (λ i → p₀ i ≡ p₁ i) q₀ q₁
            surface i = comp (λ j → p₀ i ≡ p₁ i)
              (λ { j (i = i0) → left j
                 ; j (i = i1) → right j
                 })
                (inc (qᵢ i))
