{-# OPTIONS --cubical --type-in-type #-}

module Infinity.Category.InfinityCategories where

module Size where
  open import Agda.Builtin.Size public
    renaming (SizeU to U)
    renaming (Size<_ to <_)
    renaming (_⊔ˢ_ to _⊔_)

open Size public
  hiding (∞)

module ≡ where
  open import Agda.Builtin.Equality public
    renaming (refl to idn)

  seq : ∀ {A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  seq idn g = g

  inv : ∀ {A} {x y : A} → x ≡ y → y ≡ x
  inv idn = idn

open ≡ public
  hiding (module _≡_)
  using (_≡_)

module ≅ where
  data _≅_ {A : Set} (x : A) : {B : Set} (y : B) → Set where
    idn : x ≅ x

  seq : ∀ {A B C}{x : A}{y : B}{z : C} → x ≅ y → y ≅ z → x ≅ z
  seq idn g = g

  inv : ∀ {A B}{x : A}{y : B} → x ≅ y → y ≅ x
  inv idn = idn

open ≅ public
  hiding (module _≅_)
  using (_≅_)

module 𝕊 where
  infixr 0 _⇒_
  _⇒_ : Set → Set → Set
  A ⇒ B = A → B

  idn : ∀ {A} → A ⇒ A
  idn x = x

  seq : ∀ {A B C} → A ⇒ B → B ⇒ C → A ⇒ C
  seq f g x = g (f x)

  data 𝟘 : Set where

  ¡ : ∀ {A} → 𝟘 ⇒ A
  ¡ ()

  record 𝟙 : Set where
    instance constructor tt

  ! : ∀ {A} → A ⇒ 𝟙
  ! _ = tt

  module _×_ where
    open import Agda.Builtin.Sigma public
      using (Σ)
      using (_,_)
      using (fst)
      using (snd)
    open import Agda.Builtin.Sigma
    _×_ : Set → Set → Set
    A × B = Σ A λ _ → B
  open _×_ public

  ⟨_,_⟩ : ∀ {X A B} → X ⇒ A → X ⇒ B → X ⇒ A × B
  ⟨_,_⟩ F G x .fst = F x
  ⟨_,_⟩ F G x .snd = G x

  ⟨_×_⟩ : ∀ {X Y A B} → X ⇒ A → Y ⇒ B → X × Y ⇒ A × B
  ⟨_×_⟩ F G = ⟨ seq fst F , seq snd G ⟩

  xchg : ∀ {A B C D} → (A × B) × (C × D) ⇒ (A × C) × (B × D)
  xchg = ⟨ ⟨ fst × fst ⟩ , ⟨ snd × snd ⟩ ⟩

open 𝕊 public
  using (Σ)
  using (tt)
  using (_,_)

module BNat where
  open import Agda.Builtin.Nat public
    renaming (Nat to ℕ)
    renaming (suc to succ)
  open import Agda.Builtin.FromNat
  open Number
  instance
    nat : Number ℕ
    nat .Constraint _ = 𝕊.𝟙
    nat .fromNat n = n

open BNat public

module ∞ℕ where
  infix 0 _≼_

  mutual
    data ∞ℕ : Set where
      zero : ∞ℕ
      succ : [∞ℕ] → ∞ℕ

    record [∞ℕ] : Set where
      coinductive
      field
        force : ∞ℕ

  open [∞ℕ] public

  {-# TERMINATING #-}
  ∞ : ∞ℕ
  ∞ = succ λ { .force → ∞ }

  into : ℕ → ∞ℕ
  into zero = zero
  into (succ n) = succ λ{ .force → into n }

  module _ where
    open import Agda.Builtin.FromNat
    open Number
    instance
      ∞nat : Number ∞ℕ
      ∞nat .Constraint n = 𝕊.𝟙
      ∞nat .fromNat n ⦃ tt ⦄ = into n

  _≼_ : ℕ → ∞ℕ → Set
  zero ≼ n = 𝕊.𝟙
  succ m ≼ zero = 𝕊.𝟘
  succ m ≼ succ n = m ≼ force n

  ↑≼ : ∀ {m n} .(p : m ≼ force n) → m ≼ succ n
  ↑≼ {zero} {n} p = tt
  ↑≼ {succ m} {n} p with force n
  ↑≼ {succ m} {n} () | zero
  ↑≼ {succ m} {n} p  | succ n′ = ↑≼ {m} {n′} p

  ↓≼ : ∀ {m} (n : ∞ℕ) .(p : succ m ≼ n) → m ≼ n
  ↓≼ {zero} n p = tt
  ↓≼ {succ m} zero ()
  ↓≼ {succ m} (succ n) p = ↓≼ (force n) p

open ∞ℕ public
  hiding (module ∞ℕ)

module ∞Graph where
  record ∞Graph {s : Size} : Set where
    coinductive
    field
      * : Set
      ∂ : (x y : *) {s′ : Size.< s} → ∞Graph {s′}
  open ∞Graph public

  record ∞Map {s} (A B : ∞Graph {s}) : Set where
    coinductive
    infixr 0 ⇑_
    field
      ap : * A → * B
      ⇑_ : ∀ {x y} {s′ : Size.< s} → ∞Map {s′} (A .∂ x y) (B .∂ (ap x) (ap y))
  open ∞Map public

  idn : ∀ {s A} → ∞Map {s} A A
  idn .ap = 𝕊.idn
  idn .⇑_ = idn

  seq : ∀ {s A B C} → ∞Map {s} A B → ∞Map {s} B C → ∞Map {s} A C
  seq F G .ap = 𝕊.seq (ap F) (ap G)
  seq F G .⇑_ = seq (⇑ F) (⇑ G)

  𝟘 : ∀ {s} → ∞Graph {s}
  𝟘 .* = 𝕊.𝟘
  𝟘 .∂ () ()

  ¡ : ∀ {s A} → ∞Map {s} 𝟘 A
  ¡ .ap = 𝕊.¡
  ¡ .⇑_ {()}{()}

  𝟙 : ∀ {s} → ∞Graph {s}
  𝟙 .* = 𝕊.𝟙
  𝟙 .∂ x y = 𝟙

  ! : ∀ {s A} → ∞Map {s} A 𝟙
  ! .ap = 𝕊.!
  ! .⇑_ = !

  _×_ : ∀ {s} → ∞Graph {s} → ∞Graph {s} → ∞Graph {s}
  _×_ A B .* = * A 𝕊.× * B
  _×_ A B .∂ (a₀ , b₀) (a₁ , b₁) = A .∂ a₀ a₁ × B .∂ b₀ b₁

  fst : ∀ {s A B} → ∞Map {s} (A × B) A
  fst .ap = 𝕊.fst
  fst .⇑_ = fst

  snd : ∀ {s A B} → ∞Map {s} (A × B) B
  snd .ap = 𝕊.snd
  snd .⇑_ = snd

  ⟨_,_⟩ : ∀ {s X A B} → ∞Map {s} X A → ∞Map {s} X B → ∞Map {s} X (A × B)
  ⟨_,_⟩ F G .ap = 𝕊.⟨ ap F , ap G ⟩
  ⟨_,_⟩ F G .⇑_ = ⟨ ⇑ F , ⇑ G ⟩

  ⟨_×_⟩ : ∀ {s X Y A B} → ∞Map {s} X A → ∞Map {s} Y B → ∞Map {s} (X × Y) (A × B)
  ⟨_×_⟩ F G = ⟨ seq fst F , seq snd G ⟩

  xchg : ∀ {s A B C D} → ∞Map {s} ((A × B) × (C × D)) ((A × C) × (B × D))
  xchg = ⟨ ⟨ fst × fst ⟩ , ⟨ snd × snd ⟩ ⟩

open ∞Graph public
  hiding (module ∞Graph)
  using (∞Graph)
  using (*)
  using (∂)
  using (∞Map)
  using (ap)
  using (⇑_)

module _ (Θ : ∞Graph) where
  infix 0 _∈_
  infixl 6 _▸_⇒_

  mutual
    data Disc : Set where
      · : Disc
      _▸_⇒_ : (Γ : Disc) (x y : ⟦Disc⟧ Γ .*) → Disc

    ⟦Disc⟧ : Disc → ∞Graph
    ⟦Disc⟧ · = Θ
    ⟦Disc⟧ (Γ ▸ x ⇒ y) = ⟦Disc⟧ Γ .∂ x y

  mutual
    data Diagram {r : ∞ℕ} : Set where
      · : Diagram
      _▸_⇒_ : (Ψ : Diagram {r}) (x y : ⟦Diagram⟧ Ψ) → Diagram

    ⟦Diagram⟧ : ∀ {r} → Diagram {r} → Set
    ⟦Diagram⟧ · = * Θ
    ⟦Diagram⟧ (Ψ ▸ x ⇒ y) = Cell (Ψ ▸ x ⇒ y)

    record Atom {r} (Ψ : Diagram {r}) : Set where
      inductive
      constructor [_⊢_]
      field
        {Γ} : Disc
        coe : Ψ ∈ Γ
        elm : ⟦Disc⟧ Γ .*
    pattern [_] {Γ}{coe} elm = [_⊢_] {Γ} coe elm

    data Cell {r : ∞ℕ} : Diagram {r} → Set where
      atom : ∀ {Ψ} → Atom Ψ → Cell Ψ
      idn : ∀ {Ψ x} → Cell (Ψ ▸ x ⇒ x)
      seq : ∀ {Ψ x y z} (f : Cell (Ψ ▸ x ⇒ y)) (g : Cell (Ψ ▸ y ⇒ z)) → Cell (Ψ ▸ x ⇒ z)
      inv : ∀ {Ψ x y} (f : Cell (Ψ ▸ x ⇒ y)) ⦃ ϕ : r ⊏ Ψ ⦄ → Cell (Ψ ▸ y ⇒ x)
      seq* : ∀ {Ψ x y z f f′ g g′}(α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ f′))(β : Cell (Ψ ▸ y ⇒ z ▸ g ⇒ g′)) → Cell (Ψ ▸ x ⇒ z ▸ seq {y = y} f g ⇒ seq {y = y} f′ g′)
      inv* : ∀ {Ψ x y f f′}(α : Cell (Ψ ▸ x ⇒ y ▸ f ⇒ f′)) ⦃ ϕ : r ⊏ Ψ ⦄ → Cell (Ψ ▸ y ⇒ x ▸ inv f ⦃ ϕ ⦄ ⇒ inv f′ ⦃ ϕ ⦄)
      uni-mon-λ : ∀ {Ψ x y f} → Cell (Ψ ▸ x ⇒ y ▸ seq idn f ⇒ f)
      uni-mon-ρ : ∀ {Ψ x y f} → Cell (Ψ ▸ x ⇒ y ▸ seq f idn ⇒ f)
      uni-mon-α : ∀ {Ψ w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → Cell (Ψ ▸ w ⇒ z ▸ seq (seq f g) h ⇒ seq f (seq g h))
      uni-gpd-κ : ∀ {Ψ x y f} ⦃ ϕ : r ⊏ Ψ ⦄ → Cell (Ψ ▸ y ⇒ y ▸ seq {y = x} (inv f ⦃ ϕ ⦄) f ⇒ idn)
      uni-gpd-ι : ∀ {Ψ x y f} ⦃ ϕ : r ⊏ Ψ ⦄ → Cell (Ψ ▸ x ⇒ x ▸ seq {y = y} f (inv f ⦃ ϕ ⦄) ⇒ idn)
      coh : ∀ {Ψ} {f g : ⟦Diagram⟧ {r} Ψ} (ϕ : Coh Ψ f) (ψ : Coh Ψ g) → Cell (Ψ ▸ f ⇒ g)

    data _∈_ {r} : Diagram {r} → Disc → Set where
      z : ∀ {a b}
        → · ▸ a ⇒ b ∈ · ▸ a ⇒ b
      s_ : ∀ {Ψ a b Γ x y f g}
        → (ϕ : Ψ ▸ a ⇒ b ∈ Γ ▸ x ⇒ y)
        → Ψ ▸ a ⇒ b ▸ atom [ ϕ ⊢ f ] ⇒ atom [ ϕ ⊢ g ] ∈ Γ ▸ x ⇒ y ▸ f ⇒ g

    data Coh {r} : ∀ Ψ → ⟦Diagram⟧ {r} Ψ → Set where
      idn : ∀ {Ψ x} → Coh (Ψ ▸ x ⇒ x) idn
      seq : ∀ {Ψ x y z f g} → Coh (Ψ ▸ x ⇒ y) f → Coh (Ψ ▸ y ⇒ z) g → Coh (Ψ ▸ x ⇒ z) (seq f g)
      inv : ∀ {Ψ x y f} ⦃ ϕ : r ⊏ Ψ ⦄ → Coh (Ψ ▸ x ⇒ y) f → Coh (Ψ ▸ y ⇒ x) (inv f ⦃ ϕ ⦄)
      seq* : ∀ {Ψ x y z f f′ g g′ α β} → Coh (Ψ ▸ x ⇒ y ▸ f ⇒ f′) α → Coh (Ψ ▸ y ⇒ z ▸ g ⇒ g′) β → Coh (Ψ ▸ x ⇒ z ▸ seq f g ⇒ seq f′ g′) (seq* α β)
      inv* : ∀ {Ψ x y f f′ α} ⦃ ϕ : r ⊏ Ψ ⦄ → Coh (Ψ ▸ x ⇒ y ▸ f ⇒ f′) α → Coh (Ψ ▸ y ⇒ x ▸ inv f ⦃ ϕ ⦄ ⇒ inv f′ ⦃ ϕ ⦄) (inv* α ⦃ ϕ ⦄)
      uni-mon-λ : ∀ {Ψ x y f} → Coh (Ψ ▸ x ⇒ y ▸ seq idn f ⇒ f) uni-mon-λ
      uni-mon-ρ : ∀ {Ψ x y f} → Coh (Ψ ▸ x ⇒ y ▸ seq f idn ⇒ f) uni-mon-ρ
      uni-mon-α : ∀ {Ψ w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → Coh (Ψ ▸ w ⇒ z ▸ seq (seq f g) h ⇒ seq f (seq g h)) uni-mon-α
      uni-gpd-κ : ∀ {Ψ x y f} ⦃ ϕ : r ⊏ Ψ ⦄ → Coh (Ψ ▸ y ⇒ y ▸ seq {y = x} (inv f ⦃ ϕ ⦄) f ⇒ idn) uni-gpd-κ
      uni-gpd-ι : ∀ {Ψ x y f} ⦃ ϕ : r ⊏ Ψ ⦄ → Coh (Ψ ▸ x ⇒ x ▸ seq {y = y} f (inv f ⦃ ϕ ⦄) ⇒ idn) uni-gpd-ι
      coh : ∀ {Ψ} {f g : ⟦Diagram⟧ {r} Ψ} (ϕ : Coh Ψ f) (ψ : Coh Ψ g) → Coh (Ψ ▸ f ⇒ g) (coh ϕ ψ)

    _⊏_ : ∀ {k} → ∞ℕ → Diagram {k} → Set
    zero ⊏ (_ ▸ _ ⇒ _) = 𝕊.𝟙
    succ n ⊏ (Ψ ▸ _ ⇒ _) = force n ⊏ Ψ
    _ ⊏ _ = 𝕊.𝟘

  dim : ∀ {r} → Diagram {r} → ℕ
  dim · = zero
  dim (Ψ ▸ _ ⇒ _) = succ (dim Ψ)

  record PreAlg {n r}
    {fuse : (Ψ : Diagram {r}) .{ϕ : dim Ψ ≼ n} → Disc}
    {fill : (Ψ : Diagram {r}) .{ϕ : dim Ψ ≼ n} → ⟦Diagram⟧ Ψ → ⟦Disc⟧ (fuse Ψ {ϕ}) .*}
    : Set where
    ⟦Cell⟧ : ∀ (Ψ : Diagram {r}) .{ϕ : dim Ψ ≼ n} (x y : ⟦Diagram⟧ Ψ) → Set
    ⟦Cell⟧ Ψ {ϕ} x y = ⟦Disc⟧ (fuse Ψ {ϕ}) .∂ (fill Ψ x) (fill Ψ y) .*
    field
      ⟦atom⟧ : ∀ {Ψ}.{ϕ}{x y} → Atom (Ψ ▸ x ⇒ y) → ⟦Cell⟧ Ψ {ϕ} x y
      ⟦idn⟧ : ∀ {Ψ}.{ϕ}{x} → ⟦Cell⟧ Ψ {ϕ} x x
      ⟦seq⟧ : ∀ {Ψ}.{ϕ}{x y z} (f : ⟦Cell⟧ Ψ {ϕ} x y) (g : ⟦Cell⟧ Ψ {ϕ} y z) → ⟦Cell⟧ Ψ {ϕ} x z
      ⟦inv⟧ : ∀ {Ψ}.{ϕ}{x y} (f : ⟦Cell⟧ Ψ {ϕ} x y) ⦃ ψ : r ⊏ Ψ ⦄ → ⟦Cell⟧ Ψ {ϕ} y x
      ⟦seq*⟧ : ∀ {Ψ}.{ϕ}{x y z f f′ g g′}(α : ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} f f′)(β : ⟦Cell⟧ (Ψ ▸ y ⇒ z) {ϕ} g g′) → ⟦Cell⟧ (Ψ ▸ x ⇒ z) {ϕ} (seq {y = y} f g) (seq {y = y} f′ g′)
      ⟦inv*⟧ : ∀ {Ψ}.{ϕ}{x y f f′}(α : ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} f f′) ⦃ ψ : r ⊏ Ψ ⦄ → ⟦Cell⟧ (Ψ ▸ y ⇒ x) {ϕ} (inv f ⦃ ψ ⦄) (inv f′ ⦃ ψ ⦄)
      ⟦uni-mon-λ⟧ : ∀ {Ψ}.{ϕ}{x y f} → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} (seq idn f) f
      ⟦uni-mon-ρ⟧ : ∀ {Ψ}.{ϕ}{x y f} → ⟦Cell⟧ (Ψ ▸ x ⇒ y) {ϕ} (seq f idn) f
      ⟦uni-mon-α⟧ : ∀ {Ψ}.{ϕ}{w x y z f h}{g : Cell (Ψ ▸ x ⇒ y)} → ⟦Cell⟧ (Ψ ▸ w ⇒ z) {ϕ} (seq (seq f g) h) (seq f (seq g h))
      ⟦uni-gpd-κ⟧ : ∀ {Ψ}.{ϕ}{x y f} ⦃ ψ : r ⊏ Ψ ⦄ → ⟦Cell⟧ (Ψ ▸ y ⇒ y) {ϕ} (seq {y = x} (inv f ⦃ ψ ⦄) f) idn
      ⟦uni-gpd-ι⟧ : ∀ {Ψ}.{ϕ}{x y f} ⦃ ψ : r ⊏ Ψ ⦄ → ⟦Cell⟧ (Ψ ▸ x ⇒ x) {ϕ} (seq {y = y} f (inv f ⦃ ψ ⦄)) idn
      -- FIXME: we will need to split this out in practice
      ⟦coh⟧ : ∀ {Ψ}.{ϕ}{f g : ⟦Diagram⟧ {r} Ψ} (ψ₀ : Coh Ψ f) (ψ₁ : Coh Ψ g) → ⟦Cell⟧ Ψ {ϕ} f g
  open PreAlg public

  fold : ∀ {n r f₀ f₁} (𝔉 : PreAlg {n}{r}{f₀}{f₁}) → ∀ {Ψ x y} → Cell {r} (Ψ ▸ x ⇒ y) → .{ϕ : dim Ψ ≼ n} → ⟦Cell⟧ 𝔉 Ψ {ϕ} x y
  fold 𝔉 (atom f) = ⟦atom⟧ 𝔉 f
  fold 𝔉 idn = ⟦idn⟧ 𝔉
  fold 𝔉 (seq f g) = ⟦seq⟧ 𝔉 (fold 𝔉 f) (fold 𝔉 g)
  fold 𝔉 (inv f ⦃ ϕ ⦄) = ⟦inv⟧ 𝔉 (fold 𝔉 f) ⦃ ϕ ⦄
  fold 𝔉 (seq* f g) = ⟦seq*⟧ 𝔉 (fold 𝔉 f) (fold 𝔉 g)
  fold 𝔉 (inv* f) = ⟦inv*⟧ 𝔉 (fold 𝔉 f)
  fold 𝔉 uni-mon-λ = ⟦uni-mon-λ⟧ 𝔉
  fold 𝔉 uni-mon-ρ = ⟦uni-mon-ρ⟧ 𝔉
  fold 𝔉 uni-mon-α = ⟦uni-mon-α⟧ 𝔉
  fold 𝔉 uni-gpd-κ = ⟦uni-gpd-κ⟧ 𝔉
  fold 𝔉 uni-gpd-ι = ⟦uni-gpd-ι⟧ 𝔉
  fold 𝔉 (coh ϕ ψ) = ⟦coh⟧ 𝔉 ϕ ψ

record Category (n r : ∞ℕ) : Set where
  field
    hom : ∞Graph {Size.∞}
  field
    {fuse} : (Ψ : Diagram hom {r}) .{ϕ : dim hom Ψ ≼ n} → Disc hom
    {fill} : (Ψ : Diagram hom {r}) .{ϕ : dim hom Ψ ≼ n}
              → ⟦Diagram⟧ hom Ψ → ⟦Disc⟧ hom (fuse Ψ {ϕ}) .*
    pre : PreAlg hom {n}{r}{fuse}{fill}
  field
    ⦃fuse/nil⦄ : fuse · {tt} ≡ ·
    ⦃fuse/ext⦄ : ∀ {Ψ x y}.{ϕ : 1 + dim hom Ψ ≼ n}
                 → fuse (Ψ ▸ x ⇒ y) {ϕ} ≡ fuse Ψ {↓≼ n ϕ} ▸ fill Ψ x ⇒ fill Ψ y
    ⦃fill/nil⦄ : ∀ {x} → fill · {tt} x ≅ x
    ⦃fill/ext⦄ : ∀ {Ψ x y f}.{ϕ : 1 + dim hom Ψ ≼ n}
                 → fill (Ψ ▸ x ⇒ y) {ϕ} f ≅ fold hom pre f {↓≼ n ϕ}
