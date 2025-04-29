{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Skew where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Monoidal.Instance.Cats using (module Product)
open import Categories.Enriched.Category using () renaming (Category to Enriched)
open import Categories.Functor using (module Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)

{- -- Based on the definition in:

  A skew bicategory is like a bicategory, but the associator and/or
  unitors don't have to be invertible. Lack and Street developed this
  concept in this paper:

  Stephen Lack and Ross Street. On monads and warpings. Cahiers de topologie et géométrie
  diﬀérentielle catégoriques, LV(4):244–266, 2014. ISSN 1245-530X.


  Since we have 3 degrees of freedom, skew bicategory is in fact a
  3-trit paratmertised definition, depending whether the associator,
  left, and right unitors are left-skewed, right-skewed, or
  invertible.

  There might be a nice way to index this module in a way that defines
  all 3 simultaneously. Someone cleverer than us should do it.

  We will define the so-called right-skew bicategories only.

-}
record Skew o ℓ e t : Set (suc (o ⊔ ℓ ⊔ e ⊔ t)) where
  {- The non-skew definition, uses an `enriched` substructure to pack most of the data needed for a bicategory.
     This doesn't work for skew version. In detail: the non-skew version has natural isos for the associator and unitors
     which coincides with the setoid we choose for the cat-enrichment in `enriched`. For the skew version, we need
     mere natural transformations, which don't form a setoid, and so we cannot use that shortcut.

  -}

  infix 4 _⇒₁_ _⇒₂_
  infixr 7 _∘ᵥ_ _∘₁_
  infixr 11 _⊗₂_

  field
    Obj : Set o

    -- 1-cells
    --_⇒₁_ : Obj → Obj → Set o
    _⇒₁_ : Rel Obj ℓ
    --_≈_ : {A B : Obj} → Rel (A ⇒₁ B) e  -- might not need this
    id₁ : {A : Obj} -> A ⇒₁ A
    _∘₁_ : {A B C : Obj} -> B ⇒₁ C → A ⇒₁ B → A ⇒₁ C

  _⊗_ : {A B C : Obj} -> A ⇒₁ B → B ⇒₁ C → A ⇒₁ C
  f ⊗ g = g ∘₁ f

  field
    -- 2-cells
    _⇒₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set e
    id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
    _∘ₕ_ : {A B C : Obj} {f h : A ⇒₁ B} {g k : B ⇒₁ C} → g ⇒₂ k → f ⇒₂ h → g ∘₁ f ⇒₂ k ∘₁ h
    _∘ᵥ_ : {A B : Obj} {f g h : A ⇒₁ B} -> (β : g ⇒₂ h) → (α : f ⇒₂ g) → f ⇒₂ h

    _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e

  _⊗₂_ : {A B C : Obj} {f h : A ⇒₁ B} {g k : B ⇒₁ C} → f ⇒₂ h → g ⇒₂ k → g ∘₁ f ⇒₂ k ∘₁ h
  f ⊗₂ g = g ∘ₕ f

  field
    λ⇒ : {A B : Obj} {f : A ⇒₁ B} → (id₁ ⊗ f) ⇒₂ f
    ρ′⇒ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f ⊗ id₁
    α⇒ : {A B C D : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} →
          ((f ⊗ g) ⊗ h) ⇒₂ (f ⊗ (g ⊗ h))

  assoc : {A B C D : Obj} → (f : A ⇒₁ B) → (g : B ⇒₁ C) → (h : C ⇒₁ D)
          → ((f ⊗ g) ⊗ h) ⇒₂ (f ⊗ (g ⊗ h))
  assoc f g h = α⇒

  field
    -- vertical/horiz 2-cell comp preserve ≈
    ∘ₕ-resp-≈ : {A B C : Obj} {f g : A ⇒₁ B} {h k : B ⇒₁ C} {α α′ : f ⇒₂ g} {β β′ : h ⇒₂ k} → α ≈ α′ → β ≈ β′ → (β ∘ₕ α) ≈ (β′ ∘ₕ α′)

    ∘ᵥ-resp-≈ : {A B : Obj} {f g h k : A ⇒₁ B} {α α′ : f ⇒₂ g} {β β′ : g ⇒₂ h} → α ≈ α′ → β ≈ β′ → (β ∘ᵥ α) ≈ (β′ ∘ᵥ α′)

    pentagon : {A B C D E : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {k : D ⇒₁ E}
             → (assoc f g (h ⊗ k) ∘ᵥ assoc (f ⊗ g) h k) ≈ (((id₂ ⊗₂ α⇒) ∘ᵥ α⇒) ∘ᵥ (α⇒ ⊗₂ id₂))

    -- Triangles and rectangle
    -- These are incomprehensible, one really ought to draw the diagrams!
    rectangle : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C}
              → (((id₂ {f = f}  ⊗₂ λ⇒) ∘ᵥ α⇒) ∘ᵥ (ρ′⇒ ⊗₂ id₂ {f = g})) ≈ id₂

    skew-left : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C}
              → (λ⇒ ∘ᵥ α⇒ {g = f}) ≈ (λ⇒ ⊗₂ id₂ {f = g})

    skew-right : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C}
               → (α⇒ {f = f} {g = g} ∘ᵥ ρ′⇒) ≈ (id₂ ⊗₂ ρ′⇒)

    skew-triangle : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C}
                  → (λ⇒ ∘ᵥ ρ′⇒) ≈ id₂ {f = id₁ {A = A}}

{-


  _⇒₂_ = hom._⇒_

  _⊚₀_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  f ⊚₀ g = Functor.F₀ ⊚ (f , g)

  _⊚₁_ : {A B C : Obj} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  α ⊚₁ β = Functor.F₁ ⊚ (α , β)

  _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
  _≈_ = hom._≈_

  id₁ : {A : Obj} → A ⇒₁ A
  id₁ {_} = Functor.F₀ id _

  id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
  id₂ {A} {B} = Category.id (hom A B)

  -- 1-cell composition
  _∘₁_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C
  _∘₁_ = _⊚₀_

  -- horizontal composition
  _∘ₕ_ : {A B C : Obj} {f h : B ⇒₁ C} {g i : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → f ⊚₀ g ⇒₂ h ⊚₀ i
  _∘ₕ_ = _⊚₁_

  -- vertical composition
  _∘ᵥ_ : {A B : Obj} {f g h : A ⇒₁ B} (α : g ⇒₂ h) (β : f ⇒₂ g) → f ⇒₂ h
  _∘ᵥ_ = hom._∘_

  _◁_ : {A B C : Obj} {g h : B ⇒₁ C} (α : g ⇒₂ h) (f : A ⇒₁ B) → g ∘₁ f ⇒₂ h ∘₁ f
  α ◁ _ = α ⊚₁ id₂

  _▷_ : {A B C : Obj} {f g : A ⇒₁ B} (h : B ⇒₁ C) (α : f ⇒₂ g) → h ∘₁ f ⇒₂ h ∘₁ g
  _ ▷ α = id₂ ⊚₁ α

  private
    λ⇒ : {A B : Obj} {f : A ⇒₁ B} → id₁ ⊚₀ f hom.⇒ f
    λ⇒ {_} {_} {f} = NaturalIsomorphism.⇒.η unitˡ (_ , f)

    ρ⇒ : {A B : Obj} {f : A ⇒₁ B} → f ⊚₀ id₁ hom.⇒ f
    ρ⇒ {_} {_} {f} = NaturalIsomorphism.⇒.η unitʳ (f , _)

    α⇒ : {A B C D : Obj} {f : D ⇒₁ B} {g : C ⇒₁ D} {h : A ⇒₁ C} →
          ((f ⊚₀ g) ⊚₀ h) hom.⇒ (f ⊚₀ (g ⊚₀ h))
    α⇒ {_} {_} {_} {_} {f} {g} {h} = NaturalIsomorphism.⇒.η ⊚-assoc ((f , g) , h)

  field
    triangle : {A B C : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} →
                 let open ComHom {A} {C} in
                 [ (g ∘₁ id₁) ∘₁ f ⇒ g ∘₁ f ]⟨
                   α⇒                 ⇒⟨ g ∘₁ id₁ ∘₁ f ⟩
                   g ▷ λ⇒
                 ≈ ρ⇒ ◁ f
                 ⟩
    pentagon : {A B C D E : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {i : D ⇒₁ E} →
                 let open ComHom {A} {E} in
                 [ ((i ∘₁ h) ∘₁ g) ∘₁ f ⇒ i ∘₁ h ∘₁ g ∘₁ f ]⟨
                   α⇒ ◁ f                     ⇒⟨ (i ∘₁ h ∘₁ g) ∘₁ f ⟩
                   α⇒                         ⇒⟨ i ∘₁ (h ∘₁ g) ∘₁ f ⟩
                   i ▷ α⇒
                 ≈ α⇒                         ⇒⟨ (i ∘₁ h) ∘₁ g ∘₁ f ⟩
                   α⇒
                 ⟩
-}
open import Categories.Category.Construction.Presheaves using (Presheaves)
open import Categories.Category.Construction.Functors
open import Categories.Category.Product using (Product)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Data.Product using (Σ; _×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)

open Setoid

module _ {ℓ₁ ℓ₂ : Level} (S : Set) (R : (s : S) → Setoid ℓ₁ ℓ₂ ) where

  data SetoidCoprodEquivExplicit
    : (s₁ : S) → (r₁ : Carrier (R s₁)) →
      (s₂ : S) → (r₁ : Carrier (R s₂)) → Set (ℓ₁ ⊔ ℓ₂) where
    _⊩_≈_by_ : (s : S) → (r₁ r₂ : Carrier (R s)) → ((R s)._≈_ r₁ r₂ ) →
      SetoidCoprodEquivExplicit s r₁ s r₂


  SetoidCoprodEquiv : Rel (Σ S (λ s → Carrier (R s))) {!!}
  SetoidCoprodEquiv (s₁ , r₁) (s₂ , r₂) = SetoidCoprodEquivExplicit s₁ r₁ s₂ r₂

  SetoidCoprodIsEquivalence : IsEquivalence SetoidCoprodEquiv
  IsEquivalence.refl SetoidCoprodIsEquivalence {s , r} = s ⊩ r ≈ r by (R s).refl
  IsEquivalence.sym SetoidCoprodIsEquivalence = {!!}
  IsEquivalence.trans SetoidCoprodIsEquivalence = {!!}

-- Move this to Skew/Constructions/Bimodules
SkewBimod : {o ℓ e t o′ ℓ′ : Level} → Skew (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e ⊔ suc o′ ⊔ suc ℓ′) (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) t
SkewBimod {o} {ℓ} {e} .Skew.Obj = Category o ℓ e
SkewBimod {o′ = o′} {ℓ′ = ℓ′} .Skew._⇒₁_ 𝔸 𝔹 = Presheaves {o′ = o′} {ℓ′ = ℓ′} (Product (Category.op 𝔸) 𝔹) .Category.Obj
SkewBimod {o′ = o′} {ℓ′ = ℓ′} .Skew.id₁ {A = 𝔸} = {!!}
Skew._∘₁_ SkewBimod {A = 𝔸} {B = 𝔹} {C = ℂ} p q .Functor.F₀ (a , c) = {!? ×ₛ ?!}
Skew._∘₁_ SkewBimod {A = 𝔸} {B = 𝔹} {C = ℂ} p q .Functor.F₁ = {!!}
Skew._∘₁_ SkewBimod {A = 𝔸} {B = 𝔹} {C = ℂ} p q .Functor.identity = {!!}
Skew._∘₁_ SkewBimod {A = 𝔸} {B = 𝔹} {C = ℂ} p q .Functor.homomorphism = {!!}
Skew._∘₁_ SkewBimod {A = 𝔸} {B = 𝔹} {C = ℂ} p q .Functor.F-resp-≈ = {!!}
SkewBimod .Skew._⇒₂_ {A = 𝔸} {B = 𝔹} p q = NaturalTransformation p q
SkewBimod .Skew._≈_ = {!!}
SkewBimod .Skew.id₂ = {!!}
SkewBimod .Skew._∘ₕ_ = {!!}
SkewBimod .Skew._∘ᵥ_ = {!!}
SkewBimod .Skew.λ⇒ = {!!}
SkewBimod .Skew.ρ′⇒ = {!!}
SkewBimod .Skew.α⇒ = {!!}
SkewBimod .Skew.pentagon = {!!}
SkewBimod .Skew.rectangle = {!!}
SkewBimod .Skew.skew-left = {!!}
SkewBimod .Skew.skew-right = {!!}
SkewBimod .Skew.skew-triangle = {!!}
SkewBimod .Skew.∘ₕ-resp-≈ = {!!}
SkewBimod .Skew.∘ᵥ-resp-≈ = {!!}
