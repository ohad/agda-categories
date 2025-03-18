{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Skew where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary using (Rel)

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
    _⇒₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set ℓ
    _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
    id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
    _⊗₂_ : {A B C : Obj} {g i : B ⇒₁ C} {f h : A ⇒₁ B} → f ⇒₂ h → g ⇒₂ i → g ∘₁ f ⇒₂ i ∘₁ h
    _∘ᵥ_ : {A B : Obj} {f g h : A ⇒₁ B} -> (β : g ⇒₂ h) → (α : f ⇒₂ g) → f ⇒₂ h


  --private
    λ⇒ : {A B : Obj} {f : A ⇒₁ B} → (id₁ ⊗ f) ⇒₂ f
    ρ'⇒ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f ⊗ id₁
    α⇒ : {A B C D : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} →
          ((f ⊗ g) ⊗ h) ⇒₂ (f ⊗ (g ⊗ h))

  assoc : {A B C D : Obj} → (f : A ⇒₁ B) → (g : B ⇒₁ C) → (h : C ⇒₁ D)
          → ((f ⊗ g) ⊗ h) ⇒₂ (f ⊗ (g ⊗ h))
  assoc f g h = α⇒

  field
    makeThisFieldNonEmpty : Set
    -- vertical/horiz 2-cell comp preserve ≈


    pentagon : {A B C D E : Obj} {f : A ⇒₁ B} {g : B ⇒₁ C} {h : C ⇒₁ D} {k : D ⇒₁ E}
      → (assoc f g (h ⊗ k) ∘ᵥ assoc (f ⊗ g) h k) ≈ (((id₂ ⊗₂ α⇒) ∘ᵥ α⇒) ∘ᵥ (α⇒ ⊗₂ id₂))

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
