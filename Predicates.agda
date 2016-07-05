-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------

module Predicates where

  open import Relation.Unary public
    using ( _∈_ )
    renaming ( Pred to Predℓ )

  open import Level
    using ( zero )

  Pred : Set → Set₁
  Pred A = Predℓ A zero


-------------------------------------------------------------------------------
-- Misc

  -- Pretty Pi
  Π : ∀ χ → Pred χ → Set
  Π χ ϕ = (α : χ) → ϕ α

-------------------------------------------------------------------------------
-- Relations

  -- Relations are just binary predicates.
  Rel : Set → Set → Set1
  Rel α β = α → β → Set

  -- Relations with the same domain and codomain.
  EndoRel : Set → Set1
  EndoRel α = Rel α α

  -- EndoRelations for Set1
  -- (I want universe polymorphism...)
  EndoRel₁₁ : Set1 → Set1
  EndoRel₁₁ α = α → α → Set

-------------------------------------------------------------------------------
-- Predicate Inclusion

  _⊆_ : ∀ {χ} → EndoRel₁₁ (Pred χ)
  ϕ ⊆ φ = ∀ {α} → α ∈ ϕ → α ∈ φ
