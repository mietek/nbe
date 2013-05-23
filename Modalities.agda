-------------------------------------------------------------------------------
-- Type Modalities (a.k.a. Predicate Transformers)
-------------------------------------------------------------------------------

-- See Peter Morris's thesis for background.

module Modalities where
  open import Data.Product
    using ( Σ
          ; ,_ )

  open import Ctx
  open import Predicates

-------------------------------------------------------------------------------
-- Box (a.k.a. Everywhere) Modality

  data Box {χ} (ϕ : Pred χ) : Pred (Ctx χ) where
    ε   : Box ϕ ε

    _▸_ : ∀ {Γ α}
        → (Γ□  : Box ϕ Γ)
        → (ϕ-α : ϕ α)
        → Box ϕ (Γ ▸ α)

  -- Dual to find
  fill : ∀ {χ ϕ} {Γ : Ctx χ} → Π χ ϕ → Box ϕ Γ
  fill {Γ = ε}     f = ε
  fill {Γ = Γ ▸ α} f = fill f ▸ f α

-------------------------------------------------------------------------------
-- Dia (a.k.a. Somewhere) Modality

  data Dia {χ} (ϕ : Pred χ) : Pred (Ctx χ) where
    here  : ∀ {Γ α}
          → (ϕ-α : ϕ α)
          → Dia ϕ (Γ ▸ α)

    there : ∀ {Γ α}
          → (Γ◇  : Dia ϕ Γ)
          → Dia ϕ (Γ ▸ α)

  -- Dual to fill
  find : ∀ {χ ϕ Γ} → Dia ϕ Γ → Σ χ ϕ
  find (here  ϕ-α) = , ϕ-α
  find (there Γ◇)  = find Γ◇

-------------------------------------------------------------------------------
-- Operations

  map : ∀ {χ} {ϕ φ : Pred χ} → ϕ ⊆ φ → Box ϕ ⊆ Box φ
  map f ε          = ε
  map f (Γ□ ▸ ϕ-α) = map f Γ□ ▸ f ϕ-α
