-------------------------------------------------------------------------------
-- Context Subsumption Relation
-------------------------------------------------------------------------------

module Subsumption where
  open import Data.Function
    using (id)

  open import Ctx
  open import Modalities
  open import Syntax
  open import Vars

  -- Context Subsumption, i.e., there is a corresponding variable in Δ
  -- for every variable in Γ.
  infix 0 _≤_
  _≤_ : Ctx Type → Ctx Type → Set
  Γ ≤ Δ = Box (Var Δ) Γ

  -- Snoc is increasing.
  ▸-incr : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ≤ Δ ▸ α
  ▸-incr ρ = map vs ρ

  -- Snoc is monotonic.
  ▸-mono : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ▸ α ≤ Δ ▸ α
  ▸-mono ρ = map vs ρ ▸ vz

  -- Context subsumption is reflexive.
  ≤-refl : ∀ {Γ} → Γ ≤ Γ
  ≤-refl = tabulate id

  -- Context subsumption is transitive.
  ≤-trans : ∀ {Γ Δ Σ} → Γ ≤ Δ → Δ ≤ Σ → Γ ≤ Σ
  ≤-trans ρ₁ ρ₂ = map (lookup ρ₂) ρ₁

  ▸-step : ∀ {Γ α} → Γ ≤ Γ ▸ α
  ▸-step = ▸-incr ≤-refl
