module Subsumption where
  open import Data.Function
    using (id)

  open import Ctx
  open import Modalities
  open import Syntax
  open import Vars

  -- Context Subsumption
  infix 0 _≤_
  _≤_ : Ctx Type → Ctx Type → Set
  Γ ≤ Δ = Box (Var Δ) Γ

  ▸-incr : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ≤ Δ ▸ α
  ▸-incr ρ = map vs ρ

  ▸-mono : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ▸ α ≤ Δ ▸ α
  ▸-mono ρ = map vs ρ ▸ vz

  ≤-refl : ∀ {Γ} → Γ ≤ Γ
  ≤-refl = tabulate id

  ≤-trans : ∀ {Γ Δ Σ} → Γ ≤ Δ → Δ ≤ Σ → Γ ≤ Σ
  ≤-trans ρ₁ ρ₂ = map (lookup ρ₂) ρ₁

  ≤-incr : ∀ {Γ α} → Γ ≤ Γ ▸ α
  ≤-incr = ▸-incr ≤-refl