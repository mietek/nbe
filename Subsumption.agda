-------------------------------------------------------------------------------
-- Context Subsumption Relation
-------------------------------------------------------------------------------

module Subsumption where
  open import Data.Function
    using ( id )
  open import Relation.Binary
    using ( Rel )
  open import Relation.Binary.Core
    using ( Reflexive
          ; Transitive )

  open import Ctx
  open import Modalities
  open import Syntax
  open import Vars

  -- Context Subsumption, i.e., there is a corresponding variable in Δ
  -- for every variable in Γ.
  infix 0 _≤_
  _≤_ : EndoRel (Ctx Type)
  Γ ≤ Δ = Box (Var Δ) Γ

  -- Context subsumption is reflexive.
  ≤-refl : Reflexive _≤_
  ≤-refl = tabulate id

  -- Context subsumption is transitive.
  ≤-trans : Transitive _≤_
  ≤-trans ρ₁ ρ₂ = map (lookup ρ₂) ρ₁

  -- Snoc is increasing.
  ▸-incr : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ≤ Δ ▸ α
  ▸-incr ρ = map vs ρ

  -- Snoc is monotonic.
  ▸-mono : ∀ {Γ Δ α} → Γ ≤ Δ → Γ ▸ α ≤ Δ ▸ α
  ▸-mono ρ = map vs ρ ▸ vz

  ▸-step : ∀ {Γ} {α} → Γ ≤ Γ ▸ α
  ▸-step = ▸-incr ≤-refl
