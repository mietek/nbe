-------------------------------------------------------------------------------
-- The Forcing relations for the Kripke structure
-------------------------------------------------------------------------------

module Forcing where
  open import Ctx
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Vars

  -- The forcing relation (Γ ⊩ α) constructs a universe corresponding
  -- to a Kripke model for intuitionistic propositional logic.
  Forces : Ctx Type → Type → Set
  Forces Γ ●       = Neu Γ ●
  Forces Γ (α ⇒ β) = ∀ {Δ} → Γ ≤ Δ → Forces Δ α → Forces Δ β

  -- The forcing relation with respect to a context (Γ ⊩* Δ), i.e., Γ
  -- forces everything in Δ
  ForcesCtx : Ctx Type → Ctx Type → Set
  ForcesCtx Γ Δ = Box (Forces Γ) Δ

  -- Apply a substitution to a variable.
  [_]_ : ∀ {Γ Δ α} → ForcesCtx Γ Δ → Var Δ α → Forces Γ α
  [_]_ = lookup
