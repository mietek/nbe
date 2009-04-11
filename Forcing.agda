module Forcing where
  open import Ctx
  open import Modalities
  open import Subsumption
  open import Syntax

  Forces : Ctx Type → Type → Set
  Forces Γ ●       = Neu Γ ●
  Forces Γ (α ⇒ β) = ∀ {Δ} → Γ ≤ Δ → Forces Δ α → Forces Δ β

  ForcesCtx : Ctx Type → Ctx Type → Set
  ForcesCtx Δ Γ = Box (Forces Δ) Γ
