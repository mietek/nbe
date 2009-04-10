module Values where
  open import Ctx
  open import Subsumption
  open import Syntax

  Val : Ctx Type → Type → Set
  Val Γ ●       = Neu Γ ●
  Val Γ (α ⇒ β) = ∀ {Δ} → Γ ≤ Δ → Val Δ α → Val Δ β
