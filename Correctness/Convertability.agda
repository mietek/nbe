module Correctness.Convertability where
  open import Ctx
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  open import Correctness.Substitution

  infix 0 _≈βη_
  data _≈βη_ {Γ : Ctx Type} : ∀ {α} → Term Γ α → Term Γ α → Set where
    β-red : ∀ {α β} (e₁ : Term (Γ ▸ β) α) {e₂}
          → ƛ e₁ · e₂ ≈βη subst e₁ e₂

    η-exp : ∀ {α β} {e : Term Γ (α ⇒ β)}
          → e ≈βη ƛ (wknTerm e · var vz)

