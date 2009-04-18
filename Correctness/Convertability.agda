module Correctness.Convertability where
  open import Relation.Binary
    using ( Rel )

  open import Ctx
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  open import Correctness.Substitution

  infix 0 _≃_
  data _≃_ {Γ : Ctx Type} : ∀ {α} → Rel (Term Γ α) where
    β-red : ∀ {α β} (e₁ : Term (Γ ▸ β) α) e₂
          → ƛ e₁ · e₂ ≃ subst e₂ e₁

    η-exp : ∀ {α β} {e : Term Γ (α ⇒ β)}
          → e ≃ ƛ (wknTerm e · var vz)

