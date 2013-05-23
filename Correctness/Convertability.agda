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
  data _≃_ {Γ} : ∀ {α} → Rel (Term Γ α) where
    ≃-β : ∀ {α β} (e₁ : Term (Γ ▸ β) α) e₂
        → ƛ e₁ · e₂ ≃ subst e₂ e₁

    ≃-ξ : ∀ {α β} {e₁ e₂ : Term Γ β}
        → e₁ ≃ e₂
        → ƛ_ {α = α} (wknTerm e₁) ≃ ƛ_ {α = α} (wknTerm e₂)

    ≃-η : ∀ {α β} (e : Term Γ (α ⇒ β))
        → e ≃ ƛ (wknTerm e · var vz)

    ≃-ρ : ∀ {α} (e : Term Γ α)
        → e ≃ e

    ≃-μ : ∀ {α β} (f : Term Γ (α ⇒ β)) {x₁ x₂ : Term Γ α}
        → x₁ ≃ x₂
        → f · x₁ ≃ f · x₂

    ≃-ν : ∀ {α β} {f₁ f₂ : Term Γ (α ⇒ β)} (x : Term Γ α)
        → f₁ ≃ f₂
        → f₁ · x ≃ f₂ · x

    ≃-σ : ∀ {α} {e₁ e₂ : Term Γ α}
        → e₁ ≃ e₂
        → e₂ ≃ e₁

    ≃-τ : ∀ {α} {e₁ e₂ e₃ : Term Γ α}
        → e₁ ≃ e₂
        → e₂ ≃ e₃
        → e₁ ≃ e₃
