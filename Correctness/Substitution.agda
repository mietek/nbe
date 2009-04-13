module Correctness.Substitution where
  open import Relation.Binary.PropositionalEquality
    hiding (subst)

  open import Ctx
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  lift : ∀ {Γ Δ α} → Var Γ ⊆ Term Δ → Var (Γ ▸ α) ⊆ Term (Δ ▸ α)
  lift σ (here  refl) = var vz
  lift σ (there x)    = wknTerm (σ x)

  substSim : ∀ {Γ Δ} → Var Γ ⊆ Term Δ → Term Γ ⊆ Term Δ
  substSim σ (var x)   = σ x
  substSim σ (ƛ e)     = ƛ substSim (lift σ) e
  substSim σ (e₁ · e₂) = substSim σ e₁ · substSim σ e₂

  subst : ∀ {Γ α β} → Term (Γ ▸ α) β → Term Γ α → Term Γ β
  subst {Γ} {α} e₁ e₂ = substSim σ e₁
    where
      σ : Var (Γ ▸ α) ⊆ Term Γ
      σ (here  refl) = e₂
      σ (there x)    = var x
