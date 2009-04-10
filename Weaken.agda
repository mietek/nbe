module Weaken where
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Values

  mutual
    wknNeu : ∀ {Γ Δ} → Γ ≤ Δ → Neu Γ ⊆ Neu Δ
    wknNeu ρ (var x  ) = var (lookup ρ x)
    wknNeu ρ (ne · nm) = wknNeu ρ ne · wknNrm ρ nm

    wknNrm : ∀ {Γ Δ} → Γ ≤ Δ → Nrm Γ ⊆ Nrm Δ
    wknNrm ρ (ƛ nm)   = ƛ (wknNrm (▸-mono ρ) nm)
    wknNrm ρ (neu ne) = neu (wknNeu ρ ne)

    wknVal : ∀ {Γ Δ} → Γ ≤ Δ → Val Γ ⊆ Val Δ
    wknVal ρ {●}     ne = wknNeu ρ ne
    wknVal ρ {α ⇒ β} f  = λ ρ′ v → f (≤-trans ρ ρ′) v
