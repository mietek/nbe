module Weaken where
  open import Data.Function
    using (_∘_)

  open import Forcing
  open import Modalities
  open import Subsumption
  open import Syntax

  mutual
    wknNeu : ∀ {Γ Δ} → Γ ≤ Δ → Neu Γ ⊆ Neu Δ
    wknNeu Γ≤Δ (var x  ) = var (lookup Γ≤Δ x)
    wknNeu Γ≤Δ (ne · nm) = wknNeu Γ≤Δ ne · wknNrm Γ≤Δ nm

    wknNrm : ∀ {Γ Δ} → Γ ≤ Δ → Nrm Γ ⊆ Nrm Δ
    wknNrm Γ≤Δ (ƛ nm)   = ƛ (wknNrm (▸-mono Γ≤Δ) nm)
    wknNrm Γ≤Δ (neu ne) = neu (wknNeu Γ≤Δ ne)

  wknVal : ∀ {Γ Δ} → Γ ≤ Δ → Forces Γ ⊆ Forces Δ
  wknVal Γ≤Δ {●}     ne = wknNeu Γ≤Δ ne
  wknVal Γ≤Δ {α ⇒ β} f  = λ Δ≤Σ v → f (≤-trans Γ≤Δ Δ≤Σ) v

  wknCtx : ∀ {Γ Δ} → Γ ≤ Δ → ForcesCtx Γ ⊆ ForcesCtx Δ
  wknCtx = map ∘ wknVal