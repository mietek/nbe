-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

module Weaken where
  open import Data.Function
    using (_∘_)

  open import Forcing
  open import Modalities
  open import Subsumption
  open import Syntax

  -- If Δ subsumes Γ, then we can map Neutral / Normal forms under Γ
  -- to their respective forms under Δ.
  mutual
    wknNeu : ∀ {Γ Δ} → Γ ≤ Δ → Neu Γ ⊆ Neu Δ
    wknNeu Γ≤Δ (var x  ) = var (lookup Γ≤Δ x)
    wknNeu Γ≤Δ (ne · nm) = wknNeu Γ≤Δ ne · wknNrm Γ≤Δ nm

    wknNrm : ∀ {Γ Δ} → Γ ≤ Δ → Nrm Γ ⊆ Nrm Δ
    wknNrm Γ≤Δ (ƛ nm)   = ƛ (wknNrm (▸-mono Γ≤Δ) nm)
    wknNrm Γ≤Δ (neu ne) = neu (wknNeu Γ≤Δ ne)

  -- If Δ subsumes Γ, then whatever proposition (type) Γ forces, Δ
  -- also forces.  We can view this as letting us convert semantic
  -- values under one context to another.
  wknForces : ∀ {Γ Δ} → Γ ≤ Δ → Forces Γ ⊆ Forces Δ
  wknForces Γ≤Δ {●}     ne = wknNeu Γ≤Δ ne
  wknForces Γ≤Δ {α ⇒ β} f  = λ Δ≤Σ v → f (≤-trans Γ≤Δ Δ≤Σ) v

  -- If Δ subsumes Γ, then whatever world (context) Γ forces, Δ also
  -- forces.  We can view this as letting us change the codomain of a
  -- substitution.
  wknSub : ∀ {Γ Δ} → Γ ≤ Δ → ForcesCtx Γ ⊆ ForcesCtx Δ
  wknSub = map ∘ wknForces
