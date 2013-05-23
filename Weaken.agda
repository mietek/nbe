-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

module Weaken where
  open import Data.Function
    using (_∘_)

  open import Ctx
  open import Modalities
  open import Model
  open import Predicates
  open import Subsumption
  open import Syntax
  open import Vars

  -- Arbitrarily weaken a term
  wknTerm* : ∀ {Γ Δ} → Γ ⊇ Δ → Term Δ ⊆ Term Γ
  wknTerm* Γ⊇Δ (var x)   = var (lookup Γ⊇Δ x)
  wknTerm* Γ⊇Δ (ƛ e)     = ƛ wknTerm* (▸-mono Γ⊇Δ) e
  wknTerm* Γ⊇Δ (e₁ · e₂) = wknTerm* Γ⊇Δ e₁ · wknTerm* Γ⊇Δ e₂

  -- Weaken a term by a single step
  wknTerm : ∀ {Γ α} → Term Γ ⊆ Term (Γ ▸ α)
  wknTerm = wknTerm* ▸-step

  -- If Δ subsumes Γ, then we can map Neutral / Normal forms under Γ
  -- to their respective forms under Δ.
  mutual
    wknNeu* : ∀ {Γ Δ} → Γ ⊇ Δ → Neu Δ ⊆ Neu Γ
    wknNeu* Γ⊇Δ (var x  ) = var (lookup Γ⊇Δ x)
    wknNeu* Γ⊇Δ (ne · nm) = wknNeu* Γ⊇Δ ne · wknNrm* Γ⊇Δ nm

    wknNrm* : ∀ {Γ Δ} → Γ ⊇ Δ → Nrm Δ ⊆ Nrm Γ
    wknNrm* Γ⊇Δ (ƛ nm)   = ƛ (wknNrm* (▸-mono Γ⊇Δ) nm)
    wknNrm* Γ⊇Δ (neu ne) = neu (wknNeu* Γ⊇Δ ne)

  -- If Δ subsumes Γ, then whatever proposition (type) Γ forces, Δ
  -- also forces.  We can view this as letting us convert semantic
  -- values under one context to another.
  wknVal* : ∀ {Γ Δ} → Γ ⊇ Δ → Val Δ ⊆ Val Γ
  wknVal* Γ⊇Δ {●}     ne = wknNeu* Γ⊇Δ ne
  wknVal* Γ⊇Δ {α ⇒ β} f  = λ Σ⊇Γ v → f (⊇-trans Σ⊇Γ Γ⊇Δ) v

  -- If Δ subsumes Γ, then whatever world (context) Γ forces, Δ also
  -- forces.  We can view this as letting us change the codomain of a
  -- substitution.
  wknEnv* : ∀ {Γ Δ} → Γ ⊇ Δ → Env Δ ⊆ Env Γ
  wknEnv* = map ∘ wknVal*
