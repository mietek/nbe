-------------------------------------------------------------------------------
-- The Krikpe Model
-------------------------------------------------------------------------------

module Model where
  open import Ctx
  open import Modalities
  open import Predicates
  open import Subsumption
  open import Syntax
  open import Vars

  -- The forcing relation (Γ ⊩ α) constructs a universe corresponding
  -- to a Kripke model for intuitionistic propositional logic.
  -- 'Val Γ α' can be read as 'Value Γ α'.
  Val : Rel (Ctx Type) Type
  Val Γ ●       = Neu Γ ●
  Val Γ (α ⇒ β) = ∀ {Δ} → Δ ⊇ Γ → Val Δ α → Val Δ β

  -- The forcing relation with respect to a context (Γ ⊩* Δ), i.e., Γ
  -- forces everything in Δ. 'Env Γ Δ' can be read as 'Env Γ Δ'.
  Env : EndoRel (Ctx Type)
  Env Γ Δ = Box (Val Γ) Δ

  -- Γ entails α in the Kripke model if any world (context) Δ forces α
  -- whenever Δ forces Γ.
  Models : Rel (Ctx Type) Type
  Models Γ α = ∀ {Δ} → Env Δ Γ → Val Δ α
