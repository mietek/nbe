-------------------------------------------------------------------------------
-- Generic variables via well-scoped DeBruijn indices
-------------------------------------------------------------------------------

module Vars {χ : Set} where
  open import Ctx
  open import Modalities

  open import Relation.Binary.PropositionalEquality

  -- Var Γ α means that there is a variable of type α somewhere in Γ
  Var : Ctx χ → χ → Set
  Var Γ α = Dia (_≡_ α) Γ

  -- The variable is at the head of the context.
  vz : ∀ {Γ α} → Var (Γ ▸ α) α
  vz = here refl

  -- The variable is somewhere else in the context.
  vs : ∀ {Γ α β} → Var Γ α → Var (Γ ▸ β) α
  vs = there
