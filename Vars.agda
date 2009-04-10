module Vars {χ : Set} where
  open import Ctx
  open import Modalities

  open import Relation.Binary.PropositionalEquality

  -- Generic vars in terms of Dia
  Var : Ctx χ → χ → Set
  Var Γ α = Dia (_≡_ α) Γ

  vz : ∀ {Γ α} → Var (Γ ▸ α) α
  vz = here refl

  vs : ∀ {Γ α β} → Var Γ α → Var (Γ ▸ β) α
  vs = there
