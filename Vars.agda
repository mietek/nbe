-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

module Vars {χ : Set} where
  open import Data.Function
    using ( _∘_ )
  open import Relation.Binary.PropositionalEquality
    using ( _≡_
          ; refl )

  open import Ctx
  open import Modalities
  open import Predicates

-------------------------------------------------------------------------------
-- Variables as "deBruijn predicate families"

  -- The intuition behind 'Var Γ α' is 'Γ ∋ α'
  Var : Ctx χ → Pred χ
  Var Γ α = Dia (_≡_ α) Γ

  vz : ∀ {Γ α} → Var (Γ ▸ α) α
  vz = here refl

  vs : ∀ {Γ α} → Var Γ ⊆ Var (Γ ▸ α)
  vs = there

-------------------------------------------------------------------------------
-- Operations

  lookup : ∀ {ϕ Γ} → Box ϕ Γ → Var Γ ⊆ ϕ
  lookup {Γ = ε} _          ()
  lookup         (_  ▸ ϕ-α) (here  refl) = ϕ-α
  lookup         (Γ□ ▸ _  ) (there p)    = lookup Γ□ p

  tabulate : ∀ {ϕ Γ} → Var Γ ⊆ ϕ → Box ϕ Γ
  tabulate {Γ = ε}     f = ε
  tabulate {Γ = Γ ▸ a} f = tabulate (f ∘ vs) ▸ f vz
