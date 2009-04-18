-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

module Syntax where
  open import Relation.Unary
    using ( Pred )

  open import Ctx
  open import Modalities
    using ( Rel
          ; _⊆_ )
  open import Vars

  infixr 1 _⇒_
  data Type : Set where
    ●   : Type
    _⇒_ : Type → Type → Type

  infixl 5 _·_
  data Term : Rel (Ctx Type) Type where
    var : ∀ {Γ}     → Var Γ ⊆ Term Γ
    ƛ_  : ∀ {Γ α β} → Term (Γ ▸ α) β → Term Γ (α ⇒ β)
    _·_ : ∀ {Γ α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β

  mutual
    -- Neutral forms
    data Neu : Rel (Ctx Type) Type where
      var : ∀ {Γ}     → Var Γ ⊆ Neu Γ
      _·_ : ∀ {Γ α β} → Neu Γ (α ⇒ β) → Nrm Γ α → Neu Γ β

    -- Normal forms
    data Nrm : Rel (Ctx Type) Type where
      ƛ_  : ∀ {Γ α β} → Nrm (Γ ▸ α) β → Nrm Γ (α ⇒ β)
      neu : ∀ {Γ}     → Neu Γ ● → Nrm Γ ●

  -- Convert Neutral / Normal forms back to Terms
  mutual
    termOfNeu : ∀ {Γ} → Neu Γ ⊆ Term Γ
    termOfNeu (var x)   = var x
    termOfNeu (ne · nm) = termOfNeu ne · termOfNrm nm

    termOfNrm : ∀ {Γ} → Nrm Γ ⊆ Term Γ
    termOfNrm (ƛ nm)   = ƛ (termOfNrm nm)
    termOfNrm (neu ne) = termOfNeu ne
