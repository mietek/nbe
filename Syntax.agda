-------------------------------------------------------------------------------
-- Syntax
-------------------------------------------------------------------------------

module Syntax where
  open import Ctx
  open import Vars

  infixr 1 _⇒_
  data Type : Set where
    ●   : Type
    _⇒_ : Type → Type → Type

  infixl 1 _·_
  data Term : Ctx Type → Type → Set where
    var : ∀ {Γ α  } → Var Γ α → Term Γ α
    ƛ_  : ∀ {Γ α β} → Term (Γ ▸ α) β → Term Γ (α ⇒ β)
    _·_ : ∀ {Γ α β} → Term Γ (α ⇒ β) → Term Γ α → Term Γ β

  mutual
    -- Neutral forms
    data Neu : Ctx Type → Type → Set where
      var : ∀ {Γ α  } → Var Γ α → Neu Γ α
      _·_ : ∀ {Γ α β} → Neu Γ (α ⇒ β) → Nrm Γ α → Neu Γ β

    -- Normal forms
    data Nrm : Ctx Type → Type → Set where
      ƛ_  : ∀ {Γ α β} → Nrm (Γ ▸ α) β → Nrm Γ (α ⇒ β)
      neu : ∀ {Γ}     → Neu Γ ● → Nrm Γ ●

  -- Convert Neutral / Normal forms back to Terms
  mutual
    termOfNeu : ∀ {Γ α} → Neu Γ α → Term Γ α
    termOfNeu (var x)   = var x
    termOfNeu (ne · nm) = termOfNeu ne · termOfNrm nm

    termOfNrm : ∀ {Γ α} → Nrm Γ α → Term Γ α
    termOfNrm (ƛ nm)   = ƛ (termOfNrm nm)
    termOfNrm (neu ne) = termOfNeu ne
