module Env where
  open import Ctx
  open import Modalities
  open import Syntax
  open import Values

  _⇇_ : Ctx Type → Ctx Type → Set
  Δ ⇇ Γ = Box (Val Δ) Γ
