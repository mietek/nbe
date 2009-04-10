module Env where
  open import Ctx
  open import Modalities
  open import Syntax
  open import Values

  Env : Ctx Type → Ctx Type → Set
  Env Δ Γ = Box (Val Δ) Γ
