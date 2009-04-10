module Ctx where

  -- Snoc Lists
  data Ctx (α : Set) : Set where
    ε   : Ctx α
    _▸_ : Ctx α → α → Ctx α
