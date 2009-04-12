-------------------------------------------------------------------------------
-- Modalities
-------------------------------------------------------------------------------

-- The code in the following module is used primarily to make
-- weakening and environments easy to deal with.

-- See Peter Morris's thesis for info on Box, Dia, fill, find, etc.

module Modalities where
  open import Data.Function
    using (_∘_)
  open import Data.Product
    hiding (map)
  open import Relation.Binary.PropositionalEquality

  open import Ctx

  data Box {χ : Set} (ϕ : χ → Set) : Ctx χ → Set where
    ε   : Box ϕ ε
    _▸_ : ∀ {Γ α} → Box ϕ Γ → ϕ α → Box ϕ (Γ ▸ α)

  fill : {χ : Set} {ϕ : χ → Set} (Γ : Ctx χ) → ((α : χ) → ϕ α) → Box ϕ Γ
  fill ε       f = ε
  fill (Γ ▸ α) f = fill Γ f ▸ f α

  -- Already defined in Relation.Unary, but χ is not implicit, making
  -- it slightly more annoying to work with than this version.
  _⊆_ : {χ : Set} → (χ → Set) → (χ → Set) → Set
  P ⊆ Q = ∀ {α} → P α → Q α

  map : {χ : Set} {ϕ φ : χ → Set} → ϕ ⊆ φ → Box ϕ ⊆ Box φ
  map f ε       = ε
  map f (Γ ▸ α) = map f Γ ▸ f α

  data Dia {χ : Set} (ϕ : χ → Set) : Ctx χ → Set where
    here  : ∀ {Γ α} → ϕ α → Dia ϕ (Γ ▸ α)
    there : ∀ {Γ α} → Dia ϕ Γ → Dia ϕ (Γ ▸ α)

  find : {χ : Set} {ϕ : χ → Set} (Γ : Ctx χ) → Dia ϕ Γ → Σ χ (λ α → ϕ α)
  find .(Γ ▸ α) (here  {Γ} {α} p) = α , p
  find .(Γ ▸ α) (there {Γ} {α} p) = find Γ p

  lookup : {χ : Set} {ϕ : χ → Set} {α : χ} {Γ : Ctx χ}
         → Box ϕ Γ → Dia (_≡_ α) Γ → ϕ α
  lookup {Γ = ε} _           ()
  lookup         (_   ▸ ϕ-α) (here  refl) = ϕ-α
  lookup         (ϕ-Γ ▸ _  ) (there ps)   = lookup ϕ-Γ ps

  tabulate : {χ : Set} {ϕ : χ → Set} {Γ : Ctx χ}
           → ({α : χ} → Dia (_≡_ α) Γ → ϕ α) → Box ϕ Γ
  tabulate {Γ = ε}     f = ε
  tabulate {Γ = Γ ▸ α} f = tabulate (f ∘ there) ▸ f (here refl)
