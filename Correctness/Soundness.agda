module Correctness.Soundness where
  open import Data.Function
    using    ( _∘_ )
  open import Data.Product
  open import Data.Unit
    using    ( ⊤
             ; tt )
  open import Relation.Binary
    using    ( Rel
             ; Symmetric
             ; Transitive )
  open import Relation.Binary.PropositionalEquality
    renaming ( refl  to ≡-refl
             ; sym   to ≡-sym
             ; trans to ≡-trans )

  open import Ctx
  open import Forcing
  open import Modalities
  open import NBE
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  open import Correctness.Convertability

  -- The family of partial equivalence relations (PERs).  This gives
  -- us a PER model at each context and type.  This cannot be defined
  -- as an inductive family because it is not strictly positive in the
  -- α ⇒ β case.
  _∼_ : ∀ {Γ α} → EndoRel (Val Γ α)
  _∼_ {Γ = Γ} {α = ●}     x₁ x₂ = ⌜ x₁ ⌝ ≡ ⌜ x₂ ⌝
  _∼_ {Γ = Γ} {α = α ⇒ β} f₁ f₂ = ∀ {Δ x₁ x₂} (Γ≤Δ : Γ ≤ Δ) → x₁ ∼ x₂ → f₁ Γ≤Δ x₁ ∼ f₂ Γ≤Δ x₂

  mutual
    -- Related values in the Kripke model have identical quotations.
    ~≡↓ : ∀ {Γ α} {v₁ v₂ : Val Γ α} → v₁ ∼ v₂ → ⌜ v₁ ⌝ ≡ ⌜ v₂ ⌝
    ~≡↓ {α = ●}     ≡-refl = ≡-refl
    ~≡↓ {α = α ⇒ β} f      = cong ƛ_ (~≡↓ (f ▸-step (≡↑~ ≡-refl)))

    -- Identical neutral terms have related unquotations in the Kripke model.
    ≡↑~ : ∀ {Γ α} {ne₁ ne₂ : Neu Γ α} → ne₁ ≡ ne₂ → ⌞ ne₁ ⌟ ∼ ⌞ ne₂ ⌟
    ≡↑~ {α = ●}     ≡-refl = ≡-refl
    ≡↑~ {α = α ⇒ β} ≡-refl = λ Γ≤Δ → ≡↑~ ∘ cong (_·_ (wknNeu* Γ≤Δ _)) ∘ ~≡↓

  -- _∼_ is reflexive (for variables) at all contexts and types.
  ∼-refl : ∀ {Γ : Ctx Type} {α : Type} (x : Var Γ α) → ∋→⊩ x ∼ ∋→⊩ x
  ∼-refl {α = ●}     x = ≡-refl
  ∼-refl {α = α ⇒ β} x = λ Γ≤Δ → ≡↑~ ∘ cong (_·_ (var (lookup Γ≤Δ x))) ∘ ~≡↓

  -- _∼_ is symmetric at all contexts and types.
  ∼-sym : ∀ {Γ α} → Symmetric (_∼_ {Γ = Γ} {α = α})
  ∼-sym {α = ●}     p = ≡-sym p
  ∼-sym {α = α ⇒ β} p = λ Γ≤Δ → ∼-sym ∘ p Γ≤Δ ∘ ∼-sym

  -- _∼_ is transitive at all contexts and types.
  ∼-trans : ∀ {Γ α} → Transitive (_∼_ {Γ = Γ} {α = α})
  ∼-trans {α = ●}     p₁ p₂ = ≡-trans p₁ p₂
  ∼-trans {α = α ⇒ β} p₁ p₂ = λ Γ≤Δ x₁∼x₂ → ∼-trans (p₁ Γ≤Δ x₁∼x₂) (p₂ Γ≤Δ (∼-trans (∼-sym x₁∼x₂) x₁∼x₂))

  -- The PER ∼ extended to environments.  Could use modalities for
  -- this too although it might make the other stuff harder to prove.
  _≈_ : ∀ {Γ Δ} → EndoRel (Env Γ Δ)
  ε         ≈ ε         = ⊤
  (ρ₁ ▸ v₁) ≈ (ρ₂ ▸ v₂) = v₁ ∼ v₂ × ρ₁ ≈ ρ₂

  postulate
    -- The identity environment is related to itself.
    ≈-refl : ∀ {Γ} → ⊩*-id {Γ} ≈ ⊩*-id {Γ}

    lemma : ∀ {Γ α} (e : Term Γ α) {ρ₁ ρ₂ : Env Γ Γ}
          → ρ₁ ≈ ρ₂
          → soundness e ρ₁ ∼ soundness e ρ₂

    logRel : ∀ {Γ α} {e₁ e₂ : Term Γ α} {ρ₁ ρ₂ : Env Γ Γ}
           → ρ₁ ≈ ρ₂
           → e₁ ≃ e₂
           → soundness e₁ ρ₁ ∼ soundness e₂ ρ₂

  nbe-soundness : ∀ {Γ α} {e₁ e₂ : Term Γ α} → e₁ ≃ e₂ → nbe e₁ ≡ nbe e₂
  nbe-soundness {Γ} = cong termOfNrm ∘ ~≡↓ ∘ logRel (≈-refl {Γ})
