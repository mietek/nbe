module Correctness.Soundness where
  open import Data.Function
    using    ( _∘_
             ; id )
  open import Data.Product
    hiding   ( map )
  open import Data.Unit
    using    ( ⊤
             ; tt )
  open import Relation.Binary
    using    ( Symmetric
             ; Transitive )
  open import Relation.Binary.PropositionalEquality
    hiding   ( subst )
    renaming ( refl  to ≡-refl
             ; sym   to ≡-sym
             ; trans to ≡-trans )

  open import Ctx
  open import Modalities
  open import Model
  open import NBE
  open import Predicates
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  open import Correctness.Convertability
  open import Correctness.Substitution

  -- The family of partial equivalence relations (PERs).  This gives
  -- us a PER model at each context and type.  This cannot be defined
  -- as an inductive family because it is not strictly positive in the
  -- α ⇒ β case.
  _∼_ : ∀ {Γ α} → EndoRel (Val Γ α)
  _∼_ {Γ = Γ} {α = ●}     x₁ x₂ = ⌜ x₁ ⌝ ≡ ⌜ x₂ ⌝
  _∼_ {Γ = Γ} {α = α ⇒ β} f₁ f₂ = ∀ {Δ x₁ x₂} (Δ⊇Γ : Δ ⊇ Γ) → x₁ ∼ x₂ → f₁ Δ⊇Γ x₁ ∼ f₂ Δ⊇Γ x₂

  mutual
    -- Related values in the Kripke model have identical quotations.
    ∼≡↓ : ∀ {Γ α} {v₁ v₂ : Val Γ α} → v₁ ∼ v₂ → ⌜ v₁ ⌝ ≡ ⌜ v₂ ⌝
    ∼≡↓ {α = ●}     ≡-refl = ≡-refl
    ∼≡↓ {α = α ⇒ β} f      = cong ƛ_ (∼≡↓ (f ▸-step (≡↑∼ ≡-refl)))

    -- Identical neutral terms have related unquotations in the Kripke model.
    ≡↑∼ : ∀ {Γ α} {ne₁ ne₂ : Neu Γ α} → ne₁ ≡ ne₂ → ⌞ ne₁ ⌟ ∼ ⌞ ne₂ ⌟
    ≡↑∼ {α = ●}     ≡-refl = ≡-refl
    ≡↑∼ {α = α ⇒ β} ≡-refl = λ Γ≤Δ → ≡↑∼ ∘ cong (_·_ (wknNeu* Γ≤Δ _)) ∘ ∼≡↓

  -- _∼_ is reflexive (for variables) at all contexts and types.
  ∼-refl-var : ∀ {Γ α} (x : Var Γ α) → varToVal x ∼ varToVal x
  ∼-refl-var {α = ●}     x = ≡-refl
  ∼-refl-var {α = α ⇒ β} x = λ Γ≤Δ → ≡↑∼ ∘ cong (_·_ (var (lookup Γ≤Δ x))) ∘ ∼≡↓

  -- _∼_ is symmetric at all contexts and types.
  ∼-sym : ∀ {Γ α} → Symmetric (_∼_ {Γ = Γ} {α = α})
  ∼-sym {α = ●}     p = ≡-sym p
  ∼-sym {α = α ⇒ β} p = λ Γ≤Δ → ∼-sym ∘ p Γ≤Δ ∘ ∼-sym

  -- _∼_ is transitive at all contexts and types.
  ∼-trans : ∀ {Γ α} → Transitive (_∼_ {Γ = Γ} {α = α})
  ∼-trans {α = ●}     p₁ p₂ = ≡-trans p₁ p₂
  ∼-trans {α = α ⇒ β} p₁ p₂ = λ Γ≤Δ x₁∼x₂ → ∼-trans (p₁ Γ≤Δ x₁∼x₂) (p₂ Γ≤Δ (∼-trans (∼-sym x₁∼x₂) x₁∼x₂))

  -- Weakening preserves _∼_
  ∼-weaken : ∀ {Γ Δ α} {v₁ v₂ : Val Δ α}
           → (Γ⊇Δ : Γ ⊇ Δ)
           → v₁ ∼ v₂
           → wknVal* Γ⊇Δ v₁ ∼ wknVal* Γ⊇Δ v₂
  ∼-weaken {α = ●}     Γ⊇Δ ≡-refl = ≡-refl
  ∼-weaken {α = α ⇒ β} Γ⊇Δ f₁∼f₂  = λ Ψ⊇Γ → f₁∼f₂ (⊇-trans Ψ⊇Γ Γ⊇Δ)

  _≈_ : ∀ {Γ Δ} → EndoRel (Env Γ Δ)
  ε             ≈ ε             = ⊤
  (ρ₁ ▸ val-α₁) ≈ (ρ₂ ▸ val-α₂) = val-α₁ ∼ val-α₂ × ρ₁ ≈ ρ₂

  -- Lookup preserves ≈ wrt to ∼
  ∼-lookup : ∀ {Γ Δ α} (ρ₁ ρ₂ : Env Γ Δ)
      → ρ₁ ≈ ρ₂
      → (x : Var Δ α)
      → lookup ρ₁ x ∼ lookup ρ₂ x
  ∼-lookup ε         _         _               ()
  ∼-lookup (ρ₁ ▸ v₁) (ρ₂ ▸ v₂) (v₁∼v₂ , ρ₁≈ρ₂) (here  ≡-refl) = v₁∼v₂
  ∼-lookup (ρ₁ ▸ v₁) (ρ₂ ▸ v₂) (v₁∼v₂ , ρ₁≈ρ₂) (there x)      = ∼-lookup ρ₁ ρ₂ ρ₁≈ρ₂ x

  postulate
    ≈-refl-idEnv : ∀ {Γ}   → idEnv {Γ} ≈ idEnv {Γ}

    ≈-sym        : ∀ {Γ Δ} (ρ₁ ρ₂ : Env Γ Δ) → ρ₁ ≈ ρ₂ → ρ₂ ≈ ρ₁

    ≈-trans      : ∀ {Γ Δ} (ρ₁ ρ₂ ρ₃ : Env Γ Δ) → ρ₁ ≈ ρ₂ → ρ₂ ≈ ρ₃ → ρ₁ ≈ ρ₃

  -- Weakening preserves _≈_
  ≈-weaken : ∀ {Γ Δ Ψ}
           → (ρ₁ ρ₂ : Env Γ Δ)
           → (Ψ⊇Γ : Ψ ⊇ Γ)
           → ρ₁ ≈ ρ₂
           → wknEnv* Ψ⊇Γ ρ₁ ≈ wknEnv* Ψ⊇Γ ρ₂
  ≈-weaken ε         ε         _   _               = tt
  ≈-weaken (ρ₁ ▸ v₁) (ρ₂ ▸ v₂) Ψ⊇Γ (v₁∼v₂ , ρ₁≈ρ₂) = ∼-weaken Ψ⊇Γ v₁∼v₂ , ≈-weaken ρ₁ ρ₂ Ψ⊇Γ ρ₁≈ρ₂

  logRel-lemma : ∀ {Γ Δ α} {ρ₁ ρ₂ : Env Γ Δ}
               → (e : Term Δ α)
               → ρ₁ ≈ ρ₂
               → soundness e ρ₁ ∼ soundness e ρ₂
  logRel-lemma                     (var x)   ρ₁≈ρ₂ = ∼-lookup _ _ ρ₁≈ρ₂ x
  logRel-lemma {ρ₁ = ρ₁} {ρ₂ = ρ₂} (ƛ e)     ρ₁≈ρ₂ = λ Ψ⊇Γ x₁∼x₂ → logRel-lemma e (x₁∼x₂ , ≈-weaken ρ₁ ρ₂ Ψ⊇Γ ρ₁≈ρ₂)
  logRel-lemma                     (e₁ · e₂) ρ₁≈ρ₂ = logRel-lemma e₁ ρ₁≈ρ₂ ⊇-refl (logRel-lemma e₂ ρ₁≈ρ₂)

  logRel : ∀ {Γ Δ α} {ρ₁ ρ₂ : Env Γ Δ} {e₁ e₂ : Term Δ α}
         → ρ₁ ≈ ρ₂
         → e₁ ≃ e₂
         → soundness e₁ ρ₁ ∼ soundness e₂ ρ₂
  logRel                     ρ₁≈ρ₂ (≃-β e₁ e₂)                   = {!!}
  logRel                     ρ₁≈ρ₂ (≃-ξ e₁≃e₂)                   = {!!}
  logRel                     ρ₁≈ρ₂ (≃-η e₁)                      = λ Δ⊇Γ x₁∼x₂ → {!!}
  logRel                     ρ₁≈ρ₂ (≃-ρ e₂)                      = logRel-lemma e₂ ρ₁≈ρ₂
  logRel                     ρ₁≈ρ₂ (≃-μ f x₁≃x₂)                 = logRel-lemma f ρ₁≈ρ₂ ⊇-refl (logRel ρ₁≈ρ₂ x₁≃x₂)
  logRel                     ρ₁≈ρ₂ (≃-ν x f₁≃f₂)                 = logRel ρ₁≈ρ₂ f₁≃f₂ ⊇-refl (logRel-lemma x ρ₁≈ρ₂)
  logRel {ρ₁ = ρ₁} {ρ₂ = ρ₂} ρ₁≈ρ₂ (≃-σ e₁≃e₂)                   = ∼-sym (logRel (≈-sym ρ₁ ρ₂ ρ₁≈ρ₂) e₁≃e₂)
  logRel {ρ₁ = ρ₁} {ρ₂ = ρ₂} ρ₁≈ρ₂ (≃-τ e₁≃e₂ e₂≃e₃)             = ∼-trans (logRel ρ₁≈ρ₂ e₁≃e₂) (logRel (≈-trans ρ₂ ρ₁ ρ₂ (≈-sym ρ₁ ρ₂ ρ₁≈ρ₂) ρ₁≈ρ₂) e₂≃e₃)

  nbe-soundness : ∀ {Γ α} {e₁ e₂ : Term Γ α} → e₁ ≃ e₂ → nbe e₁ ≡ nbe e₂
  nbe-soundness {Γ = Γ} = cong termOfNrm ∘ ∼≡↓ ∘ logRel (≈-refl-idEnv {Γ = Γ})
