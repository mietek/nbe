-------------------------------------------------------------------------------
-- Normalization by Evaluation
-------------------------------------------------------------------------------

module NBE where
  open import Data.Function
    using (_∘_)

  open import Ctx
  open import Forcing
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  -- The following type aliases are intended to make the logical
  -- structure of the nbe algorithm more evident from the type
  -- signatures.

  _⊢_  = Term
  _⊢↓_ = Nrm
  _⊢↑_ = Neu
  _⊩_  = Forces
  _⊩*_ = ForcesCtx

  -- Γ entails α in the Kripke model if any world Δ forces α whenever
  -- Δ forces Γ
  _⊧_ : Ctx Type → Type → Set
  Γ ⊧ α = ∀ {Δ} → Δ ⊩* Γ → Δ ⊩ α

  -- The meaning function can be viewed as the constructive content of
  -- the soundness theorem for intuitionistic propositional logic with
  -- respect to entailment in a Kripke model.
  soundness : ∀ {Γ α} → Γ ⊢ α → Γ ⊧ α
  soundness (var x)   ρ = lookup ρ x
  soundness (ƛ e)     ρ = λ Δ≤Σ x → soundness e (wknCtx Δ≤Σ ρ ▸ x)
  soundness (e₁ · e₂) ρ = (soundness e₁ ρ) ≤-refl (soundness e₂ ρ)

  mutual
    -- Quote a semantic value in the Kripke model to a normal term
    ⌜_⌝ : ∀ {Γ α} → Γ ⊩ α → Γ ⊢↓ α
    ⌜_⌝ {α = ●}     x = neu x
    ⌜_⌝ {α = α ⇒ β} f = ƛ ⌜ f refl-incr ⌞ var vz ⌟ ⌝

    -- Unquote a neutral term to a semantic value in the Kripke model
    ⌞_⌟ : ∀ {Γ α} → Γ ⊢↑ α → Γ ⊩ α
    ⌞_⌟ {α = ●}     x = x
    ⌞_⌟ {α = α ⇒ β} f = λ Δ≤Σ x → ⌞ wknNeu Δ≤Σ f · ⌜ x ⌝ ⌟

  -- The identity substitution
  id-⊩* : ∀ {Γ} → Γ ⊩* Γ
  id-⊩* {Γ} = tabulate var-⊩
    where
      var-⊩ : {α : Type} → Var Γ α → Γ ⊩ α
      var-⊩ {●}     = var
      var-⊩ {α ⇒ β} = λ f ρ x → ⌞ var (lookup ρ f) · ⌜ x ⌝ ⌟

  -- The inverse of the meaning function can be viewed as the
  -- constructive content of the completeness theorem for
  -- intuitionistic propositional logic with respect to entailment in
  -- a Kripke model.
  completeness : ∀ {Γ α} → Γ ⊧ α → Γ ⊢ α
  completeness ρ = termOfNrm ⌜ ρ id-⊩* ⌝

  -- Normalization by evaluation, i.e., reduction-free normalization.
  -- Maps a term to its meaning in the Kripke model then extracts the
  -- meaning into a canonical term (β-normal, η-long).
  nbe : ∀ {Γ α} → Γ ⊢ α → Γ ⊢ α
  nbe = completeness ∘ soundness
