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
  -- structure of the nbe algorithm more apparent from the type
  -- signatures.
  _⊢_  = Term
  _⊢↓_ = Nrm
  _⊢↑_ = Neu
  _⊩_  = Forces
  _⊩*_ = ForcesCtx

  -- Γ entails α in the Kripke model if any world (context) Δ forces α
  -- whenever Δ forces Γ.
  _⊧_ : Ctx Type → Type → Set
  Γ ⊧ α = ∀ {Δ} → Δ ⊩* Γ → Δ ⊩ α

  -- The meaning function can be viewed as the computational content
  -- of the soundness theorem for intuitionistic propositional logic
  -- with respect to entailment in a Kripke model.
  soundness : ∀ {Γ α} → Γ ⊢ α → Γ ⊧ α
  soundness (var x)   σ = [ σ ] x
  soundness (ƛ e)     σ = λ Δ≤Σ x → soundness e (wknSub* Δ≤Σ σ ▸ x)
  soundness (e₁ · e₂) σ = (soundness e₁ σ) ≤-refl (soundness e₂ σ)

  mutual
    -- Quote (reify) a semantic value in the Kripke model to a normal
    -- form.
    ⌜_⌝ : ∀ {Γ α} → Γ ⊩ α → Γ ⊢↓ α
    ⌜_⌝ {α = ●}     x = neu x
    ⌜_⌝ {α = α ⇒ β} f = ƛ ⌜ f ▸-step ⌞ var vz ⌟ ⌝

    -- Unquote (reflect) a neutral form to a semantic value in the
    -- Kripke model.
    ⌞_⌟ : ∀ {Γ α} → Γ ⊢↑ α → Γ ⊩ α
    ⌞_⌟ {α = ●}     x = x
    ⌞_⌟ {α = α ⇒ β} f = λ Δ≤Σ x → ⌞ wknNeu* Δ≤Σ f · ⌜ x ⌝ ⌟

  -- The identity substitution.
  id-⊩* : ∀ {Γ} → Γ ⊩* Γ
  id-⊩* {Γ} = tabulate var-⊩
    where
      var-⊩ : ∀ {α} → Var Γ α → Γ ⊩ α
      var-⊩ {α = ●}     x = var x
      var-⊩ {α = α ⇒ β} f = λ ρ x → ⌞ var (lookup ρ f) · ⌜ x ⌝ ⌟

  -- The inverse of the meaning function can be viewed as the
  -- computational content of the completeness theorem for
  -- intuitionistic propositional logic with respect to entailment in
  -- a Kripke model.
  completeness : ∀ {Γ α} → Γ ⊧ α → Γ ⊢ α
  completeness γ = termOfNrm ⌜ γ id-⊩* ⌝

  -- Normalization by evaluation, i.e., reduction-free normalization.
  -- Maps a term to its meaning in the Kripke model then extracts the
  -- meaning into a canonical (β-normal, η-long) term.
  nbe : ∀ {Γ α} → Γ ⊢ α → Γ ⊢ α
  nbe = completeness ∘ soundness
