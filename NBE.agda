-------------------------------------------------------------------------------
-- Normalization by Evaluation
-------------------------------------------------------------------------------

module NBE where
  open import Data.Function
    using (_∘_)

  open import Ctx
  open import Modalities
  open import Model
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

-------------------------------------------------------------------------------
-- Abbreviations

  -- The following type aliases are intended to make the logical
  -- structure of the nbe algorithm more apparent from the type
  -- signatures.
  _⊩*_ = Env
  _⊧_  = Models
  _↑_  = Neu
  _↓_  = Nrm
  _⊢_  = Term
  _∋_  = Var {Type}
  _⊩_  = Val

-------------------------------------------------------------------------------
-- Soundness (Easy Part)

  -- The meaning function can be viewed as the computational content
  -- of the soundness theorem for deduction in intuitionistic
  -- propositional logic with respect to entailment in a Kripke model.
  soundness : ∀ {Γ α} → Γ ⊢ α → Γ ⊧ α
  soundness (var x)   ρ = lookup ρ x
  soundness (ƛ e)     ρ = λ Σ⊇Δ v → soundness e (wknEnv* Σ⊇Δ ρ ▸ v)
  soundness (e₁ · e₂) ρ = (soundness e₁ ρ) ⊇-refl (soundness e₂ ρ)

-------------------------------------------------------------------------------
-- Completeness (Hard Part)

  mutual
    -- Quote (reify) a semantic value in the Kripke model to a normal
    -- form.
    ⌜_⌝ : ∀ {Γ α} → Γ ⊩ α → Γ ↓ α
    ⌜_⌝ {α = ●}     x = neu x
    ⌜_⌝ {α = α ⇒ β} f = ƛ ⌜ f ▸-step ⌞ var vz ⌟ ⌝

    -- Unquote (reflect) a neutral form to a semantic value in the
    -- Kripke model.
    ⌞_⌟ : ∀ {Γ α} → Γ ↑ α → Γ ⊩ α
    ⌞_⌟ {α = ●}     x = x
    ⌞_⌟ {α = α ⇒ β} f = λ Δ⊇Γ x → ⌞ wknNeu* Δ⊇Γ f · ⌜ x ⌝ ⌟

  -- Convert a variable to a value in the model.
  varToVal : ∀ {Γ α} → Γ ∋ α → Γ ⊩ α
  varToVal {α = ●}     x = var x
  varToVal {α = α ⇒ β} f = λ Δ⊇Γ x → ⌞ var (lookup Δ⊇Γ f) · ⌜ x ⌝ ⌟

  -- The identity environment.
  idEnv : ∀ {Γ} → Γ ⊩* Γ
  idEnv = tabulate varToVal

  -- The inverse of the meaning function can be viewed as the
  -- computational content of the completeness theorem for deduction
  -- in intuitionistic propositional logic with respect to entailment
  -- in a Kripke model.
  completeness : ∀ {Γ α} → Γ ⊧ α → Γ ⊢ α
  completeness v = termOfNrm ⌜ v idEnv ⌝

-------------------------------------------------------------------------------
-- Normalization by Evaluation (a.k.a. Reduction-free normalization)

  -- Normalization by evaluation, i.e., reduction-free normalization.
  -- Maps a term to its meaning in the Kripke model then quotes the
  -- meaning into a canonical (β-normal, η-long) term.
  nbe : ∀ {Γ α} → Γ ⊢ α → Γ ⊢ α
  nbe = completeness ∘ soundness
