module NBE where
  open import Ctx
  open import Forcing
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  _⊢_  = Term
  _⊢↓_ = Nrm
  _⊢↑_ = Neu
  _⊩_  = Forces
  _⊩*_ = ForcesCtx

  _⊧_ : Ctx Type → Type → Set
  Γ ⊧ α = ∀ {w} → w ⊩* Γ → w ⊩ α

  ⟦_⟧ : ∀ {Γ α} → Γ ⊢ α → Γ ⊧ α
  ⟦ var x   ⟧ ρ = lookup ρ x
  ⟦ ƛ e     ⟧ ρ = λ w≤Δ x → ⟦ e ⟧ (wknCtx w≤Δ ρ ▸ x)
  ⟦ e₁ · e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ≤-refl (⟦ e₂ ⟧ ρ)

  mutual
    ⌜_⌝ : ∀ {Γ α} → Γ ⊩ α → Γ ⊢↓ α
    ⌜_⌝ {α = ●}     x = neu x
    ⌜_⌝ {α = α ⇒ β} f = ƛ ⌜ f ≤-incr ⌞ var vz ⌟ ⌝

    ⌞_⌟ : ∀ {Γ α} → Γ ⊢↑ α → Γ ⊩ α
    ⌞_⌟ {α = ●}     x = x
    ⌞_⌟ {α = α ⇒ β} f = λ w≤Δ x → ⌞ wknNeu w≤Δ f · ⌜ x ⌝ ⌟

  nbe : ∀ {α} → ε ⊢ α → ε ⊢ α
  nbe e = termOfNrm ⌜ ⟦ e ⟧ ε ⌝
