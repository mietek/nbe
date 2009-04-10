module NBE where
  open import Ctx
  open import Env
  open import Modalities
  open import Subsumption
  open import Syntax
  open import Values
  open import Vars
  open import Weaken

  _⊢_  = Term
  _⊢↓_ = Nrm
  _⊢↑_ = Neu
  _⇇_  = Env
  _⊧_  = Val

  ⟦_⟧ : ∀ {Γ Δ α} → Γ ⊢ α → Δ ⇇ Γ → Δ ⊧ α
  ⟦ var x   ⟧ γ = lookup γ x
  ⟦ ƛ e     ⟧ γ = λ ρ v → ⟦ e ⟧ (map (wknVal ρ) γ ▸ v)
  ⟦ e₁ · e₂ ⟧ γ = ⟦ e₁ ⟧ γ ≤-refl (⟦ e₂ ⟧ γ)

  mutual
    ⌜_⌝ : ∀ {Γ α} → Γ ⊧ α → Γ ⊢↓ α
    ⌜_⌝ {α = ●}     ne = neu ne
    ⌜_⌝ {α = α ⇒ β} f  = ƛ ⌜ f (▸-incr ≤-refl) ⌞ var vz ⌟ ⌝

    ⌞_⌟ : ∀ {Γ α} → Γ ⊢↑ α → Γ ⊧ α
    ⌞_⌟ {α = ●}     ne = ne
    ⌞_⌟ {α = α ⇒ β} f  = λ ρ x → ⌞ wknNeu ρ f · ⌜ x ⌝ ⌟

  nbe : ∀ {α} → ε ⊢ α → ε ⊢ α
  nbe e = termOfNrm ⌜ ⟦ e ⟧ ε ⌝
