module Correctness.Soundness where
  open import Data.Function
    using (id; _∘_)
  open import Data.Product
  open import Data.Unit
    hiding (_≤_)
  open import Relation.Binary.PropositionalEquality
    renaming (subst to ≡-subst)
  open ≡-Reasoning

  open import Ctx
  open import Forcing
  open import Modalities
  open import NBE
  open import Subsumption
  open import Syntax
  open import Vars
  open import Weaken

  open import Correctness.Convertability
  open import Correctness.Substitution

  module ModalitiesEnv where
    -- FIXME: Find a way to generalize this stuff so we only need one
    -- version of Box and Dia.  Maybe we can parameterize the
    -- modalities module?
    data BoxEnv {Γ} (φ : ∀ {α} → Forces Γ α → Set) : ∀ {Δ} → ForcesCtx Γ Δ → Set where
      ε   : BoxEnv φ ε
      _▸_ : ∀ {Δ α} {ρ : ForcesCtx Γ Δ} {v : Forces Γ α} → BoxEnv φ ρ → φ v → BoxEnv φ (ρ ▸ v)

    data DiaEnv {Γ} {α} (φ : Forces Γ α → Set) : ∀ {Δ} → ForcesCtx Γ Δ → Set where
      here  : ∀ {Δ}   {ρ : ForcesCtx Γ Δ} {v : Forces Γ α} → φ v → DiaEnv φ (ρ ▸ v)
      there : ∀ {Δ β} {ρ : ForcesCtx Γ Δ} {v : Forces Γ β} → DiaEnv φ ρ → DiaEnv φ (ρ ▸ v)

    _≈_ : ∀ {Γ Δ} → ForcesCtx Γ Δ → ForcesCtx Γ Δ → Set
    ρ₁ ≈ ρ₂ = BoxEnv (λ v → DiaEnv (_≡_ v) ρ₂) ρ₁

    lookupEnv : ∀ {Γ Δ α} {φ : ∀ {β} → Forces Γ β → Set} {ρ : ForcesCtx Γ Δ} {v : Forces Γ α}
              → BoxEnv φ ρ
              → DiaEnv (_≡_ v) ρ
              → φ v
    lookupEnv {ρ = ε} _           ()
    lookupEnv         (_   ▸ φ-v) (here  refl) = φ-v
    lookupEnv         (φ-ρ ▸ _  ) (there p)    = lookupEnv φ-ρ p

    tabulateEnv : ∀ {Γ Δ} {φ : ∀ {α} → Forces Γ α → Set} {ρ : ForcesCtx Γ Δ}
                → (∀ {α} {v : Forces Γ α} → DiaEnv (_≡_ v) ρ → φ v) → BoxEnv φ ρ
    tabulateEnv {ρ = ε}     f = ε
    tabulateEnv {ρ = _ ▸ _} f = tabulateEnv (f ∘ there) ▸ f (here refl)

  open ModalitiesEnv

  _∼_ : ∀ {Γ α} → Forces Γ α → Forces Γ α → Set
  _∼_ {Γ = Γ} {α = ●}     x₁ x₂ = ⌜ x₁ ⌝ ≡ ⌜ x₂ ⌝
  _∼_ {Γ = Γ} {α = α ⇒ β} f₁ f₂ = ∀ {Δ x₁ x₂} (Γ≤Δ : Γ ≤ Δ) → x₁ ∼ x₂ → f₁ Γ≤Δ x₁ ∼ f₂ Γ≤Δ x₂

--   _≈_ : ∀ {Γ Δ} → ForcesCtx Γ Δ → ForcesCtx Γ Δ → Set
--   ε         ≈ ε         = ⊤
--   (ρ₁ ▸ v₁) ≈ (ρ₂ ▸ v₂) = ρ₁ ≈ ρ₂ × v₁ ∼ v₂

  mutual
    lemma₁ : ∀ {Γ α} {d₁ d₂ : Forces Γ α} → d₁ ∼ d₂ → ⌜ d₁ ⌝ ≡ ⌜ d₂ ⌝
    lemma₁ {α = ●}     d₁≡d₂ = d₁≡d₂
    lemma₁ {α = α ⇒ β} d₁~d₂ = cong ƛ_ (lemma₁ (d₁~d₂ ▸-step (lemma₂ refl)))

    lemma₂ : ∀ {Γ α} {ne₁ ne₂ : Neu Γ α} → ne₁ ≡ ne₂ → ⌞ ne₁ ⌟ ∼ ⌞ ne₂ ⌟
    lemma₂ {α = ●}                 refl = refl
    lemma₂ {α = α ⇒ β} {ne₂ = ne₂} refl = λ Γ≤Δ x₁~x₂ → lemma₂ (cong (λ x → wknNeu* Γ≤Δ ne₂ · x) (lemma₁ x₁~x₂))

  ∼-refl : ∀ (Γ : Ctx Type) (α : Type) (x : Var Γ α) → var-⊩ x ∼ var-⊩ x
  ∼-refl Γ ●       _ = refl
  ∼-refl Γ (α ⇒ β) x = λ Γ≤Δ x₁∼x₂ → lemma₂ (cong (λ x′ → var (lookup Γ≤Δ x) · x′) (lemma₁ x₁∼x₂))

  ≈-refl : ∀ Γ → id-⊩* {Γ} ≈ id-⊩* {Γ}
  ≈-refl Γ = tabulateEnv id

--   ≈-refl : ∀ Γ → id-⊩* {Γ} ≈ id-⊩* {Γ}
--   ≈-refl ε       = tt
--   ≈-refl (Γ ▸ α) = {!!} , ∼-refl (Γ ▸ α) α vz

  lemma₃ : ∀ {Γ α} {e₁ e₂ : Term Γ α} {ρ₁ ρ₂ : ForcesCtx Γ Γ}
         → ρ₁ ≈ ρ₂
         → e₁ ≃ e₂
         → soundness e₁ ρ₁ ∼ soundness e₂ ρ₂
  lemma₃ = {!!}

  nbe-soundness : ∀ {Γ α} {e₁ e₂ : Term Γ α} → e₁ ≃ e₂ → nbe e₁ ≡ nbe e₂
  nbe-soundness {Γ} = cong termOfNrm ∘ lemma₁ ∘ lemma₃ (≈-refl Γ)
