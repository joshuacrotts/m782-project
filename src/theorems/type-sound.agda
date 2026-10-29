module theorems.type-sound where

open import SystemF.definitions
open import theorems.preservation using (preservation)

-- Evaluation in zero or more small steps.
infix 4 _↦*_

data _↦*_ : Term → Term → Set where
  ms-refl : ∀ {e} → e ↦* e
  ms-step : ∀ {e e' e''} → e ↦ e' → e' ↦* e'' → e ↦* e''

-- Every term reachable from a well-typed closed term has the same type.
-- Proof by induction on the evaluation derivation.
type-safety : ∀ {e e' τ} →
                (• ⨟ ∘ ⊢ e ⦂ τ) →
                (e ↦* e') →
                (• ⨟ ∘ ⊢ e' ⦂ τ)
type-safety te ms-refl = te
type-safety te (ms-step step steps) =
  type-safety (preservation te step) steps


-- If a well-typed closed program evaluates to a value, that value has
-- the initial program's type. The value witness need not assume that type.
type-sound : ∀ {e v τ τv} →
             (• ⨟ ∘ ⊢ e ⦂ τ) →
             (e ↦* v) →
             Valτ τv v →
             (• ⨟ ∘ ⊢ v ⦂ τ)
type-sound te steps _ = type-safety te steps
