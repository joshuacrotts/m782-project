module Values where

open import Terms
open import Types

{- Values are terms that cannot step further.
 - Here we define the value judgments as being inductive types that receive a type, a term, and
 - produce a type. 
 - For example, vτ-true is a proof that true is a value of type 𝔹. -}
data Valτ : τ → Term → Set where
  vτ-true  : Valτ 𝔹 true
  vτ-false : Valτ 𝔹 false

  vτ-zero  : Valτ ℕ zero
  vτ-suc   : ∀ {v} → Valτ ℕ v → Valτ ℕ (suc v)

  vτ-cons  : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → Valτ (τ1 × τ2) (cons v1 v2)
