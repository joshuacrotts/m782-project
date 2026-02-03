module SystemF.Values where

open import SystemF.Terms
open import SystemF.Types

{- Values are terms that cannot step further.
 - Here we define the value judgments as being inductive types that receive a type, a term, and
 - produce a type. 
 - For example, vτ-true is a proof that true is a value of type 𝔹. -}
data Valτ : τ → Term → Set where
  vτ-true  : Valτ Bool true
  vτ-false : Valτ Bool false

  vτ-zero  : Valτ Nat zero
  vτ-suc   : ∀ {v} → Valτ Nat v → Valτ Nat (suc v)

  vτ-cons  : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → Valτ (τ1 × τ2) (cons v1 v2)
  
  vτ-lam   : ∀ {τ1 τ2 body} → Valτ (τ1 ⇒ τ2) (lam body)
  