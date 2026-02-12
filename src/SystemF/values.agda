module SystemF.values where

open import SystemF.terms
open import SystemF.types

{- Values are terms that cannot step further.
 - Here we define the value judgments as being inductive types that receive a type, a term, and
 - produce a type. 
 - For example, vτ-true is a proof that true is a value of type 𝔹. -}
data Valτ : τ → Term → Set where
  vτ-true  : Valτ Bool True
  vτ-false : Valτ Bool False

  vτ-zero  : Valτ Nat Zero
  vτ-suc   : ∀ {v} → Valτ Nat v → Valτ Nat (Suc v)

  vτ-cons  : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → Valτ (τ1 × τ2) (Cons v1 v2)

  vτ-lam   : ∀ {τ1 τ2 body} → Valτ (τ1 ⇒ τ2) (Lam body)
  
  vτ-inl  : ∀ {τ1 τ2 v} → Valτ τ1 v → Valτ (τ1 + τ2) (Inl v)
  vτ-inr  : ∀ {τ1 τ2 v} → Valτ τ2 v → Valτ (τ1 + τ2) (Inr v)
  