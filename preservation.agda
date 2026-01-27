module Preservation where

open import Syntax
open import Semantics
open import Values
open import Types
open import Progress
open import Terms


------------------------------------------------------------------------

-- Preservation theorem
-- If e : τ and e ↦ e' then e' : τ
preservation : ∀ {e e' τ} →
             (⊢ e ∶ τ) →
             (e ↦ e') →
             (⊢ e' ∶ τ)

-- Proof by induction on the step relation
preservation (τ-zero? τ-zero) ss-zero?                                          = τ-true
preservation (τ-zero? (τ-suc τ₁)) (ss-zero?-suc nv)                             = τ-false

preservation (τ-if τ₁ τ₂ τ₃) ss-if-true                                         = τ₂
preservation (τ-if τ₁ τ₂ τ₃) ss-if-false                                        = τ₃
preservation (τ-if τ₁ τ₂ τ₃) (ss-if-step step)                                  = τ-if (preservation τ₁ step) τ₂ τ₃

preservation (τ-pred τ-zero) ss-pred-zero                                       = τ-zero
preservation (τ-pred (τ-suc τ₁)) (ss-pred-suc nv)                               = τ₁
preservation (τ-pred τ₁) (ss-pred-step step)                                    = τ-pred (preservation τ₁ step)

preservation (τ-suc τ₁) (ss-suc-step step)                                      = τ-suc (preservation τ₁ step)
preservation (τ-zero? τ₁) (ss-zero?-step step)                                  = τ-zero? (preservation τ₁ step)

preservation (τ-cons τ₁ τ₂) (ss-cons-left-step step1)  =    -- if e1 steps, the pair steps.
  τ-cons (preservation τ₁ step1) τ₂

preservation (τ-cons τ₁ τ₂) (ss-cons-right-step v1 step2) =   -- if e2 steps, the pair steps.
  τ-cons τ₁ (preservation τ₂ step2)

preservation (τ-fst (τ-cons τ₁ τ₂)) (ss-fst v1 v2)     = τ₁     -- fst (cons v1 v2) steps to v1
preservation (τ-fst τ₁×₂)           (ss-fst-step step) =    -- fst e steps to fst e'
  τ-fst (preservation τ₁×₂ step)

preservation (τ-snd (τ-cons τ₁ τ₂)) (ss-snd v1 v2)     = τ₂     -- snd (cons v1 v2) steps to v2
preservation (τ-snd τ₁×₂)           (ss-snd-step step) =    -- snd e steps to snd e'
  τ-snd (preservation τ₁×₂ step)
