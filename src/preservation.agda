{-# OPTIONS --allow-unsolved-metas #-}

module preservation where

open import SystemF.types
open import SystemF.terms
open import SystemF.values
open import SystemF.context
open import SystemF.typing
open import SystemF.semantics
open import lemma

-- Preservation theorem
-- If ∘ ⊢ e ⦂ τ and e ↦ e' then ∘ ⊢ e' ⦂ τ
preservation : ∀ {e e' τ} →
             (• ⨟ ∘ ⊢ e ⦂ τ) →
             (e ↦ e') →
             (• ⨟ ∘ ⊢ e' ⦂ τ)
             
-- Proof by induction on the step relation
preservation (τ-zero? τ-zero) ss-zero?                      = τ-true
preservation (τ-zero? (τ-suc τ₁)) (ss-zero?-suc nv)         = τ-false

preservation (τ-if τ₁ τ₂ τ₃) ss-if-true                     = τ₂
preservation (τ-if τ₁ τ₂ τ₃) ss-if-false                    = τ₃
preservation (τ-if τ₁ τ₂ τ₃) (ss-if-step step)              = τ-if (preservation τ₁ step) τ₂ τ₃

preservation (τ-pred τ-zero) ss-pred-zero                   = τ-zero
preservation (τ-pred (τ-suc τ₁)) (ss-pred-suc nv)           = τ₁
preservation (τ-pred τ₁) (ss-pred-step step)                = τ-pred (preservation τ₁ step)

preservation (τ-suc τ₁) (ss-suc-step step)                  = τ-suc (preservation τ₁ step)
preservation (τ-zero? τ₁) (ss-zero?-step step)              = τ-zero? (preservation τ₁ step)

preservation (τ-cons τ₁ τ₂) (ss-cons-left-step step1)       = τ-cons (preservation τ₁ step1) τ₂

preservation (τ-cons τ₁ τ₂) (ss-cons-right-step v1 step2)   = τ-cons τ₁ (preservation τ₂ step2)
  

preservation (τ-fst (τ-cons τ₁ τ₂)) (ss-fst v1 v2)          = τ₁     -- fst (cons v1 v2) steps to v1
preservation (τ-fst τ₁×₂)           (ss-fst-step step)      = τ-fst (preservation τ₁×₂ step)   -- fst e steps to fst e'
  

preservation (τ-snd (τ-cons τ₁ τ₂)) (ss-snd v1 v2)          = τ₂     -- snd (cons v1 v2) steps to v2
preservation (τ-snd τ₁×₂)           (ss-snd-step step)      = τ-snd (preservation τ₁×₂ step)   -- snd e steps to snd e'

-- app: function steps
preservation (τ-app fTy eTy) (ss-app-func stepf)            = τ-app (preservation fTy stepf) eTy

-- app: argument steps
preservation (τ-app fTy eTy) (ss-app-arg stepe)             = τ-app fTy (preservation eTy stepe)

-- app: beta
preservation (τ-app (τ-lam ΔTy bodyTy) vTy) (ss-app-beta vVal)  = subst0-τ bodyTy vTy

-- inl: steps
preservation (τ-inl τ₁) (ss-inl-step step)                  = τ-inl (preservation τ₁ step)

-- inr: steps
preservation (τ-inr τ₂) (ss-inr-step step)                  = τ-inr (preservation τ₂ step)

-- case: steps
preservation (τ-case τₑ τₗ τᵣ) (ss-case-step step)          = τ-case (preservation τₑ step) τₗ τᵣ
preservation (τ-case τₑ τₗ τᵣ) (ss-case-inl v)              = subst0-τ-inl τₗ τₑ
preservation (τ-case τₑ τₗ τᵣ) (ss-case-inr v)              = subst0-τ-inr τᵣ τₑ

-- fix
preservation (τ-fix {τ = τ} {e = e} ΔTy τₑ) ss-fix              = subst0-τ τₑ (τ-fix ΔTy τₑ)

-- appT : function steps
preservation (τ-appT ΔTy fTy) (ss-appT-func stepf)            = τ-appT ΔTy (preservation fTy stepf)

-- appT : beta
preservation (τ-appT ΔTy (τ-lamT bodyTy)) (ss-appT-beta)  = {!   !}