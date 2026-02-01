module SystemF.Semantics where

------------------------------------------------------------------------
-- Small-step semantics
------------------------------------------------------------------------

open import SystemF.Types
open import SystemF.Terms
open import SystemF.Values

infix 3 _↦_

data _↦_ : Term → Term → Set where
    ---------- Computation rules ----------
    -- 
    -- -------------------------------
    --       zero?(zero) ↦ true
    ss-zero? : zero?(zero) ↦ true

    --           v Valτ Nat
    -- -------------------------------
    --      zero?(suc(v)) ↦ false
    ss-zero?-suc : ∀ {v} → Valτ Nat v → zero?(suc(v)) ↦ false

    -- 
    -- -------------------------------
    --       if true e2 e3 ↦ e2
    ss-if-true : ∀ {e2 e3} → if true e2 e3 ↦ e2

    -- 
    -- -------------------------------
    --       if false e2 e3 ↦ e3
    ss-if-false : ∀ {e2 e3} → if false e2 e3 ↦ e3

    --          
    -- -------------------------------
    --     pred(zero) ↦ zero
    ss-pred-zero : pred(zero) ↦ zero

    --           v Valτ Nat
    -- -------------------------------
    --      pred(suc(v)) ↦ v
    ss-pred-suc : ∀ {v} → Valτ Nat v → pred(suc(v)) ↦ v

    --   v1 Valτ τ1    v2 Valτ τ2
    -- -----------------------------
    --  fst (cons v1 v2) ↦ v1
    ss-fst : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → fst (cons v1 v2) ↦ v1

    --   v1 Valτ τ1    v2 Valτ τ2
    -- -----------------------------
    --  snd (cons v1 v2) ↦ v2
    ss-snd : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → snd (cons v1 v2) ↦ v2


    ---------- Congruence rules ----------

    --           e1 ↦ e1'
    -- -------------------------------
    --   if e1 e2 e3 ↦ if e1' e2 e3
    ss-if-step : ∀ {e1 e1' e2 e3} → (e1 ↦ e1') → (if e1 e2 e3 ↦ if e1' e2 e3)

    --           e ↦ e'
    -- -------------------------------
    --     suc(e) ↦ suc(e')
    ss-suc-step : ∀ {e e'} → (e ↦ e') → (suc e ↦ suc e')

    --           e ↦ e'
    -- -------------------------------
    --     zero?(e) ↦ zero(e')
    ss-zero?-step : ∀ {e e'} → (e ↦ e') → (zero? e ↦ zero? e')

    --           e ↦ e'
    -- -------------------------------
    --    pred(e) ↦ pred(e')
    ss-pred-step : ∀ {e e'} → (e ↦ e') → (pred e ↦ pred e')

    --   e₁ ↦ e₁' 
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-left-step : ∀ {e₁ e₁' e₂} → (e₁ ↦ e₁') → (cons e₁ e₂ ↦ cons e₁' e₂)


    --   v val            e₂ ↦ e₂'
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-right-step :   ∀ {τ v e₂ e₂'} → Valτ τ v → (e₂ ↦ e₂') → cons v e₂ ↦ cons v e₂'

    --   e ↦ e'
    -- ----------------------------
    --     fst e ↦ fst e'
    ss-fst-step : ∀ {e e'} → (e ↦ e') → (fst e ↦ fst e')

    --  e ↦ e'
    -- ---------------------
    --     snd e ↦ snd e'
    ss-snd-step : ∀ {e e'} → (e ↦ e') → (snd e ↦ snd e')

    -- --          e ↦ e'
    -- -- ----------------------------
    -- --   lam e ↦ lam e'
    -- ss-lam-step : ∀ {e e'} → (e ↦ e') → (lam e ↦ lam e')

    -- --   f ↦ f'
    -- -- ----------------------------
    -- --   app f e ↦ app f' e
    -- ss-app-func : ∀ {f f' e} → (f ↦ f') → (app f e ↦ app f' e)

    -- --   e ↦ e'
    -- -- ----------------------------
    -- --   app f e ↦ app f e'
    -- ss-app-arg : ∀ {f e e'} → (e ↦ e') → (app f e ↦ app f e')

    -- --   v1 val
    -- -- ----------------------------
    -- -- app (lam body) v1 ↦ [v1/0] body
    -- ss-app-beta : ∀ {body v1 τ1} → Valτ τ1 v1 → app (lam body) v1 ↦ sub0 v1 body