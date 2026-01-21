module Semantics where

------------------------------------------------------------------------
-- Small-step semantics
------------------------------------------------------------------------

open import Types
open import Terms
open import Values

infix 3 _↦_

data _↦_ : Term → Term → Set where
    ---------- Computation rules ----------
    -- 
    -- -------------------------------
    --       zero?(zero) ↦ true
    ss-zero? : zero?(zero) ↦ true

    --           v NatVal
    -- -------------------------------
    --      zero?(suc(v)) ↦ false
    ss-zero?-suc : ∀ {v} → NatVal v → zero?(suc(v)) ↦ false

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

    --           v NatVal
    -- -------------------------------
    --      pred(suc(v)) ↦ v
    ss-pred-suc : ∀ {v} → NatVal v → pred(suc(v)) ↦ v

    --   v1 val    v2 val
    -- -----------------------
    --  fst(cons(v1, v2)) ↦ v1
    ss-fst : ∀ {v1 v2} → Val v1 → Val v2 → fst(cons v1 v2) ↦ v1

    --   v1 val    v2 val
    -- -----------------------
    --  snd(cons(v1, v2)) ↦ v2
    ss-snd : ∀ {v1 v2} → Val v1 → Val v2 → snd(cons v1 v2) ↦ v2


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

    --   e₁ ↦ e₁'       e₂ ↦ e₂'
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-left-step : ∀ {e₁ e₁' e₂ e₂'} → (e₁ ↦ e₁') → (e₂ ↦ e₂') → (cons e₁ e₂ ↦ cons e₁' e₂)

    --   v val            e₂ ↦ e₂'
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-right-step : ∀ {v e₂ e₂'} → (Val v) → (e₂ ↦ e₂') → (cons v e₂ ↦ cons v e₂')

    --          e ↦ e'
    -- -------------------------
    --       fst e ↦ fst e1'
    ss-fst-step : ∀ {e e'} → (e ↦ e') → (fst e ↦ fst e')


    --          e ↦ e'
    -- -------------------------
    --       snd e ↦ snd e'
    ss-snd-step : ∀ {e e'} → (e ↦ e') → (snd e ↦ snd e')

