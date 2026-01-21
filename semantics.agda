module Semantics where

------------------------------------------------------------------------
-- Small-step semantics
------------------------------------------------------------------------

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
    

