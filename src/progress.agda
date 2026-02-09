module Progress where

import SystemF.Context as C
open C using (Context; ∘; lookup) -- Don't bring _,_ into scope to avoid name clashes

open import SystemF.Types
open import SystemF.Terms
open import SystemF.Values
open import SystemF.Typing
open import SystemF.Semantics

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)


-- Progress theorem
-- If ∘ ⊢ e ⦂ τ then either e Val or e steps to e'.
progress : ∀ {e τ} → 
         (∘ ⊢ e ⦂ τ) → 
         (Valτ τ e ⊎ Σ[ e' ∈ Term ] (e ↦ e'))

-- Proof by induction on typing derivation
-- true case
progress τ-true  = inj₁ (vτ-true)

-- false case
progress τ-false = inj₁ (vτ-false)

-- zero case
progress τ-zero  = inj₁ (vτ-zero)

-- suc case (typed values)
progress (τ-suc τ₁) with progress τ₁
... | inj₁ v              = inj₁ (vτ-suc v)
... | inj₂ (e' , st)    = inj₂ (Suc e' , ss-suc-step st)


-- pred case
progress (τ-pred τ₁) with progress τ₁
... | inj₁ vτ-zero              = inj₂ (Zero , ss-pred-zero)         -- pred(zero) steps to zero
... | inj₁ (vτ-suc {v = v₁} v)  = inj₂ (v₁ , ss-pred-suc v)          -- pred(suc(v)) steps to v
... | inj₂ (e' , step)          = inj₂ (Pred e' , ss-pred-step step)


-- zero? case
progress (τ-zero? τ₁) with progress τ₁
... | inj₁ vτ-zero              = inj₂ (True , ss-zero?) -- zero?(zero) steps to true
... | inj₁ (vτ-suc {v = v₁} v)  = inj₂ (False , ss-zero?-suc v) -- zero?(suc(v)) steps to false
... | inj₂ (e' , step)          = inj₂ (Zero? e' , ss-zero?-step step) -- zero?(e) steps to zero?(e')


-- if case
progress (τ-if {e1 = e1} {e2 = e2} {e3 = e3} τ₁ τ₂ τ₃) with progress τ₁
... | inj₁ vτ-true          = inj₂ (e2 , ss-if-true)
... | inj₁ vτ-false         = inj₂ (e3 , ss-if-false) 
... | inj₂ (e1' , step)     = inj₂ (If e1' e2 e3 , ss-if-step step)


-- cons case
progress (τ-cons {e1 = e1} {e2 = e2} τ₁ τ₂) with progress τ₁
... | inj₂ (e1' , step1)        = inj₂ (Cons e1' e2 , ss-cons-left-step step1) -- if e1 steps, the pair steps.
... | inj₁ v1 with progress τ₂                           -- if e1 is a value, check e2.
...     | inj₁ v2               = inj₁ (vτ-cons v1 v2)   -- if both are values then the pair is a value.
...     | inj₂ (e2' , step2)    = inj₂ (Cons e1 e2' , ss-cons-right-step v1 step2)               -- if e2 steps, the pair steps.


-- fst case
progress (τ-fst {e = e} {τ1 = τ1} {τ2 = τ2} τ₁ₓ₂) with progress τ₁ₓ₂  -- induct on the typing of e
... | inj₁ (vτ-cons {v1 = v1t} {v2 = v2t} v1 v2)    = inj₂ (v1t , ss-fst v1 v2) -- if e is a value cons(v1, v2), then fst(cons(v1, v2)) steps to v1
... | inj₂ (e' , step)                              = inj₂ (Fst e' , ss-fst-step step)


-- snd case
progress (τ-snd {e = e} {τ1 = τ1} {τ2 = τ2} τ₁ₓ₂) with progress τ₁ₓ₂  -- induct on the typing of e
... | inj₁ (vτ-cons {v1 = v1t} {v2 = v2t} v1 v2)    = inj₂ (v2t , ss-snd v1 v2) -- if e is a value cons(v1, v2), then snd(cons(v1, v2)) steps to v2
... | inj₂ (e' , step)                              = inj₂ (Snd e' , ss-snd-step step)


-- lam case
progress (τ-lam _) = inj₁ (vτ-lam)


-- app case
progress (τ-app {f = f} {e = e} {τ1 = τ1} {τ2 = τ2} tf te) with progress tf 
... | inj₂ (f' , stepf) = inj₂ (App f' e , ss-app-func stepf)                                     -- if f steps then app f e steps to app f' e
... | inj₁ (vτ-lam) with progress te
...     | inj₁ ve               = {!   !}
...     | inj₂ (e' , stepe)     = inj₂ (App f e' , ss-app-arg stepe)                             -- if e steps then app f e steps to app f e'