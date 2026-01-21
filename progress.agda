module Progress where

open import Syntax
open import Semantics
open import Values
open import Types
open import Terms

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)


-- If we give it a NatVal and a proof that it has type 𝔹, we can derive a contradiction.
noNatIsBool : ∀ {e} → NatVal e → ⊢ e ∶ 𝔹 → ⊥
noNatIsBool nv-zero      ()
noNatIsBool (nv-suc nv)  ()

-- Progress theorem
-- If e : τ then either e Val or e steps to e'.
progress : ∀ {e τ} → 
         (⊢ e ∶ τ) → 
         (Val e ⊎ Σ[ e' ∈ Term ] (e ↦ e'))

-- Proof by induction on typing derivation
-- true case
progress τ-true  = inj₁ v-true

-- false case
progress τ-false = inj₁ v-false

-- zero case
progress τ-zero  = inj₁ (v-val nv-zero)

-- suc case
progress (τ-suc τ₁) with progress τ₁
... | inj₁ (v-val v)  = inj₁ (v-val (nv-suc v))
... | inj₂ (e , step) = inj₂ (suc e , ss-suc-step step)

-- pred case
progress (τ-pred τ₁) with progress τ₁
... | inj₁ (v-val nv-zero)          = inj₂ (zero , ss-pred-zero)
... | inj₁ (v-val (nv-suc {v} nv))  = inj₂ (v , ss-pred-suc nv)
... | inj₂ (e , step)               = inj₂ (pred e , ss-pred-step step)

-- zero? case
progress (τ-zero? τ₁) with progress τ₁
... | inj₁ (v-val nv-zero)          = inj₂ (true , ss-zero?)
... | inj₁ (v-val (nv-suc {v} nv))  = inj₂ (false , ss-zero?-suc nv)
... | inj₂ (e , step)               = inj₂ (zero? e , ss-zero?-step step)

-- if case
progress (τ-if {e1 = e1} {e2 = e2} {e3 = e3} τ₁ τ₂ τ₃) with progress τ₁
... | inj₁ v-true       = inj₂ (e2 , ss-if-true)
... | inj₁ v-false      = inj₂ (e3 , ss-if-false)
... | inj₂ (e1' , step) = inj₂ (if e1' e2 e3 , ss-if-step step)
... | inj₁ (v-val x)    = ⊥-elim (noNatIsBool x τ₁)




