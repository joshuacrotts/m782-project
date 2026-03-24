module examples.eval-driver where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemF.definitions hiding (_∷_)
open import theorems.progress
open import theorems.preservation 
open import theorems.lemmas.summary 

import Data.List as AgdaList
open AgdaList using ([]; _∷_)


--
-- Given a term that is a number, convert it into a ℕ.
-- If it's not a number, return nothing.
--
toℕ : Term → Maybe ℕ
toℕ Zero    = just zero
toℕ (Suc t) with toℕ t
... | just n  = just (suc n)
... | nothing = nothing
toℕ _       = nothing

--
-- Given a term that is a boolean, convert it into a 𝔹.
-- If it's not a boolean, return nothing.
--
toBool : Term → Maybe 𝔹
toBool True  = just true
toBool False = just false
toBool _     = nothing

--
-- Given a term that is a list of numbers, convert it into a List ℕ.
-- If it's not a list of numbers, return nothing.
--
toListOfℕ : Term → Maybe (AgdaList.List ℕ)
toListOfℕ (Nil Nat) = just []
toListOfℕ (LCons t ts) with toℕ t | toListOfℕ ts
... | just n  | just ns  = just (n ∷ ns)
... | _       | _       = nothing
toListOfℕ _   = nothing

-- 
-- Eval partial function, use n steps to limit evaluation depth.
-- If evaluation finishes before n steps, return the resulting value wrapped in just.
-- If evaluation does not finish before n steps, return nothing.
--
eval : ∀ {e τ} → (te : • ⨟ ∘ ⊢ e ⦂ τ) → ℕ → Maybe Term
eval te zero = nothing
eval {e = e} te (suc n) with progress te
... | inj₁ v = just e
... | inj₂ (e' , step) = eval (preservation te step) n

--
-- Evaluates a term that reduces to type Nat. 
-- Displays the results as a Maybe ℕ.
-- 
evalNat : ∀ {e} → (te : • ⨟ ∘ ⊢ e ⦂ Nat) → ℕ → Maybe ℕ
evalNat te fuel with eval te fuel
... | just v  = toℕ v
... | nothing = nothing

--
-- Evaluates a term that reduces to type Bool.
-- Displays the result as a Maybe 𝔹.
--
evalBool : ∀ {e} → (te : • ⨟ ∘ ⊢ e ⦂ Bool) → ℕ → Maybe 𝔹
evalBool te fuel with eval te fuel
... | just v  = toBool v
... | nothing = nothing

evalListOfNat : ∀ {e} → (te : • ⨟ ∘ ⊢ e ⦂ List Nat) → ℕ → Maybe (AgdaList.List ℕ)
evalListOfNat te fuel with eval te fuel
... | just v  = toListOfℕ v
... | nothing = nothing

--
-- Converts a ℕ into a Term.
--
natLit : ℕ → Term
natLit zero = Zero
natLit (suc n) = Suc (natLit n)

--
-- Creates a type judgment for a ℕ literal.
--
natLitTy : ∀ n → • ⨟ ∘ ⊢ natLit n ⦂ Nat
natLitTy zero    = τ-zero
natLitTy (suc n) = τ-suc (natLitTy n)