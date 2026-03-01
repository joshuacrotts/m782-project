module examples.fact where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemF.terms
open import SystemF.types
open import SystemF.typing
open import SystemF.values
open import SystemF.semantics
open import SystemF.typing
open import progress
open import preservation
open import lemma using (weaken-closed)

import SystemF.context as C
open C using (TypeContext; •; TermContext; ∘; lookup) -- Don't bring _,_ into scope to avoid name clashes

open import examples.eval-driver
open import examples.mul

-- Factorial over natural numbers.
fact : Term
fact = 
  Fix (Nat ⇒ Nat)
    (Lam
      (If (Zero? (Var 0))
          (Suc Zero)
          (App (App mul (Var 0)) 
               (App (Var 1) 
                    (Pred (Var 0))))))

factτ : • ⨟ ∘ ⊢ fact ⦂ Nat ⇒ Nat
factτ =
  τ-fix
    (ty-arr ty-nat ty-nat)
    (τ-lam
      ty-nat
      (τ-if
        (τ-zero? (τ-var ty-nat refl))
        (τ-suc τ-zero)
        (τ-app
          (τ-app (weaken-closed mulτ) -- (* n (! n-1))
                  (τ-var ty-nat refl))
          (τ-app
            (τ-var (ty-arr ty-nat ty-nat) refl)
            (τ-pred (τ-var ty-nat refl))))))

fact5 : Term
fact5 = App fact (natLit 5)

fact5τ : • ⨟ ∘ ⊢ fact5 ⦂ Nat
fact5τ = τ-app factτ (natLitTy 5)
