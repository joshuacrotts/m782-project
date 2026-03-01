module examples.mul where

open import examples.eval-driver

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

open import examples.add using (add; addτ)

-- Natural number multiplication.
mul : Term
mul =
  Fix (Nat ⇒ Nat ⇒ Nat)
    (Lam
      (Lam
        (If (Zero? (Var 1))
            Zero
            (App (App add (Var 0))
                 (App (App (Var 2) 
                           (Pred (Var 1))) 
                      (Var 0))))))
          
mulτ : • ⨟ ∘ ⊢ mul ⦂ Nat ⇒ Nat ⇒ Nat
mulτ =
  τ-fix
    (ty-arr ty-nat (ty-arr ty-nat ty-nat))
    (τ-lam
      ty-nat
      (τ-lam
        ty-nat
        (τ-if
          (τ-zero? (τ-var ty-nat refl))
          τ-zero
          (τ-app
            (τ-app (weaken-closed addτ) 
                   (τ-var ty-nat refl))
            (τ-app
              (τ-app
                (τ-var (ty-arr ty-nat (ty-arr ty-nat ty-nat)) refl)
                (τ-pred (τ-var ty-nat refl)))
              (τ-var ty-nat refl))))))
