module examples.fib where

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
open import examples.add
open import examples.mul

fib : Term
fib =
  Fix (Nat ⇒ Nat)
    (Lam
      (If (Zero? (Var 0))
          Zero
          (If (Zero? (Pred (Var 0)))
              (Suc Zero)
              (App (App add (App (Var 1) (Pred (Var 0))))
                   (App (Var 1) 
                        (Pred (Pred (Var 0))))))))

fibτ : • ⨟ ∘ ⊢ fib ⦂ Nat ⇒ Nat
fibτ =
  τ-fix
    (ty-arr ty-nat ty-nat)
    (τ-lam
      ty-nat
      (τ-if
        (τ-zero? (τ-var ty-nat refl))
        τ-zero
        (τ-if
          (τ-zero? (τ-pred (τ-var ty-nat refl)))
          (τ-suc τ-zero)
          (τ-app
            (τ-app (weaken-closed addτ)
                    (τ-app (τ-var (ty-arr ty-nat ty-nat) refl) (τ-pred (τ-var ty-nat refl))))
            (τ-app (τ-var (ty-arr ty-nat ty-nat) refl)
                    (τ-pred (τ-pred (τ-var ty-nat refl))))))))

fib10 : Term
fib10 = App fib (natLit 10)
fib10τ : • ⨟ ∘ ⊢ fib10 ⦂ Nat
fib10τ = τ-app fibτ (natLitTy 10)