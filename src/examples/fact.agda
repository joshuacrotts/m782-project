module examples.fact where

open import examples.prelude
open import examples.mul

-- Factorial over natural numbers.
fact : Term
fact = 
  (Fix
  (Nat ⇒ Nat)
  (Lam
   (If
    (Zero? (Var 0))
    (Suc Zero)
    (App (App mul (Var 0)) (App (Var 1) (Pred (Var 0)))))))

factτ : • ⨟ ∘ ⊢ fact ⦂ Nat ⇒ Nat
factτ =
  (τ-fix 
    (ty-arr ty-nat ty-nat) 
    (τ-lam ty-nat 
      (τ-if 
        (τ-zero? (τ-var ty-nat refl)) 
        (τ-suc τ-zero) 
        (τ-app 
          (τ-app (weaken-closed mulτ) (τ-var ty-nat refl)) 
          (τ-app (τ-var (ty-arr ty-nat ty-nat) refl) (τ-pred (τ-var ty-nat refl)))))))


fact5 : Term
fact5 = App fact (natLit 5)

fact5τ : • ⨟ ∘ ⊢ fact5 ⦂ Nat
fact5τ = τ-app factτ (natLitTy 5)
