module examples.mul where

open import examples.prelude
open import examples.add

-- Natural number multiplication.
mul : Term
mul =
  (Fix
  (Nat ⇒ (Nat ⇒ Nat))
  (Lam
   (Lam
    (If
     (Zero? (Var 1))
     Zero
     (App (App add (Var 0)) (App (App (Var 2) (Pred (Var 1))) (Var 0)))))))
          
mulτ : • ⨟ ∘ ⊢ mul ⦂ Nat ⇒ Nat ⇒ Nat
mulτ =
  (τ-fix
  (ty-arr ty-nat (ty-arr ty-nat ty-nat))
  (τ-lam
   ty-nat
   (τ-lam
    ty-nat
    (τ-if
     (τ-zero? (τ-var {n = 1} ty-nat refl))
     τ-zero
     (τ-app
      (τ-app (weaken-closed addτ) (τ-var {n = 0} ty-nat refl))
      (τ-app
       (τ-app
        (τ-var {n = 2} (ty-arr ty-nat (ty-arr ty-nat ty-nat)) refl)
        (τ-pred (τ-var {n = 1} ty-nat refl)))
       (τ-var {n = 0} ty-nat refl)))))))
