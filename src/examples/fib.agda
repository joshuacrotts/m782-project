module examples.fib where

open import examples.prelude
open import examples.add

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