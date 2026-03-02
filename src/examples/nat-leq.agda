module examples.nat-leq where

open import examples.prelude

-- Less than or equal to over natural numbers.

leqℕ : Term
leqℕ = 
  Fix (Nat ⇒ Nat ⇒ Bool)
    (Lam
      (Lam
        (If (Zero? (Var 1)) -- if x is zero, then x ≤ y is true
            True
            (If (Zero? (Var 0)) -- if y is zero but x is not, then x ≤ y is false
                False
                (App 
                  (App 
                    (Var 2) 
                    (Pred (Var 1))) 
                  (Pred (Var 0)))))))
  
leqℕτ : • ⨟ ∘ ⊢ leqℕ ⦂ Nat ⇒ Nat ⇒ Bool
leqℕτ =
  τ-fix
    (ty-arr ty-nat (ty-arr ty-nat ty-bool))
    (τ-lam 
      ty-nat 
      (τ-lam 
        ty-nat 
        (τ-if 
          (τ-zero? (τ-var {n = 1} ty-nat refl)) 
          τ-true 
          (τ-if 
            (τ-zero? 
              (τ-var {n = 0} ty-nat refl)) 
              τ-false 
                (τ-app 
                  (τ-app 
                    (τ-var (ty-arr ty-nat (ty-arr ty-nat ty-bool)) refl) 
                    (τ-pred (τ-var ty-nat refl))) 
                  (τ-pred (τ-var ty-nat refl)))))))

