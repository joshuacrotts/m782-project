module examples.add where

open import examples.prelude

add : Term
add = 
  (Fix
  (Nat ⇒ (Nat ⇒ Nat))
  (Lam
   (Lam
    (If
     (Zero? (Var 1))
     (Var 0)
     (App (App (Var 2) (Pred (Var 1))) (Suc (Var 0)))))))

addτ : • ⨟ ∘ ⊢ add ⦂ Nat ⇒ Nat ⇒ Nat
addτ = 
  (τ-fix
  (ty-arr ty-nat (ty-arr ty-nat ty-nat))
  (τ-lam
   ty-nat
   (τ-lam
    ty-nat
    (τ-if
     (τ-zero? (τ-var {n = 1} ty-nat refl))
     (τ-var {n = 0} ty-nat refl)
     (τ-app
      (τ-app
       (τ-var {n = 2} (ty-arr ty-nat (ty-arr ty-nat ty-nat)) refl)
       (τ-pred (τ-var {n = 1} ty-nat refl)))
      (τ-suc (τ-var {n = 0} ty-nat refl)))))))

add34 : Term
add34 = App (App add (natLit 3)) (natLit 4)

add34τ : • ⨟ ∘ ⊢ add34 ⦂ Nat
add34τ = τ-app (τ-app addτ (natLitTy 3)) (natLitTy 4)

evalAdd34 : Maybe ℕ
evalAdd34 = evalNat add34τ 100 -- Should return just 7