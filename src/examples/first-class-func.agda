module examples.first-class-func where

open import examples.prelude
open import examples.add

apply-func : Term
apply-func = 
  (Lam 
    (Lam
      (App (Var 1) (Var 0))))

apply-funcτ : • ⨟ ∘ ⊢ apply-func ⦂ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat)
apply-funcτ =
  τ-lam
    (ty-arr ty-nat ty-nat)
    (τ-lam
      ty-nat
      (τ-app
        (τ-var (ty-arr ty-nat ty-nat) refl)
        (τ-var ty-nat refl)))

add-two : Term
add-two = App apply-func (App add (natLit 2))

add-twoτ : • ⨟ ∘ ⊢ add-two ⦂ Nat ⇒ Nat
add-twoτ =
  τ-app apply-funcτ (τ-app addτ (natLitTy 2))

res : Maybe ℕ
res = evalNat (τ-app add-twoτ (natLitTy 10)) 100