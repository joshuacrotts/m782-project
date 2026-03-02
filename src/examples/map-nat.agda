module examples.map-nat where

open import examples.prelude
open import examples.add
open import examples.mul

mapℕ : Term
mapℕ = 
  Fix 
    ((Nat ⇒ Nat) ⇒ List Nat ⇒ List Nat)
    (Lam         -- f
      (Lam       -- ls
        (If (Nil? (Var 0))
            (Var 0)
            (Case (First (Var 0))
              (Var 1) -- ls
              (LCons (App (Var 2) (Var 0))  -- h = 0, ls = 1, f = 2, rec = 3
                     (App 
                       (App (Var 3) (Var 2))  -- rec f (Rest ls)
                       (Rest (Var 1))))))))

mapℕτ : • ⨟ ∘ ⊢ mapℕ ⦂ (Nat ⇒ Nat) ⇒ List Nat ⇒ List Nat
mapℕτ =
  τ-fix
    (ty-arr (ty-arr ty-nat ty-nat) (ty-arr (ty-list ty-nat) (ty-list ty-nat)))
    (τ-lam 
      (ty-arr ty-nat ty-nat)
        (τ-lam (ty-list ty-nat) 
          (τ-if (τ-nil? (τ-var (ty-list ty-nat) refl)) 
                (τ-var (ty-list ty-nat) refl) 
                (τ-case 
                  (τ-first (τ-var (ty-list ty-nat) refl))
                  (τ-var (ty-list ty-nat) refl)
                  (τ-lcons 
                    (τ-app 
                      (τ-var (ty-arr ty-nat ty-nat) refl) 
                      (τ-var ty-nat refl))
                    (τ-app 
                      (τ-app 
                        (τ-var (ty-arr (ty-arr ty-nat ty-nat) 
                                       (ty-arr (ty-list ty-nat) (ty-list ty-nat))) refl) 
                        (τ-var (ty-arr ty-nat ty-nat) refl))
                      (τ-rest (τ-var (ty-list ty-nat) refl))))))))

mapAddOne : Term
mapAddOne = App mapℕ (App add (natLit 1))

mapAddOneτ : • ⨟ ∘ ⊢ mapAddOne ⦂ List Nat ⇒ List Nat
mapAddOneτ = τ-app mapℕτ (τ-app addτ (natLitTy 1))

-- evalMapAddOneList123 : Maybe ℕ
-- evalMapAddOneList123 = eval (τ-app mapAddOneτ list123τ) 100