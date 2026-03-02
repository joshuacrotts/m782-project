module examples.insertion-sort where

open import examples.prelude
open import examples.nat-leq

insert-into-sortedℕ : Term
insert-into-sortedℕ = 
    (Fix 
      (Nat ⇒ List Nat ⇒ List Nat)
      (Lam -- n
        (Lam -- ls
          (If (Nil? (Var 0))
              (LCons (Var 1) (Var 0))
              (Case (First (Var 0))
                    (Var 1)
                    (If (App (App leqℕ (Var 2)) (Var 0))
                        (LCons (Var 2) (Var 1))
                        (LCons (Var 0)
                               (App 
                                 (App 
                                   (Var 3) 
                                   (Var 2))
                                 (Rest (Var 1))))))))))

insert-into-sortedℕτ : • ⨟ ∘ ⊢ insert-into-sortedℕ ⦂ Nat ⇒ List Nat ⇒ List Nat
insert-into-sortedℕτ = 
    τ-fix 
      (ty-arr ty-nat (ty-arr (ty-list ty-nat) (ty-list ty-nat))) 
      (τ-lam 
        ty-nat 
        (τ-lam 
          (ty-list ty-nat) 
          (τ-if 
            (τ-nil? (τ-var (ty-list ty-nat) refl)) 
            (τ-lcons 
              (τ-var ty-nat refl) 
              (τ-var (ty-list ty-nat) refl)) 
            (τ-case 
              (τ-first (τ-var (ty-list ty-nat) refl)) 
              (τ-var (ty-list ty-nat) refl) 
              (τ-if 
                (τ-app 
                  (τ-app 
                    (weaken-closed leqℕτ)
                    (τ-var ty-nat refl)) 
                  (τ-var 
                    ty-nat 
                    refl)) 
                (τ-lcons 
                  (τ-var ty-nat refl) 
                  (τ-var (ty-list ty-nat) refl)) 
                (τ-lcons 
                  (τ-var ty-nat refl) 
                  (τ-app 
                    (τ-app 
                      (τ-var 
                        (ty-arr ty-nat (ty-arr (ty-list ty-nat) (ty-list ty-nat))) 
                        refl) 
                      (τ-var ty-nat refl))
                    (τ-rest (τ-var (ty-list ty-nat) refl)))))))))

isortℕ : Term
isortℕ = 
    Fix 
      (List Nat ⇒ List Nat)
      (Lam -- ls
        (If (Nil? (Var 0))
            (Var 0)
            (Case (First (Var 0))
              (Var 1)
              (App
                (App insert-into-sortedℕ (Var 0))
                (App (Var 2) (Rest (Var 1)))))))
              

isortℕτ : • ⨟ ∘ ⊢ isortℕ ⦂ List Nat ⇒ List Nat
isortℕτ = 
    τ-fix 
      (ty-arr (ty-list ty-nat) (ty-list ty-nat)) 
      (τ-lam 
        (ty-list ty-nat) 
        (τ-if 
          (τ-nil? (τ-var (ty-list ty-nat) refl)) 
          (τ-var (ty-list ty-nat) refl) 
          (τ-case 
            (τ-first (τ-var (ty-list ty-nat) refl)) 
            (τ-var (ty-list ty-nat) refl) 
            (τ-app 
              (τ-app 
                (weaken-closed insert-into-sortedℕτ) 
                (τ-var ty-nat refl)) 
              (τ-app 
                (τ-var (ty-arr (ty-list ty-nat) (ty-list ty-nat)) refl) 
                (τ-rest (τ-var (ty-list ty-nat) refl)))))))

listOf10ℕ : Term
listOf10ℕ = 
  (LCons (natLit 17)
    (LCons (natLit 3)
      (LCons (natLit 14)
        (LCons (natLit 1)
          (LCons (natLit 95)
            (LCons (natLit 101)
              (LCons (natLit 67)
                (LCons (natLit 42)
                  (LCons (natLit 83)
                    (LCons (natLit 55)
                      (Nil Nat)))))))))))

listOf10ℕτ : • ⨟ ∘ ⊢ listOf10ℕ ⦂ List Nat
listOf10ℕτ =
  τ-lcons (natLitTy 17) 
    (τ-lcons (natLitTy 3) 
      (τ-lcons (natLitTy 14) 
        (τ-lcons (natLitTy 1) 
          (τ-lcons (natLitTy 95) 
            (τ-lcons (natLitTy 101) 
              (τ-lcons (natLitTy 67) 
                (τ-lcons (natLitTy 42) 
                  (τ-lcons (natLitTy 83) 
                    (τ-lcons (natLitTy 55) 
                      (τ-nil ty-nat))))))))))

isort10ℕ : Term
isort10ℕ = App isortℕ listOf10ℕ

isort10ℕτ : • ⨟ ∘ ⊢ isort10ℕ ⦂ List Nat
isort10ℕτ =
  τ-app
    isortℕτ
    listOf10ℕτ

-- evalListOfNat isort10ℕτ 1000000