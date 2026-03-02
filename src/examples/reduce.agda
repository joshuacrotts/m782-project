module examples.reduce where

open import examples.prelude
open import examples.add
open import examples.mul
open import examples.length using (length; lengthτ; listOf3; listOf3τ; listOf4Bools; listOf4Boolsτ)

-- reduce : forall A . (A -> A -> A) -> A -> List A -> A
reduce : Term
reduce =
    Fix
    (∀' ((TVar 0) ⇒ ((TVar 0) ⇒ (TVar 0))) ⇒ (TVar 0) ⇒ List (TVar 0) ⇒ (TVar 0))
    (LamT
      (Lam -- f
        (Lam -- acc
          (Lam -- ls
            (If (Nil? (Var 0))
                (Var 1) -- acc
                (Case (First (Var 0))
                      (Var 2) -- acc is now var 2 due to the case binder
                      (App
                        (App 
                          (App
                            (AppT (Var 4) (TVar 0)) -- recursive call to reduce
                            (Var 3))
                          (App 
                            (App (Var 3) (Var 2))
                            (Var 0))) -- f applied to h and acc
                        (Rest (Var 1)))))))))
      
reduceτ : • ⨟ ∘ ⊢ reduce ⦂ ∀' ((TVar 0) ⇒ ((TVar 0) ⇒ (TVar 0))) ⇒ (TVar 0) ⇒ List (TVar 0) ⇒ (TVar 0)
reduceτ = 
    τ-fix 
      (ty-all 
        (ty-arr 
          (ty-arr (ty-var refl) (ty-arr (ty-var refl) (ty-var refl))) -- A ⇒ A
          (ty-arr (ty-var refl) (ty-arr (ty-list (ty-var refl)) (ty-var refl)))))
        (τ-lamT 
          (τ-lam 
            (ty-arr (ty-var refl) (ty-arr (ty-var refl) (ty-var refl)))
            (τ-lam 
              (ty-var refl) 
              (τ-lam 
                (ty-list (ty-var refl)) 
                (τ-if 
                  (τ-nil? (τ-var (ty-list (ty-var refl)) refl)) 
                  (τ-var (ty-var refl) refl) 
                  (τ-case 
                    (τ-first (τ-var (ty-list (ty-var refl)) refl)) 
                    (τ-var (ty-var refl) refl)
                    (τ-app 
                      (τ-app 
                        (τ-app 
                          (τ-appT 
                            (ty-var refl) 
                            (τ-var 
                              (ty-all 
                                (ty-arr (ty-arr (ty-var refl) (ty-arr (ty-var refl) (ty-var refl))) (ty-arr (ty-var refl) (ty-arr (ty-list (ty-var refl)) (ty-var refl))))) 
                              refl)) 
                          (τ-var 
                            (ty-arr (ty-var refl) (ty-arr (ty-var refl) (ty-var refl))) 
                            refl)) 
                        (τ-app 
                          (τ-app 
                            (τ-var (ty-arr (ty-var refl) (ty-arr (ty-var refl) (ty-var refl))) refl) 
                            (τ-var (ty-var refl) refl)) 
                          (τ-var (ty-var refl) refl)))
                      (τ-rest (τ-var (ty-list (ty-var refl)) refl)))))))))

reduceMulOverList : Term
reduceMulOverList = 
    (App 
      (App 
        (App 
          (AppT 
            reduce 
            Nat) 
          mul) 
        (natLit 1))
      listOf3)

-- ((((reduce A) f) 1) ls)

reduceMulOverListτ : • ⨟ ∘ ⊢ reduceMulOverList ⦂ Nat
reduceMulOverListτ = 
    τ-app 
      (τ-app 
        (τ-app 
          (τ-appT ty-nat reduceτ)
          mulτ) 
        (natLitTy 1)) 
      listOf3τ


---------------------------------------
-- TO RUN:                           --
-- evalNat reduceMulOverListτ 100000 --
---------------------------------------