module examples.insertion-sort where

open import examples.prelude
open import examples.nat-leq

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


-- evalListOfNat isort10ℕτ 1000000


insert-into-sorted : Term
insert-into-sorted =
  (Fix
  (∀' (((TVar 0) ⇒ ((TVar 0) ⇒ Bool))
     ⇒
     ((TVar 0) ⇒ ((List (TVar 0)) ⇒ (List (TVar 0))))))
  (LamT
   (Lam
    (Lam
     (Lam
      (If
       (Nil? (Var 0))
       (LCons (Var 1) (Var 0))
       (Case
        (First (Var 0))
        (Var 1)
        (If
         (App (App (Var 3) (Var 2)) (Var 0))
         (LCons (Var 2) (Var 1))
         (LCons
          (Var 0)
          (App
           (App (App (AppT (Var 4) (TVar 0)) (Var 3)) (Var 2))
           (Rest (Var 1))))))))))))

insert-into-sortedτ : • ⨟ ∘ ⊢ insert-into-sorted ⦂ ∀' (((TVar 0) ⇒ ((TVar 0) ⇒ Bool)) ⇒ ((TVar 0) ⇒ ((List (TVar 0)) ⇒ (List (TVar 0)))))
insert-into-sortedτ = 
  (τ-fix
  (ty-all
   (ty-arr
    (ty-arr (ty-var {n = 0} refl) (ty-arr (ty-var {n = 0} refl) ty-bool))
    (ty-arr
     (ty-var {n = 0} refl)
     (ty-arr
      (ty-list (ty-var {n = 0} refl))
      (ty-list (ty-var {n = 0} refl))))))
  (τ-lamT
   (τ-lam
    (ty-arr (ty-var {n = 0} refl) (ty-arr (ty-var {n = 0} refl) ty-bool))
    (τ-lam
     (ty-var {n = 0} refl)
     (τ-lam
      (ty-list (ty-var {n = 0} refl))
      (τ-if
       (τ-nil? (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl))
       (τ-lcons
        (τ-var {n = 1} (ty-var {n = 0} refl) refl)
        (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl))
       (τ-case
        (τ-first (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl))
        (τ-var {n = 1} (ty-list (ty-var {n = 0} refl)) refl)
        (τ-if
         (τ-app
          (τ-app
           (τ-var
            {n = 3}
            (ty-arr
             (ty-var {n = 0} refl)
             (ty-arr (ty-var {n = 0} refl) ty-bool))
            refl)
           (τ-var {n = 2} (ty-var {n = 0} refl) refl))
          (τ-var {n = 0} (ty-var {n = 0} refl) refl))
         (τ-lcons
          (τ-var {n = 2} (ty-var {n = 0} refl) refl)
          (τ-var {n = 1} (ty-list (ty-var {n = 0} refl)) refl))
         (τ-lcons
          (τ-var {n = 0} (ty-var {n = 0} refl) refl)
          (τ-app
           (τ-app
            (τ-app
             (τ-appT
              (ty-var {n = 0} refl)
              (τ-var
               {n = 4}
               (ty-all
                (ty-arr
                 (ty-arr
                  (ty-var {n = 0} refl)
                  (ty-arr (ty-var {n = 0} refl) ty-bool))
                 (ty-arr
                  (ty-var {n = 0} refl)
                  (ty-arr
                   (ty-list (ty-var {n = 0} refl))
                   (ty-list (ty-var {n = 0} refl))))))
               refl))
             (τ-var
              {n = 3}
              (ty-arr
               (ty-var {n = 0} refl)
               (ty-arr (ty-var {n = 0} refl) ty-bool))
              refl))
            (τ-var {n = 2} (ty-var {n = 0} refl) refl))
           (τ-rest
            (τ-var {n = 1} (ty-list (ty-var {n = 0} refl)) refl))))))))))))

isort : Term
isort  =
  (Fix
  (∀' (((TVar 0) ⇒ ((TVar 0) ⇒ Bool)) ⇒ ((List (TVar 0)) ⇒ (List (TVar 0)))))
  (LamT
   (Lam
    (Lam
     (If
      (Nil? (Var 0))
      (Var 0)
      (Case
       (First (Var 0))
       (Var 1)
       (App
        (App (App (AppT insert-into-sorted (TVar 0)) (Var 2)) (Var 0))
        (App (App (AppT (Var 3) (TVar 0)) (Var 2)) (Rest (Var 1))))))))))

isortτ : • ⨟ ∘ ⊢ isort ⦂ ∀' (((TVar 0) ⇒ ((TVar 0) ⇒ Bool)) ⇒ ((List (TVar 0)) ⇒ (List (TVar 0))))
isortτ = 
  (τ-fix
  (ty-all
   (ty-arr
    (ty-arr (ty-var {n = 0} refl) (ty-arr (ty-var {n = 0} refl) ty-bool))
    (ty-arr (ty-list (ty-var {n = 0} refl)) (ty-list (ty-var {n = 0} refl)))))
  (τ-lamT
   (τ-lam
    (ty-arr (ty-var {n = 0} refl) (ty-arr (ty-var {n = 0} refl) ty-bool))
    (τ-lam
     (ty-list (ty-var {n = 0} refl))
     (τ-if
      (τ-nil? (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl))
      (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl)
      (τ-case
       (τ-first (τ-var {n = 0} (ty-list (ty-var {n = 0} refl)) refl))
       (τ-var {n = 1} (ty-list (ty-var {n = 0} refl)) refl)
       (τ-app
        (τ-app
         (τ-app
          (τ-appT (ty-var {n = 0} refl) (weaken-closed insert-into-sortedτ))
          (τ-var
           {n = 2}
           (ty-arr
            (ty-var {n = 0} refl)
            (ty-arr (ty-var {n = 0} refl) ty-bool))
           refl))
         (τ-var {n = 0} (ty-var {n = 0} refl) refl))
        (τ-app
         (τ-app
          (τ-appT
           (ty-var {n = 0} refl)
           (τ-var
            {n = 3}
            (ty-all
             (ty-arr
              (ty-arr
               (ty-var {n = 0} refl)
               (ty-arr (ty-var {n = 0} refl) ty-bool))
              (ty-arr
               (ty-list (ty-var {n = 0} refl))
               (ty-list (ty-var {n = 0} refl)))))
            refl))
          (τ-var
           {n = 2}
           (ty-arr
            (ty-var {n = 0} refl)
            (ty-arr (ty-var {n = 0} refl) ty-bool))
           refl))
         (τ-rest (τ-var {n = 1} (ty-list (ty-var {n = 0} refl)) refl))))))))))


isort10ℕ : Term
isort10ℕ =
  (App
    (App
      (AppT isort Nat)
      leqℕ)
    listOf10ℕ)

isort10ℕτ : • ⨟ ∘ ⊢ isort10ℕ ⦂ List Nat
isort10ℕτ =
    (τ-app
      (τ-app 
        (τ-appT ty-nat isortτ) 
        leqℕτ)
      listOf10ℕτ)

