module examples.map where

open import examples.prelude
open import examples.add
open import examples.mul
open import examples.length using (length; lengthτ; listOf3; listOf3τ; listOf4Bools; listOf4Boolsτ)

map : Term
map =
  Fix
    (∀' (∀' ((TVar 1) ⇒ (TVar 0)) ⇒ List (TVar 1) ⇒ List (TVar 0)))
    (LamT
      (LamT
        (Lam
          (Lam
            (If (Nil? (Var 0))
                (Nil (TVar 0))              -- was (Var 0)
                (Case (First (Var 0))
                  (Nil (TVar 0))            -- was (Var 1)
                  (LCons
                    (App (Var 2) (Var 0))
                    (App
                      (App
                        (AppT (AppT (Var 3) (TVar 1)) (TVar 0))
                        (Var 2))
                      (Rest (Var 1))))))))))

mapτ : • ⨟ ∘ ⊢ map ⦂ ∀' (∀' ((TVar 1) ⇒ (TVar 0)) ⇒ (((List (TVar 1)) ⇒ List (TVar 0))))
mapτ =
  τ-fix
    (ty-all
      (ty-all
        (ty-arr
          (ty-arr (ty-var {n = 1} refl) (ty-var {n = 0} refl))                 -- A ⇒ B
          (ty-arr (ty-list (ty-var {n = 1} refl)) (ty-list (ty-var {n = 0} refl)))))) -- List A ⇒ List B
    (τ-lamT
      (τ-lamT
        (τ-lam
          (ty-arr (ty-var {n = 1} refl) (ty-var {n = 0} refl))                  -- f : A ⇒ B
          (τ-lam
            (ty-list (ty-var {n = 1} refl))                                     -- xs : List A
            (τ-if
              (τ-nil? (τ-var (ty-list (ty-var {n = 1} refl)) refl))

              -- then: []  (must be List B)
              (τ-nil (ty-var refl))

              -- else: case (First xs) ...
              (τ-case
                (τ-first (τ-var (ty-list (ty-var {n = 1} refl)) refl))

                -- left branch: impossible, but must return List B
                (τ-nil (ty-var refl))

                -- right branch: binder h : A at Var 0
                (τ-lcons
                  -- head : B = f h
                  (τ-app
                    (τ-var (ty-arr (ty-var {n = 1} refl) (ty-var {n = 0} refl)) refl)  -- f
                    (τ-var (ty-var {n = 1} refl) refl))                                 -- h

                  -- tail : map f (Rest xs)
                  (τ-app
                    (τ-app
                      (τ-appT
                        (ty-var {n = 0} refl)                                           -- instantiate B
                        (τ-appT
                          (ty-var {n = 1} refl)                                         -- instantiate A
                          (τ-var
                            (ty-all
                              (ty-all
                                (ty-arr
                                  (ty-arr (ty-var {n = 1} refl) (ty-var {n = 0} refl))
                                  (ty-arr (ty-list (ty-var {n = 1} refl))
                                          (ty-list (ty-var {n = 0} refl))))))
                            refl)))                                                     -- rec
                      (τ-var (ty-arr (ty-var {n = 1} refl) (ty-var {n = 0} refl)) refl))-- f
                    (τ-rest (τ-var (ty-list (ty-var {n = 1} refl)) refl))))))))))

mapZero?ToNatList : Term
mapZero?ToNatList = -- map zero? ls where ls is listOf3
  App
    (App
      (AppT 
        (AppT map Nat) 
        Bool)
      (Lam 
        (If (Zero? (Var 0))
            True
            False)))
    listOf3

mapZero?ToNatListτ : • ⨟ ∘ ⊢ mapZero?ToNatList ⦂ List Bool
mapZero?ToNatListτ =
  τ-app 
    (τ-app 
      (τ-appT
        ty-bool
        (τ-appT ty-nat mapτ))
        (τ-lam 
          ty-nat 
          (τ-if (τ-zero? (τ-var ty-nat refl)) τ-true τ-false)))
    listOf3τ

------------------------------------
-- TO RUN:                        --
-- eval mapZero?ToNatListτ 100000 --
------------------------------------