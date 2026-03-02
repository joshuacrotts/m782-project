module examples.append where

open import prelude 
open import examples.add
open import examples.mul
open import examples.length using (length; lengthτ; listOf3; listOf3τ; listOf4Bools; listOf4Boolsτ)

append : Term
append =
  Fix
    (∀' (List (TVar 0) ⇒ List (TVar 0) ⇒ List (TVar 0)))
    (LamT
      (Lam                      -- xs
        (Lam                    -- ys
          (If (Nil? (Var 1))
              (Var 0) -- nil ++ ys = ys
              (Case (First (Var 1))
                -- impossible case, but must return List A
                (Var 1)
                -- right branch: binder h : A at Var 0
                -- var 0 is h, var 1 is ys, var 2 is xs, var 3 is rec
                (LCons (Var 0)
                       (App 
                          (App
                            (AppT (Var 3) (TVar 0))
                            (Rest (Var 2)))
                          (Var 1))))))))

appendτ : • ⨟ ∘ ⊢ append ⦂ ∀' (List (TVar 0) ⇒ List (TVar 0) ⇒ List (TVar 0))
appendτ = 
  τ-fix 
    (ty-all
      (ty-arr (ty-list (ty-var refl))
        (ty-arr (ty-list (ty-var refl))
          (ty-list (ty-var refl)))))
    (τ-lamT 
 (τ-lam
    (ty-list (ty-var refl))
    (τ-lam
     (ty-list (ty-var refl))
     (τ-if
      (τ-nil? (τ-var (ty-list (ty-var refl)) refl))
      (τ-var (ty-list (ty-var refl)) refl)
      (τ-case
       (τ-first (τ-var (ty-list (ty-var refl)) refl))
       (τ-var (ty-list (ty-var refl)) refl)
       (τ-lcons
        (τ-var (ty-var refl) refl)
        (τ-app
         (τ-app (τ-appT (ty-var refl) (τ-var (ty-all (ty-arr (ty-list (ty-var refl)) (ty-arr (ty-list (ty-var refl)) (ty-list (ty-var refl))))) refl)) (τ-rest (τ-var (ty-list (ty-var refl)) refl)))
         (τ-var (ty-list (ty-var refl)) refl)))))))) -- if Cons, then cons head onto recursive call on tail and ys

list123 : Term
list123 = LCons (natLit 1) (LCons (natLit 2) (LCons (natLit 3) (Nil Nat)))
list123τ : • ⨟ ∘ ⊢ list123 ⦂ List Nat
list123τ =
  τ-lcons (natLitTy 1)
    (τ-lcons (natLitTy 2)
      (τ-lcons (natLitTy 3)
        (τ-nil ty-nat)))

list45 : Term
list45 = LCons (natLit 4) (LCons (natLit 5) (Nil Nat))
list45τ : • ⨟ ∘ ⊢ list45 ⦂ List Nat
list45τ =
  τ-lcons (natLitTy 4)
    (τ-lcons (natLitTy 5)
      (τ-nil ty-nat))


append123to45 : Term
append123to45 = App (App (AppT append Nat) list123) list45

append123to45τ : • ⨟ ∘  ⊢ append123to45 ⦂ List Nat
append123to45τ =
  τ-app
    (τ-app (τ-appT ty-nat appendτ) list123τ)
    list45τ