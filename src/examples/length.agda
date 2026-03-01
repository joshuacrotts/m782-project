module examples.length where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import SystemF.terms
open import SystemF.types
open import SystemF.typing
open import SystemF.values
open import SystemF.semantics
open import SystemF.typing
open import progress
open import preservation
open import lemma using (weaken-closed)

import SystemF.context as C
open C using (TypeContext; •; TermContext; ∘; lookup) -- Don't bring _,_ into scope to avoid name clashes

open import examples.eval-driver
open import examples.add
open import examples.mul


length : Term
length =
  LamT
    (Fix (List (TVar 0) ⇒ Nat)
      (Lam
        (If (Nil? (Var 0))
            Zero
            (Suc (App (Var 1) (Rest (Var 0)))))))

lengthτ : • ⨟ ∘ ⊢ length ⦂ ∀' (List (TVar 0) ⇒ Nat)
lengthτ =
  τ-lamT
    (τ-fix
      (ty-arr (ty-list (ty-var refl)) ty-nat) -- ∀α. List α ⇒ Nat
      (τ-lam                                  -- lambda 
        (ty-list (ty-var refl))               -- ls
        (τ-if
          (τ-nil? (τ-var (ty-list (ty-var refl)) refl)) -- Nil? ls
          τ-zero                                        -- 0
          (τ-suc                                        -- 1 + 
            (τ-app
              (τ-var (ty-arr (ty-list (ty-var refl)) ty-nat) refl) -- length ...
              (τ-rest
                (τ-var (ty-list (ty-var refl)) refl)))))))         -- Rest ls

listOf3 : Term
listOf3 =
  LCons (natLit 1)
    (LCons (natLit 2)
      (LCons (natLit 3)
        (Nil Nat)))

listOf3τ : • ⨟ ∘ ⊢ listOf3 ⦂ List Nat
listOf3τ =
  τ-lcons (natLitTy 1)
    (τ-lcons (natLitTy 2)
      (τ-lcons (natLitTy 3)
        (τ-nil ty-nat)))

listOf4Bools : Term
listOf4Bools =
  LCons True
    (LCons False
      (LCons True
        (LCons False
          (Nil Bool))))

listOf4Boolsτ : • ⨟ ∘ ⊢ listOf4Bools ⦂ List Bool
listOf4Boolsτ =
  τ-lcons τ-true
    (τ-lcons τ-false
      (τ-lcons τ-true
        (τ-lcons τ-false
          (τ-nil ty-bool))))

length-listOf3τ : • ⨟ ∘ ⊢ App (AppT length Nat) listOf3 ⦂ Nat
length-listOf3τ =
  τ-app
    (τ-appT ty-nat lengthτ)   -- swapped!
    listOf3τ

length-listOf4Boolsτ : • ⨟ ∘ ⊢ App (AppT length Bool) listOf4Bools ⦂ Nat
length-listOf4Boolsτ =
  τ-app
    (τ-appT ty-bool lengthτ)   -- swapped!
    listOf4Boolsτ

evalLengthListOf3 : Maybe ℕ
evalLengthListOf3 = evalNat length-listOf3τ 100

evalLengthListOf4Bools : Maybe ℕ
evalLengthListOf4Bools = evalNat length-listOf4Boolsτ 100

add-lengths-of-different-typed-lists : Term
add-lengths-of-different-typed-lists =
  (LamT -- A
    (LamT -- B
      (Lam -- xs -- type List A
        (Lam -- ys -- type List B
          (App (App add (App (AppT length (TVar 1)) (Var 1))) -- length A xs
               (App (AppT length (TVar 0)) (Var 0))))))) -- length B ys

add-lengths-of-different-typed-listsτ : • ⨟ ∘ ⊢ add-lengths-of-different-typed-lists ⦂ ∀' (∀' ((List (TVar 1)) ⇒ (List (TVar 0)) ⇒ Nat))
add-lengths-of-different-typed-listsτ =
  τ-lamT          -- A
    (τ-lamT       -- B
      (τ-lam (ty-list (ty-var refl))                        -- xs
        (τ-lam (ty-list (ty-var refl))                        -- ys
          (τ-app 
            (τ-app 
              (weaken-closed addτ)
              (τ-app (τ-appT (ty-var refl) (weaken-closed lengthτ)) (τ-var (ty-list (ty-var refl)) refl))) 
            (τ-app 
              (τ-appT 
                (ty-var refl) 
                (weaken-closed lengthτ)) 
              ((τ-var 
                (ty-list (ty-var refl)) 
                refl)))))))

evalAddLengthsOfDifferentTypedLists : Term
evalAddLengthsOfDifferentTypedLists = 
  App
    (App
      (AppT 
        (AppT add-lengths-of-different-typed-lists Nat)
        Bool)
      listOf3)
    listOf4Bools

evalAddLengthsOfDifferentTypedListsτ : • ⨟ ∘ ⊢ evalAddLengthsOfDifferentTypedLists ⦂ Nat
evalAddLengthsOfDifferentTypedListsτ =
  τ-app
    (τ-app
      (τ-appT
        ty-bool
        (τ-appT ty-nat add-lengths-of-different-typed-listsτ))
      listOf3τ)
    listOf4Boolsτ

evalAddLengthsOfDifferentTypedListsRes : Maybe ℕ
evalAddLengthsOfDifferentTypedListsRes = evalNat evalAddLengthsOfDifferentTypedListsτ 100
