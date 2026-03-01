module examples.filter where

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
open import examples.length using (length; lengthτ; listOf3; listOf3τ; listOf4Bools; listOf4Boolsτ)

{-
(define filter
  (lambda (p)
    (lambda (ls)
      (if (nil? ls)
            nil
            (case (first ls)
             (nil)
             (if (p h)
                 (cons h (filter p (rest ls)))
                 (filter p (rest ls))))))))
-}


filter : Term
filter =
  Fix
    (∀' ((TVar 0) ⇒ Bool) ⇒ List (TVar 0) ⇒ List (TVar 0))
    (LamT
      (Lam  -- p
        (Lam  -- ls
          (If (Nil? (Var 0))
              (Nil (TVar 0))
              (Case (First (Var 0))
                (Nil (TVar 0))
                (If (App (Var 2) (Var 0))  -- h=0 ls=1 p=2 rec=3
                    (LCons (Var 0)
                      (App (App (AppT (Var 3) (TVar 0)) (Var 2))
                           (Rest (Var 1))))
                    (App (App (AppT (Var 3) (TVar 0)) (Var 2))
                         (Rest (Var 1)))))))))

filterτ : • ⨟ ∘ ⊢ filter ⦂ ∀' ((TVar 0) ⇒ Bool) ⇒ (List (TVar 0)) ⇒ List (TVar 0)
filterτ =
  τ-fix
    -- Goal: ∘ ⊢ Fix ... ⦂ ∀A. (A⇒Bool) ⇒ List A ⇒ List A
    (ty-all
      -- Type of fixpoint is ∀A. (A⇒Bool) ⇒ List A ⇒ List A
      (ty-arr
        -- first arg: predicate p : A ⇒ Bool
        (ty-arr (ty-var refl) ty-bool)
        -- second arg: list xs : List A, result: List A
        (ty-arr (ty-list (ty-var refl)) (ty-list (ty-var refl)))))
    (τ-lamT
      -- after LamT: Δ = •,★ ; Γ = inc-Γ ∘ = ∘
      (τ-lam
        -- p : TVar 0 ⇒ Bool
        (ty-arr (ty-var refl) ty-bool)
        (τ-lam
          -- ls : List (TVar 0)
          (ty-list (ty-var refl))
          (τ-if
            -- if (Nil? ls) ...
            (τ-nil? (τ-var (ty-list (ty-var refl)) refl))  -- ls : List A
            -- then branch: Nil A : List A
            (τ-nil (ty-var refl))
            -- else branch: we know ls is non-empty, so we destruct it with First
            (τ-case
              -- scrutinee: First ls : Unit ⨁ A
              (τ-first (τ-var (ty-list (ty-var refl)) refl))
              -- left branch (impossible when ls non-nil, but must type as List A):
              (τ-nil (ty-var refl))
              -- right branch: binder h : A at Var 0
              (τ-if
                -- condition: p h : Bool
                (τ-app
                  (τ-var (ty-arr (ty-var refl) ty-bool) refl) -- p : A ⇒ Bool  (Var 2 in this branch)
                  (τ-var (ty-var refl) refl))                -- h : A         (Var 0)
                -- then: keep h :: filter p (Rest ls)
                (τ-lcons
                  -- head: h : A
                  (τ-var (ty-var refl) refl)
                  -- tail: filter p (Rest ls) : List A
                  (τ-app
                    (τ-app
                      -- function: (AppT rec A) : (A⇒Bool) ⇒ List A ⇒ List A
                      (τ-appT
                        (ty-var refl) -- instantiate rec at A = TVar 0
                        (τ-var
                          -- rec : ∀A. (A⇒Bool) ⇒ List A ⇒ List A   (Var 3 in this branch)
                          (ty-all
                            (ty-arr
                              (ty-arr (ty-var refl) ty-bool)
                              (ty-arr (ty-list (ty-var refl))
                                      (ty-list (ty-var refl)))))
                          refl))
                      -- apply predicate p : A ⇒ Bool
                      (τ-var (ty-arr (ty-var refl) ty-bool) refl))
                    -- apply to Rest ls : List A
                    (τ-rest (τ-var (ty-list (ty-var refl)) refl))))
                -- else: drop h, just filter p (Rest ls)
                (τ-app
                  (τ-app
                    -- again: (AppT A rec)
                    (τ-appT
                      (ty-var refl)
                      (τ-var
                        (ty-all
                          (ty-arr
                            (ty-arr (ty-var refl) ty-bool)
                            (ty-arr (ty-list (ty-var refl))
                                    (ty-list (ty-var refl)))))
                        refl))
                    -- apply predicate p
                    (τ-var (ty-arr (ty-var refl) ty-bool) refl))
                  -- apply Rest ls
                  (τ-rest (τ-var (ty-list (ty-var refl)) refl)))))))))



filterEx : Term
filterEx =
  App
    (App
      (AppT filter Nat)
      (Lam (If (Zero? (Var 0)) False True)))
    listOf3

filterExτ : • ⨟ ∘ ⊢ filterEx ⦂ List Nat
filterExτ =
  τ-app
    (τ-app
      (τ-appT ty-nat filterτ)
      (τ-lam ty-nat (τ-if (τ-zero? (τ-var ty-nat refl)) τ-false τ-true)))
    listOf3τ