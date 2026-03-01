module examples.snoc where

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

snoc : Term
snoc =
  Fix
    (∀' (List (TVar 0) ⇒ TVar 0 ⇒ List (TVar 0)))
    (LamT
      (Lam                      -- xs
        (Lam                    -- x
          (If (Nil? (Var 1))
              (LCons (Var 0) (Nil (TVar 0)))
              (Case (First (Var 1))
                -- impossible case, but must return List (TVar 0)
                (LCons (Var 1) (Nil (TVar 0)))
                -- right branch: binder h : TVar 0 at Var 0
                (LCons (Var 0)
                  (App
                    (App
                      (AppT (Var 3) (TVar 0))   -- instantiate rec at A
                      (Rest (Var 2)))
                    (Var 1))))))))


snocτ : • ⨟ ∘ ⊢ snoc ⦂ ∀' (List (TVar 0) ⇒ TVar 0 ⇒ List (TVar 0))
snocτ =
  τ-fix
    (ty-all
      (ty-arr (ty-list (ty-var refl))
        (ty-arr (ty-var refl)
          (ty-list (ty-var refl)))))
    (τ-lamT
      (τ-lam (ty-list (ty-var refl))
        (τ-lam (ty-var refl)
          (τ-if
            (τ-nil? (τ-var (ty-list (ty-var refl)) refl))

            -- then: cons x []
            (τ-lcons
              (τ-var (ty-var refl) refl)
              (τ-nil (ty-var refl)))

            -- else: case (First xs) ...
            (τ-case
              (τ-first (τ-var (ty-list (ty-var refl)) refl))

              -- left branch: impossible but must return List A
              (τ-lcons
                (τ-var (ty-var refl) refl)
                (τ-nil (ty-var refl)))

              -- right branch: binder h : A at Var 0
              (τ-lcons
                (τ-var (ty-var refl) refl)
                (τ-app 
                  (τ-app
                    (τ-appT
                      (ty-var refl) (τ-var (ty-all (ty-arr (ty-list (ty-var refl))
  (ty-arr (ty-var refl)
    (ty-list (ty-var refl))))) refl))
                      (τ-rest (τ-var (ty-list (ty-var refl)) refl)))
                      (τ-var (ty-var refl) refl))))))))

snocListOf3 : Term
snocListOf3 = App (App (AppT snoc Nat) listOf3) (natLit 4)

snocListOf3τ : • ⨟ ∘ ⊢ snocListOf3 ⦂ List Nat
snocListOf3τ =
  τ-app
    (τ-app (τ-appT ty-nat snocτ) listOf3τ)
    (natLitTy 4)