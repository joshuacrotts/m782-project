module examples.first-class-func where

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