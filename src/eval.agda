module eval where

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


--
-- Given a term that is a number, convert it into a ℕ.
-- If it's not a number, return nothing.
--
toℕ : Term → Maybe ℕ
toℕ Zero    = just zero
toℕ (Suc t) with toℕ t
... | just n  = just (suc n)
... | nothing = nothing
toℕ _       = nothing

--
-- Given a term that is a boolean, convert it into a 𝔹.
-- If it's not a boolean, return nothing.
--
toBool : Term → Maybe 𝔹
toBool True  = just true
toBool False = just false
toBool _     = nothing

-- 
-- Eval partial function, use n steps to limit evaluation depth.
-- If evaluation finishes before n steps, return the resulting value wrapped in just.
-- If evaluation does not finish before n steps, return nothing.
--
eval : ∀ {e τ} → (te : • ⨟ ∘ ⊢ e ⦂ τ) → ℕ → Maybe Term
eval te zero = nothing
eval {e = e} te (suc n) with progress te
... | inj₁ v = just e
... | inj₂ (e' , step) = eval (preservation te step) n

--
-- Evaluates a term that reduces to type Nat. 
-- Displays the results as a Maybe ℕ.
-- 
evalNat : ∀ {e} → (te : • ⨟ ∘ ⊢ e ⦂ Nat) → ℕ → Maybe ℕ
evalNat te fuel with eval te fuel
... | just v  = toℕ v
... | nothing = nothing

--
-- Evaluates a term that reduces to type Bool.
-- Displays the result as a Maybe 𝔹.
--
evalBool : ∀ {e} → (te : • ⨟ ∘ ⊢ e ⦂ Bool) → ℕ → Maybe 𝔹
evalBool te fuel with eval te fuel
... | just v  = toBool v
... | nothing = nothing

--
-- Converts a ℕ into a Term.
--
natLit : ℕ → Term
natLit zero = Zero
natLit (suc n) = Suc (natLit n)

--
-- Creates a type judgment for a ℕ literal.
--
natLitTy : ∀ n → • ⨟ ∘ ⊢ natLit n ⦂ Nat
natLitTy zero    = τ-zero
natLitTy (suc n) = τ-suc (natLitTy n)

-- Natural Number addition.
Nat⇒Nat⇒Nat : τ
Nat⇒Nat⇒Nat = Nat ⇒ Nat ⇒ Nat

Nat⇒Nat : τ
Nat⇒Nat = Nat ⇒ Nat

add : Term
add = Fix Nat⇒Nat⇒Nat 
        (Lam 
          (Lam 
            (If (Zero? (Var 1))
                       (Var 0)
                       (Suc (App (App (Var 2) (Pred (Var 1))) (Var 0))))))

addτ : • ⨟ ∘ ⊢ add ⦂ Nat ⇒ Nat ⇒ Nat
addτ = 
  τ-fix 
    (ty-arr
      ty-nat 
      (ty-arr ty-nat ty-nat)) 
    (τ-lam 
      ty-nat 
      (τ-lam ty-nat 
        (τ-if 
          (τ-zero? (τ-var ty-nat refl)) 
          (τ-var ty-nat refl)
          (τ-suc 
            (τ-app 
              (τ-app 
                (τ-var (ty-arr ty-nat (ty-arr ty-nat ty-nat)) refl) 
                (τ-pred (τ-var ty-nat refl)))
              (τ-var ty-nat refl))))))

add34 : Term
add34 = App (App add (natLit 3)) (natLit 4)

add34τ : • ⨟ ∘ ⊢ add34 ⦂ Nat
add34τ = τ-app (τ-app addτ (natLitTy 3)) (natLitTy 4)

evalAdd34 : Maybe ℕ
evalAdd34 = evalNat add34τ 100 -- Should return just 7

-- Natural number multiplication.
mul : Term
mul =
  Fix Nat⇒Nat⇒Nat
    (Lam
      (Lam
        (If (Zero? (Var 1))
            Zero
            (App (App add (Var 0))
                 (App (App (Var 2) 
                           (Pred (Var 1))) 
                      (Var 0))))))
          
mulτ : • ⨟ ∘ ⊢ mul ⦂ Nat ⇒ Nat ⇒ Nat
mulτ =
  τ-fix
    (ty-arr ty-nat (ty-arr ty-nat ty-nat))
    (τ-lam
      ty-nat
      (τ-lam
        ty-nat
        (τ-if
          (τ-zero? (τ-var ty-nat refl))
          τ-zero
          (τ-app
            (τ-app (weaken-closed addτ) 
                   (τ-var ty-nat refl))
            (τ-app
              (τ-app
                (τ-var (ty-arr ty-nat (ty-arr ty-nat ty-nat)) refl)
                (τ-pred (τ-var ty-nat refl)))
              (τ-var ty-nat refl))))))

-- Factorial over natural numbers.
fact : Term
fact = 
  Fix Nat⇒Nat
    (Lam
      (If (Zero? (Var 0))
          (Suc Zero)
          (App (App mul (Var 0)) 
               (App (Var 1) 
                    (Pred (Var 0))))))

factτ : • ⨟ ∘ ⊢ fact ⦂ Nat ⇒ Nat
factτ =
  τ-fix
    (ty-arr ty-nat ty-nat)
    (τ-lam
      ty-nat
      (τ-if
        (τ-zero? (τ-var ty-nat refl))
        (τ-suc τ-zero)
        (τ-app
          (τ-app (weaken-closed mulτ) -- (* n (! n-1))
                  (τ-var ty-nat refl))
          (τ-app
            (τ-var (ty-arr ty-nat ty-nat) refl)
            (τ-pred (τ-var ty-nat refl))))))

fact5 : Term
fact5 = App fact (natLit 5)

fact5τ : • ⨟ ∘ ⊢ fact5 ⦂ Nat
fact5τ = τ-app factτ (natLitTy 5)

fib : Term
fib =
  Fix Nat⇒Nat
    (Lam
      (If (Zero? (Var 0))
          Zero
          (If (Zero? (Pred (Var 0)))
              (Suc Zero)
              (App (App add (App (Var 1) (Pred (Var 0))))
                   (App (Var 1) 
                        (Pred (Pred (Var 0))))))))

fibτ : • ⨟ ∘ ⊢ fib ⦂ Nat ⇒ Nat
fibτ =
  τ-fix
    (ty-arr ty-nat ty-nat)
    (τ-lam
      ty-nat
      (τ-if
        (τ-zero? (τ-var ty-nat refl))
        τ-zero
        (τ-if
          (τ-zero? (τ-pred (τ-var ty-nat refl)))
          (τ-suc τ-zero)
          (τ-app
            (τ-app (weaken-closed addτ)
                    (τ-app (τ-var (ty-arr ty-nat ty-nat) refl) (τ-pred (τ-var ty-nat refl))))
            (τ-app (τ-var (ty-arr ty-nat ty-nat) refl)
                    (τ-pred (τ-pred (τ-var ty-nat refl))))))))

fib10 : Term
fib10 = App fib (natLit 10)
fib10τ : • ⨟ ∘ ⊢ fib10 ⦂ Nat
fib10τ = τ-app fibτ (natLitTy 10)


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