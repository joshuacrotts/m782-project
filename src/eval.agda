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
Nat⇒Nat⇒Nat⇒Nat : τ
Nat⇒Nat⇒Nat⇒Nat = Nat ⇒ Nat ⇒ Nat ⇒ Nat

Nat⇒Nat⇒Nat : τ
Nat⇒Nat⇒Nat = Nat ⇒ Nat ⇒ Nat

Nat⇒Nat : τ
Nat⇒Nat = Nat ⇒ Nat


addTR : Term
addTR =
  Fix Nat⇒Nat⇒Nat
    (Lam
      (Lam
        (If (Zero? (Var 1))
            (Var 0)
            (App (App (Var 2) (Pred (Var 1)))
                 (Suc (Var 0))))))   -- tail call: addTR (pred m) (suc acc)

addTRτ : • ⨟ ∘ ⊢ addTR ⦂ Nat ⇒ Nat ⇒ Nat
addTRτ =
  τ-fix
    (τ-lam
      (τ-lam
        (τ-if
          -- condition: zero? m
          (τ-zero? (τ-var {n = 1} refl))
          -- then: acc
          (τ-var {n = 0} refl)
          -- else: addTR (pred m) (suc acc)
          (τ-app
            (τ-app
              (τ-var {n = 2} refl)
              (τ-pred (τ-var {n = 1} refl)))
            (τ-suc (τ-var {n = 0} refl))))))


-- Natural number multiplication.
mul : Term
mul =
  Fix Nat⇒Nat⇒Nat
    (Lam
      (Lam
        (If (Zero? (Var 1))
            Zero
            (App (App addTR (Var 0))
                 (App (App (Var 2) 
                           (Pred (Var 1))) 
                      (Var 0))))))
          
mulτ : • ⨟ ∘ ⊢ mul ⦂ Nat ⇒ Nat ⇒ Nat
mulτ =
  τ-fix
    (τ-lam
      (τ-lam
        (τ-if
          (τ-zero? (τ-var refl))
          τ-zero
          (τ-app
            (τ-app (weaken-closed addTRτ) 
                   (τ-var refl))
            (τ-app
              (τ-app
                (τ-var refl)
                (τ-pred (τ-var refl)))
              (τ-var refl))))))

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
    (τ-lam
      (τ-if
        (τ-zero? (τ-var refl))
        (τ-suc τ-zero)
        (τ-app
          (τ-app (weaken-closed mulτ) -- (* n (! n-1))
                  (τ-var refl))
          (τ-app
            (τ-var refl)
            (τ-pred (τ-var refl))))))

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
              (App (App addTR (App (Var 1) (Pred (Var 0))))
                   (App (Var 1) 
                        (Pred (Pred (Var 0))))))))
fibτ : • ⨟ ∘ ⊢ fib ⦂ Nat ⇒ Nat
fibτ =
  τ-fix
    (τ-lam
      (τ-if
        (τ-zero? (τ-var refl))
        τ-zero
        (τ-if
          (τ-zero? (τ-pred (τ-var refl)))
          (τ-suc τ-zero)
          (τ-app
            (τ-app (weaken-closed addTRτ)
                    (τ-app (τ-var refl) (τ-pred (τ-var refl))))
            (τ-app (τ-var refl)
                    (τ-pred (τ-pred (τ-var refl))))))))

fib10 : Term
fib10 = App fib (natLit 10)
fib10τ : • ⨟ ∘ ⊢ fib10 ⦂ Nat
fib10τ = τ-app fibτ (natLitTy 10)

lengthℕ : Term
lengthℕ =
  Fix (List Nat ⇒ Nat)
    (Lam
      (If (Nil? (Var 0))
          Zero
          (Suc (App (Var 1) (Rest (Var 0))))))

lengthℕτ : • ⨟ ∘ ⊢ lengthℕ ⦂ List Nat ⇒ Nat
lengthℕτ =
  τ-fix
    (τ-lam
      (τ-if
        (τ-nil? (τ-var refl))
        τ-zero
        (τ-suc (τ-app (τ-var {n = 1} refl)
                      (τ-rest (τ-var refl))))))

length3 : Term
length3 = App lengthℕ (LCons (natLit 1) (LCons (natLit 2) (LCons (natLit 3) (Nil Nat))))
length3τ : • ⨟ ∘ ⊢ length3 ⦂ Nat
length3τ = τ-app lengthℕτ (τ-lcons (natLitTy 1) (τ-lcons (natLitTy 2) (τ-lcons (natLitTy 3) (τ-nil {τ = Nat}))))

val : Maybe ℕ
val = evalNat length3τ 1000


appendℕ : Term
appendℕ =
  Fix (List Nat ⇒ List Nat ⇒ List Nat)
    (Lam
      (Lam
        (If (Nil? (Var 1))
            (Var 0)
            (Case (First (Var 1))
              -- left branch: binder is Unit at Var 0, so ys is Var 1
              (Var 1)
              -- right branch: binder is x : Nat at Var 0
              (LCons (Var 0)
                (App (App (Var 3) (Rest (Var 2))) (Var 1)))))))


appendℕτ : • ⨟ ∘ ⊢ appendℕ ⦂ List Nat ⇒ List Nat ⇒ List Nat
appendℕτ =
  τ-fix
    (τ-lam
      (τ-lam
        (τ-if
          (τ-nil? (τ-var {n = 1} refl))
          (τ-var {n = 0} refl)
          (τ-case
            (τ-first (τ-var {n = 1} refl))      -- First xs : Unit + Nat
            (τ-var {n = 1} refl)                -- left branch returns ys
            (τ-lcons
              (τ-var {n = 0} refl)              -- x : Nat
              (τ-app
                (τ-app (τ-var {n = 3} refl)
                       (τ-rest (τ-var {n = 2} refl)))  -- Rest xs
                (τ-var {n = 1} refl)))))))      -- ys

append12to3 : Term
append12to3 = App (App appendℕ (LCons (natLit 1) (LCons (natLit 2) (Nil Nat)))) (LCons (natLit 3) (Nil Nat))
append12to3τ : • ⨟ ∘ ⊢ append12to3 ⦂ List Nat
append12to3τ = τ-app (τ-app appendℕτ (τ-lcons (natLitTy 1) (τ-lcons (natLitTy 2) (τ-nil {τ = Nat})))) (τ-lcons (natLitTy 3) (τ-nil {τ = Nat}))

