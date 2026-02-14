module eval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

import SystemF.context as C
open C using (Context; ∘; lookup) -- Don't bring _,_ into scope to avoid name clashes

-- eval partial function, use n steps to limit evaluation depth
eval : ∀ {e τ} → (te : ∘ ⊢ e ⦂ τ) → ℕ → Maybe Term
eval te zero = nothing
eval {e = e} te (suc n) with progress te
... | inj₁ v = just e
... | inj₂ (e' , step) = eval (preservation te step) n


t : Term
t = (Snd (App (Lam (Cons (Var 0) (Var 0))) Zero))

-- ((lambda (x) (cons x x)) zero)
-- (cons zero zero)

tTy : ∘ ⊢ t ⦂ Nat
tTy = (τ-snd (τ-app (τ-lam (τ-cons (τ-var refl) (τ-var refl))) τ-zero))

-- now you can run:
test : Maybe Term
test = eval tTy 200

t2 : Term
t2 = Case (Inr (Suc Zero))
          (Suc Zero)
          Zero

t2Ty : ∘ ⊢ t2 ⦂ Nat
t2Ty =
  τ-case
    (τ-inr {τ1 = Nat} {τ2 = Nat} (τ-suc τ-zero))
    (τ-suc τ-zero)
    τ-zero

eval2 : Maybe Term
eval2 = eval t2Ty 200
