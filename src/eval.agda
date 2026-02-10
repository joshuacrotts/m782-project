module Eval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


open import SystemF.Terms
open import SystemF.Types
import SystemF.Context as C
open C using (Context; ∘; lookup) -- Don't bring _,_ into scope to avoid name clashes
open import SystemF.Typing
open import SystemF.Values
open import SystemF.Semantics
open import SystemF.Typing
open import Progress
open import Preservation

-- eval partial function, use n steps to limit evaluation depth
eval : ∀ {e τ} → (te : ∘ ⊢ e ⦂ τ) → ℕ → Maybe Term
eval te zero = nothing
eval {e = e} te (suc n) with progress te
... | inj₁ v = just e
... | inj₂ (e' , step) = eval (preservation te step) n


t : Term
t = (App (Lam (Cons (Var 0) (Var 0))) Zero)

-- ((lambda (x) (cons x x)) zero)
-- (cons zero zero)

tTy : ∘ ⊢ t ⦂ Nat × Nat
tTy = (τ-app (τ-lam (τ-cons (τ-var refl) (τ-var refl))) τ-zero)

-- now you can run:
test : Maybe Term
test = eval tTy 200