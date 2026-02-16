module SystemF.semantics where

------------------------------------------------------------------------
-- Small-step semantics
------------------------------------------------------------------------

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; pred; _>_; _≡ᵇ_; _<ᵇ_)
open import Function.Base using (case_of_)

open import SystemF.types
open import SystemF.terms
open import SystemF.values

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

-- subst : body [v / x] -> body'
-- subst : body -> v -> x -> body'
-- x is the de Bruijn index of the variable to be substituted
-- When substituting at index n:
--   - Var m where m = n  →  s (substitute)
--   - Var m where m < n  →  Var m (unchanged, bound by outer binder)
-- 
-- β (Case sum left right) s n = Case (β sum s n) (β left s (suc n)) (β right s (suc n))
-- The behavior of Case is
-- (1) evaluate the sum expression
-- (2) if the result matches the inl case, substitute the value into the left branch
-- (3) if the result matches the inr case, substitute the value into the right branch
-- The sum expression corresponds to the function argument,
-- while the two branches correspond to the function body. 
-- This means Case expression introduces one more binder for the two branches, 
-- but not for the sum expression.
-- Hence, we only increment the index for the left and right branches, but not for the sum expression.

β : Term → Term → ℕ → Term
β (Var m) s n with m ≡ᵇ n 
... | true  = s
... | false = Var m
β (Lam t) s n               = Lam (β t s (suc n)) 
β (App t u) s n             = App (β t s n) (β u s n)
β True s n                  = True   
β False s n                 = False
β Zero s n                  = Zero
β (Suc t) s n               = Suc (β t s n)
β (Pred t) s n              = Pred (β t s n)
β (Zero? t) s n             = Zero? (β t s n)
β (If t u v) s n            = If (β t s n) (β u s n) (β v s n)
β (Cons t u) s n            = Cons (β t s n) (β u s n)
β (Fst t) s n               = Fst (β t s n)
β (Snd t) s n               = Snd (β t s n)
β (Inl t) s n               = Inl (β t s n)
β (Inr t) s n               = Inr (β t s n)
β (Case sum left right) s n = Case (β sum s n) (β left s (suc n)) (β right s (suc n))
β (Fix τ t) s n             = Fix τ (β t s (suc n))

infixl 5 _[_]

_[_] : Term → Term →  Term
t [ s ] = β t s 0


infix 3 _↦_

data _↦_ : Term → Term → Set where
    ---------- Computation rules ----------
    -- 
    -- -------------------------------
    --       Zero?(Zero) ↦ True
    ss-zero? : Zero? (Zero) ↦ True

    --           v Valτ Nat
    -- -------------------------------
    --      Zero?(Suc(v)) ↦ False
    ss-zero?-suc : ∀ {v} → Valτ Nat v → Zero?(Suc(v)) ↦ False

    -- 
    -- -------------------------------
    --       If True e2 e3 ↦ e2
    ss-if-true : ∀ {e2 e3} → If True e2 e3 ↦ e2

    -- 
    -- -------------------------------
    --       If False e2 e3 ↦ e3
    ss-if-false : ∀ {e2 e3} → If False e2 e3 ↦ e3

    --          
    -- -------------------------------
    --     pred(Zero) ↦ Zero
    ss-pred-zero : Pred (Zero) ↦ Zero

    --           v Valτ Nat
    -- -------------------------------
    --      pred(Suc(v)) ↦ v
    ss-pred-suc : ∀ {v} → Valτ Nat v → Pred (Suc(v)) ↦ v

    --   v1 Valτ τ1    v2 Valτ τ2
    -- -----------------------------
    --  fst (cons v1 v2) ↦ v1
    ss-fst : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → Fst (Cons v1 v2) ↦ v1

    --   v1 Valτ τ1    v2 Valτ τ2
    -- -----------------------------
    --  snd (cons v1 v2) ↦ v2
    ss-snd : ∀ {τ1 τ2 v1 v2} → Valτ τ1 v1 → Valτ τ2 v2 → Snd (Cons v1 v2) ↦ v2


    ---------- Congruence rules ----------

    --           e1 ↦ e1'
    -- -------------------------------
    --   if e1 e2 e3 ↦ if e1' e2 e3
    ss-if-step : ∀ {e1 e1' e2 e3} → (e1 ↦ e1') → (If e1 e2 e3 ↦ If e1' e2 e3)

    --           e ↦ e'
    -- -------------------------------
    --     suc(e) ↦ suc(e')
    ss-suc-step : ∀ {e e'} → (e ↦ e') → (Suc e ↦ Suc e')

    --           e ↦ e'
    -- -------------------------------
    --     zero?(e) ↦ zero(e')
    ss-zero?-step : ∀ {e e'} → (e ↦ e') → (Zero? e ↦ Zero? e')

    --           e ↦ e'
    -- -------------------------------
    --    pred(e) ↦ pred(e')
    ss-pred-step : ∀ {e e'} → (e ↦ e') → (Pred e ↦ Pred e')

    --   e₁ ↦ e₁' 
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-left-step : ∀ {e₁ e₁' e₂} → (e₁ ↦ e₁') → (Cons e₁ e₂ ↦ Cons e₁' e₂)


    --   v val            e₂ ↦ e₂'
    -- -----------------------------
    --   cons e₁ e₂ ↦ cons e₁' e₂
    ss-cons-right-step :   ∀ {τ v e₂ e₂'} → Valτ τ v → (e₂ ↦ e₂') → Cons v e₂ ↦ Cons v e₂'

    --   e ↦ e'
    -- ----------------------------
    --     fst e ↦ fst e'
    ss-fst-step : ∀ {e e'} → (e ↦ e') → (Fst e ↦ Fst e')

    --  e ↦ e'
    -- ---------------------
    --     snd e ↦ snd e'
    ss-snd-step : ∀ {e e'} → (e ↦ e') → (Snd e ↦ Snd e')

    --   f ↦ f'
    -- ----------------------------
    --   app f e ↦ app f' e
    ss-app-func : ∀ {f f' e} → (f ↦ f') → (App f e ↦ App f' e)

    --   e ↦ e'
    -- ----------------------------
    --   app f e ↦ app f e'
    ss-app-arg : ∀ {f e e'} → (e ↦ e') → (App f e ↦ App f e')

    -- --   v1 val
    -- -- ----------------------------
    -- -- app (lam body) v1 ↦ body [v1 / x]
    ss-app-beta : ∀ {body v1 τ1} → Valτ τ1 v1 → App (Lam body) v1 ↦ body [ v1 ]

    --  e ↦ e'
    -- -----------------------------
    -- inl e ↦ inl e'
    ss-inl-step : ∀ {e e'} → (e ↦ e') → (Inl e ↦ Inl e')

    --  e ↦ e'
    -- -----------------------------
    -- inr e ↦ inr e'
    ss-inr-step : ∀ {e e'} → (e ↦ e') → (Inr e ↦ Inr e')

    -- e ↦ e'
    -- ----------------------------------------------------------
    -- case e [inl x ⇒ eₗ | inr y ⇒ eᵣ] ↦ case e' [inl x ⇒ eₗ | inr y ⇒ eᵣ]
    ss-case-step : ∀ {e e' eₗ eᵣ} → (e ↦ e') → (Case e eₗ eᵣ ↦ Case e' eₗ eᵣ)

    -- v val
    -- ----------------------------------------------------------
    -- case v [inl x ⇒ eₗ | inr y ⇒ eᵣ] ↦ eₗ [v / x]
    ss-case-inl : ∀ {v eₗ eᵣ τₗ} → Valτ τₗ v → Case (Inl v) eₗ eᵣ ↦ eₗ [ v ]

    -- v val
    -- ----------------------------------------------------------
    -- case v [inl x ⇒ eₗ | inr y ⇒ eᵣ] ↦ eᵣ [v / y]
    ss-case-inr : ∀ {v eₗ eᵣ τᵣ} → Valτ τᵣ v → Case (Inr v) eₗ eᵣ ↦ eᵣ [ v ]

    --
    -- --------------------------------------------------------
    --   fix τ e ↦ e [fix τ e / x]
    ss-fix : ∀ {τ e} → Fix τ e ↦ e [ Fix τ e ]
