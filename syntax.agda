module Syntax where

open import Terms
open import Types

-- Typing judgments--

infix 4 ⊢_∶_

data ⊢_∶_ : Term → τ → Set where

    --
    -- ---------------------------
    --      true has type 𝔹
    τ-true : ⊢ true ∶ 𝔹

    --
    -- ---------------------------
    --      false has type 𝔹
    τ-false : ⊢ false ∶ 𝔹

    --
    -- ---------------------------
    --      zero : nat
    τ-zero : ⊢ zero ∶ ℕ

    --        e : ℕ
    -- ---------------------------
    --      suc(e) : ℕ
    τ-suc : ∀ {e} → (⊢ e ∶ ℕ) → (⊢ suc e ∶ ℕ)

    --        e : ℕ
    -- ---------------------------
    --      pred(e) : ℕ
    τ-pred : ∀ {e} → (⊢ e ∶ ℕ) → (⊢ pred e ∶ ℕ)

    --        e : ℕ
    -- ---------------------------
    --      zero?(e) : 𝔹
    τ-zero? : ∀ {e} → (⊢ e ∶ ℕ) → (⊢ zero? e ∶ 𝔹)

    --   e1 : 𝔹   e2 : τ    e3 : τ
    -- ---------------------------
    --      if e1 e2 e3 : τ
    τ-if : ∀ {e1 e2 e3 τ} → (⊢ e1 ∶ 𝔹) → (⊢ e2 ∶ τ) → (⊢ e3 ∶ τ) → (⊢ if e1 e2 e3 ∶ τ)

