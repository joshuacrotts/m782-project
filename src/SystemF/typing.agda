module SystemF.Typing where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import SystemF.Terms
open import SystemF.Types
open import SystemF.Context

-- Typing judgments--

infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → τ → Set where

    -- --
    -- -- ---------------------------
    -- --  Γ, τ ⊢ zero ⦂ τ
    -- nameless vars
    τ-var : ∀ {Γ n τ} → lookup n Γ ≡ just τ → Γ ⊢ Var n ⦂ τ

    --
    -- ---------------------------
    --      true has type 𝔹
    τ-true : ∀ {Γ} → (Γ ⊢ True ⦂ Bool)

    --
    -- ---------------------------
    --      false has type 𝔹
    τ-false : ∀ {Γ} → (Γ ⊢ False ⦂ Bool)

    --
    -- ---------------------------
    --      Γ ⊢ zero ⦂ Nat
    τ-zero : ∀ {Γ} → (Γ ⊢ Zero ⦂ Nat)

    --        Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Γ ⊢ suc(e) ⦂ Nat
    τ-suc : ∀ {Γ e} → (Γ ⊢ e ⦂ Nat) → (Γ ⊢ Suc e ⦂ Nat)

    --        Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Γ ⊢ pred(e) ⦂ Nat
    τ-pred : ∀ {Γ e} → (Γ ⊢ e ⦂ Nat) → (Γ ⊢ Pred e ⦂ Nat)

    --        Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Γ ⊢ zero?(e) ⦂ Bool
    τ-zero? : ∀ {Γ e} → (Γ ⊢ e ⦂ Nat) → (Γ ⊢ Zero? e ⦂ Bool)

    --   e1 ⦂ Bool   e2 ⦂ τ    e3 ⦂ τ
    -- ---------------------------
    --      if e1 e2 e3 ⦂ τ
    τ-if : ∀ {Γ e1 e2 e3 τ} → (Γ ⊢ e1 ⦂ Bool) → (Γ ⊢ e2 ⦂ τ) → (Γ ⊢ e3 ⦂ τ) → (Γ ⊢ If e1 e2 e3 ⦂ τ)

    --  e1 ⦂ τ₁   e2 ⦂ τ₂
    -- ---------------------------
    --      cons e1 e2 ⦂ τ₁ × τ₂
    τ-cons : ∀ {Γ e1 e2 τ1 τ2} → (Γ ⊢ e1 ⦂ τ1) → (Γ ⊢ e2 ⦂ τ2) → (Γ ⊢ Cons e1 e2 ⦂ τ1 × τ2)

    --      e ⦂ τ₁ × τ₂
    -- ---------------------------
    --      fst e ⦂ τ₁
    τ-fst : ∀ {Γ e τ1 τ2} → (Γ ⊢ e ⦂ τ1 × τ2) → (Γ ⊢ Fst e ⦂ τ1)

    --      e ⦂ τ₁ × τ₂
    -- ---------------------------
    --      snd e ⦂ τ₂
    τ-snd : ∀ {Γ e τ1 τ2} → (Γ ⊢ e ⦂ τ1 × τ2) → (Γ ⊢ Snd e ⦂ τ2)

    --   Γ, τ1 → e ⦂ τ2
    -- ---------------------------
    --  Γ ⊢ lam e ⦂ τ1 ⇒ τ2
    τ-lam : ∀ {Γ τ1 τ2 e } →  (Γ , τ1 ⊢ e ⦂ τ2) → (Γ ⊢ (Lam e) ⦂ τ1 ⇒ τ2)

    -- -- Γ ⊢ f ⦂ τ1 ⇒ τ2   Γ ⊢ e ⦂ τ1
    -- -- ---------------------------
    -- --  Γ ⊢ f e ⦂ τ2
    τ-app : ∀ {Γ f e τ1 τ2} → (Γ ⊢ f ⦂ τ1 ⇒ τ2) → (Γ ⊢ e ⦂ τ1) → (Γ ⊢ App f e ⦂ τ2)

    --         Γ ⊢ e ⦂ τ₁         
    -- ---------------------------
    --      Γ ⊢ inl e ⦂ τ₁ + τ₂
    τ-inl : ∀ {Γ e τ1 τ2} → (Γ ⊢ e ⦂ τ1) → (Γ ⊢ Inl e ⦂ τ1 + τ2)
    
    --         Γ ⊢ e ⦂ τ₂         
    -- ---------------------------
    --      Γ ⊢ inr e ⦂ τ₁ + τ₂
    τ-inr : ∀ {Γ e τ1 τ2} → (Γ ⊢ e ⦂ τ2) → (Γ ⊢ Inr e ⦂ τ1 + τ2)
    
    --
    --
    --      e ⦂ τ₁ + τ₂   e1 ⦂ τ₃   e2 ⦂ τ₃
    -- --------------------------------------
    --      case e of inl x ⇒ e1 | inr y ⇒ e2 ⦂ τ₃
    τ-case : ∀ {Γ e eₗ eᵣ τₗ τᵣ τ}  → 
                  (Γ ⊢ e ⦂ τₗ + τᵣ)  → 
                  (Γ , τₗ ⊢ eₗ ⦂ τ) → 
                  (Γ , τᵣ ⊢ eᵣ ⦂ τ) → 
                  (Γ ⊢ Case e eₗ eᵣ ⦂ τ)