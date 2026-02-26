module SystemF.typing where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc; pred; _≡ᵇ_; _<ᵇ_)

open import SystemF.terms
open import SystemF.types
open import SystemF.context


-- Typing judgments--

infix 4 _⊢_ty

data _⊢_ty : TypeContext → τ → Set where

  ty-unit : ∀ {Δ} → Δ ⊢ Unit ty
  ty-nat : ∀ {Δ} → Δ ⊢ Nat ty
  ty-bool : ∀ {Δ} → Δ ⊢ Bool ty
  ty-var : ∀ {Δ n} → lookup' n Δ ≡ just (TVar n) → Δ ⊢ TVar n ty
  ty-prod : ∀ {Δ τ1 τ2} → Δ ⊢ τ1 ty → Δ ⊢ τ2 ty → Δ ⊢ (τ1 × τ2) ty
  ty-sum : ∀ {Δ τ1 τ2} → Δ ⊢ τ1 ty → Δ ⊢ τ2 ty → Δ ⊢ (τ1 ⨁ τ2) ty
  ty-arr : ∀ {Δ τ1 τ2} → Δ ⊢ τ1 ty → Δ ⊢ τ2 ty → Δ ⊢ (τ1 ⇒ τ2) ty
  ty-all : ∀ {Δ τ} → Δ ,★ ⊢ τ ty → Δ ⊢ (∀' τ) ty


inc-Γ : TermContext → TermContext 
inc-Γ ∘ = ∘
inc-Γ (Γ , τ) = (inc-Γ Γ) , (inc-τ τ)


βᵧ : TermContext → τ → ℕ → TermContext
βᵧ ∘ τ₂ i = ∘
βᵧ (Γ , τ₁) τ₂ i = (βᵧ Γ τ₂ i) , (β# τ₁ τ₂ i)

infix 4 _⨟_⊢_⦂_

data _⨟_⊢_⦂_ : TypeContext → TermContext → Term → τ → Set where

    -- 
    -- ---------------------------
    -- Δ ⨟ Γ, x ⊢ x ⦂ τ
    -- nameless vars
    τ-var :           ∀ {Δ Γ n τ} → 
            Δ ⊢ τ ty →
            lookup n Γ ≡ just τ → Δ ⨟ Γ ⊢ Var n ⦂ τ

    --
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ true ⦂ Bool
    τ-true : ∀ {Δ Γ} → 
            (Δ ⨟ Γ ⊢ True ⦂ Bool)

    --
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ false ⦂ Bool
    τ-false : ∀ {Δ Γ} → 
             (Δ ⨟ Γ ⊢ False ⦂ Bool)

    --
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ zero ⦂ Nat
    τ-zero : ∀ {Δ Γ} → 
            (Δ ⨟ Γ ⊢ Zero ⦂ Nat)

    --        Δ ⨟ Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ suc(e) ⦂ Nat
    τ-suc : ∀ {Δ Γ e} → 
      (Δ ⨟ Γ ⊢ e ⦂ Nat) → 
      (Δ ⨟ Γ ⊢ Suc e ⦂ Nat)

    --        Δ ⨟ Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ pred(e) ⦂ Nat
    τ-pred : ∀ {Δ Γ e} →
       (Δ ⨟ Γ ⊢ e ⦂ Nat) → 
       (Δ ⨟ Γ ⊢ Pred e ⦂ Nat)

    --        Δ ⨟ Γ ⊢ e ⦂ Nat
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ zero?(e) ⦂ Bool
    τ-zero? : ∀ {Δ Γ e} → 
        (Δ ⨟ Γ ⊢ e ⦂ Nat) → 
        (Δ ⨟ Γ ⊢ Zero? e ⦂ Bool)

    --  Δ ⨟ Γ ⊢ e1 ⦂ Bool  
    --  Δ ⨟ Γ ⊢ e2 ⦂ τ 
    --  Δ ⨟ Γ ⊢ e3 ⦂ τ
    -- ---------------------------
    --     Δ ⨟ Γ ⊢ if e1 e2 e3 ⦂ τ
    τ-if : ∀ {Δ Γ e1 e2 e3 τ} → 
            (Δ ⨟ Γ ⊢ e1 ⦂ Bool) → 
               (Δ ⨟ Γ ⊢ e2 ⦂ τ) → 
               (Δ ⨟ Γ ⊢ e3 ⦂ τ) → 
               (Δ ⨟ Γ ⊢ If e1 e2 e3 ⦂ τ)

    --  Δ ⨟ Γ ⊢ e1 ⦂ τ₁  
    --  Δ ⨟ Γ ⊢ e2 ⦂ τ₂
    -- ---------------------------
    --  Δ ⨟ Γ ⊢ cons e1 e2 ⦂ τ₁ × τ₂
    τ-cons : ∀ {Δ Γ e1 e2 τ1 τ2} → 
                 (Δ ⨟ Γ ⊢ e1 ⦂ τ1) → 
                 (Δ ⨟ Γ ⊢ e2 ⦂ τ2) → 
                 (Δ ⨟ Γ ⊢ Cons e1 e2 ⦂ τ1 × τ2)

    --   Δ ⨟ Γ ⊢ e ⦂ τ₁ × τ₂
    -- ---------------------------
    --     Δ ⨟ Γ ⊢ fst e ⦂ τ₁
    τ-fst : ∀ {Δ Γ e τ1 τ2} → 
        (Δ ⨟ Γ ⊢ e ⦂ τ1 × τ2) → 
        (Δ ⨟ Γ ⊢ Fst e ⦂ τ1)

    --      e ⦂ τ₁ × τ₂
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ snd e ⦂ τ₂
    τ-snd : ∀ {Δ Γ e τ1 τ2} → 
        (Δ ⨟ Γ ⊢ e ⦂ τ1 × τ2) → 
        (Δ ⨟ Γ ⊢ Snd e ⦂ τ2)

    --   Δ ⨟ Γ , τ1 ⊢ e ⦂ τ2
    -- ---------------------------
    --  Δ ⨟ Γ ⊢ lam e ⦂ τ1 ⇒ τ2
    τ-lam : ∀ {Δ Γ τ1 τ2 e } → 
         Δ ⊢ τ1 ty →
         (Δ ⨟ Γ , τ1 ⊢ e ⦂ τ2) → 
         (Δ ⨟ Γ ⊢ (Lam e) ⦂ τ1 ⇒ τ2)

    -- Δ ⨟ Γ ⊢ f ⦂ τ1 ⇒ τ2   Δ ⨟ Γ ⊢ e ⦂ τ1
    -- ---------------------------
    --  Δ ⨟ Γ ⊢ f e ⦂ τ2
    τ-app : ∀ {Δ Γ f e τ1 τ2} → 
          (Δ ⨟ Γ ⊢ f ⦂ τ1 ⇒ τ2) → 
               (Δ ⨟ Γ ⊢ e ⦂ τ1) → 
               (Δ ⨟ Γ ⊢ App f e ⦂ τ2)

    --         Δ ⨟ Γ ⊢ e ⦂ τ₁         
    -- ---------------------------
    --     Δ ⨟ Γ ⊢ inl e ⦂ τ₁ ⨁ τ₂
    τ-inl : ∀ {Δ Γ e τ1 τ2} → 
            Δ ⊢ τ2 ty → 
             (Δ ⨟ Γ ⊢ e ⦂ τ1) → 
             (Δ ⨟ Γ ⊢ Inl e ⦂ τ1 ⨁ τ2)
    
    --         Δ ⨟ Γ ⊢ e ⦂ τ₂         
    -- ---------------------------
    --      Δ ⨟ Γ ⊢ inr e ⦂ τ₁ ⨁ τ₂
    τ-inr : ∀ {Δ Γ e τ1 τ2} →
             Δ ⊢ τ1 ty → 
             (Δ ⨟ Γ ⊢ e ⦂ τ2) → 
             (Δ ⨟ Γ ⊢ Inr e ⦂ τ1 ⨁ τ2)
    
    --  Δ ⨟ Γ ⊢ e ⦂ τ₁ ⨁ τ₂ 
    --  Δ ⨟ Γ ⊢ e1 ⦂ τ₃ 
    --  Δ ⨟ Γ ⊢ e2 ⦂ τ₃
    -- --------------------------------------
    --  Δ ⨟ Γ ⊢ case e of inl x ⇒ e1 | inr y ⇒ e2 ⦂ τ₃
    τ-case : ∀ {Δ Γ τₗ τᵣ τ e eₗ eᵣ } → 
                  (Δ ⨟ Γ ⊢ e ⦂ τₗ ⨁ τᵣ) → 
                  (Δ ⨟ Γ , τₗ ⊢ eₗ ⦂ τ) → 
                  (Δ ⨟ Γ , τᵣ ⊢ eᵣ ⦂ τ) → 
                  (Δ ⨟ Γ ⊢ Case e eₗ eᵣ ⦂ τ)

    --      Δ ⨟ Γ , τ ⊢ e ⦂ τ 
    -- --------------------------------------
    --     Δ ⨟ Γ ⊢ fix τ e ⦂ τ
    τ-fix : ∀ {Δ Γ τ e} → 
      Δ ⊢ τ ty →
      (Δ ⨟ Γ , τ ⊢ e ⦂ τ) → 
      (Δ ⨟ Γ ⊢ Fix τ e ⦂ τ)


    --      Δ ,α ⨟ Γ  ⊢ e ⦂ τ 
    -- --------------------------------------
    --     Δ ⨟ Γ ⊢ lamT τ e ⦂ ∀' τ
    τ-lamT : ∀ {Δ Γ τ e} → 
      (Δ ,★ ⨟ (inc-Γ Γ) ⊢ e ⦂ τ) → 
      (Δ ⨟ Γ ⊢ LamT e ⦂ ∀' τ)

    --  Δ ⊢ τ₂ ty    Δ ⨟ Γ ⊢ f ⦂ ∀' τ₁
    -- --------------------------------------
    --     Δ ⨟ Γ ⊢ AppT f τ₂ ⦂ τ₁ #[ τ₂ ]
    τ-appT : ∀ {Δ Γ f τ1 τ2} →    
          Δ ⊢ τ2 ty →
          (Δ ⨟ Γ ⊢ f ⦂ ∀' τ1) →  
          (Δ ⨟ Γ ⊢ AppT f τ2 ⦂ τ1 #[ τ2 ])