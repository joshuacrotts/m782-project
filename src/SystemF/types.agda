module SystemF.types where

open import Data.Nat using (ℕ; suc; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (true; false)

infixr 6 _⇒_
infixr 7 _×_
infixr 5 ∀'_

--
-- System F types: includes type variables (de Bruijn indexed),
-- universal quantification (∀τ), and standard base/compound types.
--
data τ : Set where
    Unit   : τ
    Nat    : τ
    Bool   : τ
    TVar   : ℕ → τ        -- type variable (de Bruijn index)
    _×_    : τ → τ → τ
    _⨁_    : τ → τ → τ
    _⇒_    : τ → τ → τ
    ∀'_    : τ → τ         -- ∀α. body  (α is implicitly index 0 in body)
    List   : τ → τ        -- List type constructor



inc-τ-i : τ → ℕ → τ
inc-τ-i Unit _ = Unit
inc-τ-i Nat _ = Nat
inc-τ-i Bool _ = Bool
inc-τ-i (TVar n) i with n <ᵇ i
... | true  = TVar n
... | false = TVar (suc n)
inc-τ-i (τ1 × τ2) i = (inc-τ-i τ1 i) × (inc-τ-i τ2 i)
inc-τ-i (τ1 ⨁ τ2) i = (inc-τ-i τ1 i) ⨁ (inc-τ-i τ2 i)
inc-τ-i (τ1 ⇒ τ2) i = (inc-τ-i τ1 i) ⇒ (inc-τ-i τ2 i)
inc-τ-i (∀' τ1) i = ∀' (inc-τ-i τ1 (suc i))
inc-τ-i (List τ1) i = List (inc-τ-i τ1 i)


inc-τ : τ → τ
inc-τ t = inc-τ-i t 0


-- Type substitution: β σ n τ  replaces TVar n with σ in τ
β# : τ → τ → ℕ → τ
β# Unit σ n = Unit
β# Nat σ n = Nat
β# Bool σ n = Bool
β# (TVar m) σ n with m ≡ᵇ n | m <ᵇ n
... | true  | _ = σ
... | false | true  = TVar m 
... | false | false = TVar (pred m) 
β# (τ₁ × τ₂) σ n = (β# τ₁ σ n) × (β# τ₂ σ n)
β# (τ₁ ⨁ τ₂) σ n = (β# τ₁ σ n) ⨁ (β# τ₂ σ n)
β# (τ₁ ⇒ τ₂) σ n = (β# τ₁ σ n) ⇒ (β# τ₂ σ n)
β# (∀' τ₁) σ n = ∀' (β# τ₁ (inc-τ σ) (suc n))
β# (List τ₁) σ n = List (β# τ₁ σ n)




infixl 5 _#[_]

_#[_] : τ → τ → τ
t #[ σ ] = β# t σ 0

