module SystemF.types where

open import Data.Nat using (ℕ; suc; _≡ᵇ_)
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
    _+_    : τ → τ → τ
    _⇒_    : τ → τ → τ
    ∀'_    : τ → τ         -- ∀α. body  (α is implicitly index 0 in body)
    List   : τ → τ        -- List type constructor




-- Type substitution: β σ n τ  replaces TVar n with σ in τ
β# : τ → τ → ℕ → τ
β# Unit σ n = Unit
β# Nat σ n = Nat
β# Bool σ n = Bool
β# (TVar m) σ n with m ≡ᵇ n
... | true  = σ
... | false = TVar m
β# (τ₁ × τ₂) σ n = (β# τ₁ σ n) × (β# τ₂ σ n)
β# (τ₁ + τ₂) σ n = (β# τ₁ σ n) + (β# τ₂ σ n)
β# (τ₁ ⇒ τ₂) σ n = (β# τ₁ σ n) ⇒ (β# τ₂ σ n)
β# (∀' τ₁) σ n = ∀' (β# τ₁ σ (suc n))
β# (List τ₁) σ n = List (β# τ₁ σ n)

infixl 5 _#[_]

_#[_] : τ → τ → τ
t #[ σ ] = β# t σ 0
