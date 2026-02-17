module SystemF.terms where

open import Data.Nat using (ℕ)

open import SystemF.types

--
-- Terms for now are booleans and natural numbers.
-- 
data Term : Set where
    ⋆       : Term
    Var     : ℕ → Term
    Lam     : Term → Term
    App     : Term → Term → Term
    True    : Term
    False   : Term
    Zero    : Term
    Suc     : Term → Term
    Pred    : Term → Term
    Zero?   : Term → Term
    If      : Term → Term → Term → Term
    Cons    : Term → Term → Term
    Fst     : Term → Term
    Snd     : Term → Term
    Inl     : Term → Term
    Inr     : Term → Term
    Case    : Term → Term → Term → Term
    Fix     : τ → Term → Term
    LamT    : Term → Term
    AppT    : Term → τ → Term

