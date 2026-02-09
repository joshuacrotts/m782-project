open import Data.Nat using (ℕ)
open import SystemF.Types


module SystemF.Terms where

--
-- Terms for now are booleans and natural numbers.
-- 
data Term : Set where
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
    -- inl     : Term → Term
    -- inr     : Term → Term
    -- case    : Term → Term → Term → Term

