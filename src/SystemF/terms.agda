open import SystemF.Types
open import Data.Nat using (ℕ)

module SystemF.Terms where

--
-- Terms for now are booleans and natural numbers.
-- 
data Term : Set where
    var     : ℕ → Term
    lam     : Term → Term
    app     : Term → Term → Term
    true    : Term
    false   : Term
    zero    : Term
    suc     : Term → Term
    pred    : Term → Term
    zero?   : Term → Term
    if      : Term → Term → Term → Term
    cons    : Term → Term → Term
    fst     : Term → Term
    snd     : Term → Term
    -- inl     : Term → Term
    -- inr     : Term → Term
    -- case    : Term → Term → Term → Term

