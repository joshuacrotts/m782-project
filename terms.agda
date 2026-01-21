module Terms where

--
-- Terms for now are booleans and natural numbers.
-- 
data Term : Set where
    true : Term
    false : Term
    zero : Term
    suc : Term → Term
    pred : Term → Term
    zero? : Term → Term
    if : Term → Term → Term → Term
    cons : Term → Term → Term
    fst : Term → Term
    snd : Term → Term