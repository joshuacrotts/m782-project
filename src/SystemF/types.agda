module SystemF.types where

infixr 6 _⇒_
infixr 7 _×_

--
-- Types for now are booleans and natural numbers.
-- 
data τ : Set where
    Nat    : τ
    Bool   : τ
    _×_    : τ → τ → τ
    _+_    : τ → τ → τ
    _⇒_    : τ → τ → τ


