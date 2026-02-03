module SystemF.Types where

--
-- Types for now are booleans and natural numbers.
-- 
data τ : Set where
    Nat    : τ
    Bool   : τ
    _×_    : τ → τ → τ
    -- _+_    : τ → τ → τ
    _⇒_    : τ → τ → τ


