module Types where

--
-- Types for now are booleans and natural numbers.
-- 
data τ : Set where
    ℕ : τ
    𝔹 : τ
    _×_ : τ → τ → τ

