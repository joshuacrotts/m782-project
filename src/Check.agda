module Check where

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Bool using (false)
open import Data.Nat.Properties using (≡ᵇ-false)
open import Relation.Binary.PropositionalEquality using (_≢_)

test : ∀ m n → m ≡ᵇ n ≡ false → m ≢ n
test m n p = ≡ᵇ-false p
