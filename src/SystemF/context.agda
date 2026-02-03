
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (Dec; yes; no)
open import SystemF.Types
open import SystemF.Terms

module SystemF.Context where


--
-- Term Context for typing.
-- 
infixl 5 _,_⦂_

data Context : Set where
    ∘ : Context
    _,_⦂_ : Context → Term → τ → Context

lookup : Term → Context → Maybe τ
lookup x ∘ = nothing 
lookup (var x) (Γ , (var y) ⦂ τ) with x ≟ y
... | yes _ = just τ
... | no _  = lookup (var x) Γ 
lookup _ _ = nothing