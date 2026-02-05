
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; zero; suc)
open import Relation.Nullary using (Dec; yes; no)
open import SystemF.Types
open import SystemF.Terms

module SystemF.Context where


--
-- Term Context for typing.
-- 
infixl 5 _,_

data Context : Set where
    ∘ : Context
    _,_ : Context → τ → Context

lookup : ℕ → Context → Maybe τ
lookup _ ∘              = nothing 
lookup zero (Γ , τ)     = just τ
lookup (suc n) (Γ , τ)  = lookup n Γ