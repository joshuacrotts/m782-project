open import SystemF.Types
open import SystemF.Terms

module SystemF.Context where


--
-- Term Context for typing.
-- 
infixl 5 _,_⦂_

data Context : Set where
    ∘ : Context
    _,_⦂_ : Context → Variable → τ → Context

