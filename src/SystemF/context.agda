module SystemF.context where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z<s; s<s; s≤s)
open import Data.Nat.Properties using (≤-pred)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym; cong)
open import Function using (case_of_)

open import SystemF.types
open import SystemF.terms


--
-- Term Context for typing.
-- 
infixl 5 _,_

data Context : Set where
    ∘ : Context
    _,_ : Context →  τ → Context


infixr 4 _∷_
_∷_ : τ → Context → Context
_∷_ τ ∘ = ∘ , τ
_∷_ τ (Γ , τ') = (τ ∷ Γ) , τ'



infixr 4 _++_
_++_ : Context → Context → Context
_++_ ∘ Γ  = Γ
_++_ (Γ₁ , τ) Γ₂  = Γ₁ ++ (τ ∷ Γ₂ )



lookup : ℕ → Context → Maybe τ
lookup _ ∘             = nothing 
lookup zero (Γ , τ)    = just τ
lookup (suc n) (Γ , τ) = lookup n Γ


size : Context → ℕ
size ∘ = zero
size (Γ , τ) = suc (size Γ)

∷assoc : ∀ {Γ τ₁ τ₂} → ((τ₁ ∷ Γ) , τ₂) ≡ (τ₁ ∷ (Γ , τ₂))
∷assoc {Γ} {τ₁} {τ₂} = refl

-- ++assoc : ∀ {Γ τ} → (Γ ++ (∘ , τ)) ≡ (Γ , τ)
-- ++assoc {Γ} with Γ
-- ... | ∘ = refl
-- ... | (Γ' , τ') = {!   !}


lookup-size : ∀ {Γ n τ} → lookup n Γ ≡ just τ → n < size Γ 
lookup-size {∘} {n} lookupN = case lookupN of λ ()
lookup-size {Γ , _} {zero} lookupN = z<s
lookup-size {Γ , _} {suc n} lookupN = s<s (lookup-size lookupN)

lookup-empty : ∀ {Γ n} → size Γ ≡ zero → lookup n Γ ≡ nothing
lookup-empty {Γ} size0 with Γ 
... | ∘ = refl
... | (Γ' , τ) = case size0 of λ () 

lookup-inc : ∀ {Γ n τ₁ τ₂} → lookup n Γ ≡ just τ₁ → lookup (suc n) (Γ , τ₂) ≡ just τ₁
lookup-inc lookupN = lookupN

lookup-head : ∀ {Γ τ₁ i} → size Γ ≡ i → lookup i (τ₁  ∷ Γ) ≡ just τ₁
lookup-head {Γ} {τ₁} {i} sizeΓ with Γ
... | ∘ rewrite (sym sizeΓ) = refl
... | (Γ' , τ₂) with sizeΓ
...                  | refl = lookup-head {Γ'} {τ₁} {size Γ'} refl


lookup-rest : ∀ {Γ τ₁ i} → i < size Γ → lookup i (τ₁  ∷ Γ) ≡ lookup i Γ
lookup-rest {Γ} {τ₁} {i} sizeΓ with Γ
... | ∘ = case sizeΓ of λ ()
... | (Γ' , τ₂) with i
...                  | zero = refl
...                  | suc n = lookup-rest (case sizeΓ of λ{ (s<s x) → x })


size-head : ∀ {Γ τ₁} → size (τ₁  ∷ Γ) ≡ suc (size Γ)
size-head {Γ} {τ₁} with Γ
... | ∘ = refl
... | (Γ' , τ₂) = cong suc (size-head {Γ'} {τ₁})



lookup-concat : ∀ {Γ₁ Γ₂ n τ₁} → lookup n Γ₂ ≡ just τ₁ → lookup n (Γ₁ ++ Γ₂) ≡ just τ₁
lookup-concat {Γ₁} {Γ₂} {n} {τ₁} lookupN with Γ₁ 
... | ∘  = lookupN
... | (Γ₃ , τ₂) =
    let Γ₄ = τ₂ ∷ Γ₂ 
        n<|Γ₂| = lookup-size {Γ₂} {n} {τ₁} lookupN
        Γ₄[n]≡Γ₂[n] = lookup-rest {Γ₂} {τ₂} n<|Γ₂|
        Γ₄[n]≡τ₁ = trans Γ₄[n]≡Γ₂[n] lookupN
    in lookup-concat {Γ₃} {Γ₄} {n} {τ₁} Γ₄[n]≡τ₁

concat-append : ∀ {Γ₁ Γ₂ τ₁} → (Γ₁ ++ (Γ₂ , τ₁)) ≡ ((Γ₁ ++ Γ₂) , τ₁)
concat-append {∘} = refl
concat-append {Γ₁ , τ₂} {Γ₂} {τ₁} = concat-append {Γ₁} {τ₂ ∷ Γ₂} {τ₁}

concat-id : ∀ (Γ) →  (Γ ++ ∘) ≡ Γ
concat-id ∘ = refl
concat-id (Γ , τ) = trans (concat-append {Γ} {∘} {τ}) (cong (_, τ) (concat-id Γ))