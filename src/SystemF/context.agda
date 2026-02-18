module SystemF.context where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z<s; s<s; s≤s; _<ᵇ_)
open import Data.Nat.Properties using (≤-pred; <⇒<ᵇ)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym; cong)
open import Function using (case_of_)

open import SystemF.types
open import SystemF.terms


--
-- Term TermContext for typing.
-- 
infixl 5 _,_

data TermContext : Set where
    ∘ : TermContext
    _,_ : TermContext → τ → TermContext


infixr 4 _∷_
_∷_ : τ → TermContext → TermContext
_∷_ τ ∘ = ∘ , τ
_∷_ τ (Γ , τ') = (τ ∷ Γ) , τ'



infixr 4 _++_
_++_ : TermContext → TermContext → TermContext
_++_ ∘ Γ  = Γ
_++_ (Γ₁ , τ) Γ₂  = Γ₁ ++ (τ ∷ Γ₂ )



lookup : ℕ → TermContext → Maybe τ
lookup _ ∘             = nothing 
lookup zero (Γ , τ)    = just τ
lookup (suc n) (Γ , τ) = lookup n Γ


size : TermContext → ℕ
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




-- The type context in System F is simply a count of how many
-- type variables are in scope (de Bruijn indexed).
TypeContext : Set
TypeContext = ℕ

-- Empty type context
• : TypeContext
• = zero

★ : TypeContext
★ = suc •

-- Extend the type context with a new type variable
infixl 5 _,★
_,★ : TypeContext → TypeContext
_,★ = suc


infixl 5 ★++_
★++_ : TypeContext → TypeContext
★++_ = suc


infixr 4 _++'_
_++'_ : TypeContext → TypeContext → TypeContext
_++'_ zero Δ₂ = Δ₂
_++'_ (suc Δ₁) Δ₂ = suc (Δ₁ ++' Δ₂)




lookup' : ℕ → TypeContext → Maybe τ
lookup' n Δ with n <ᵇ Δ
... | true  = just (TVar n)
... | false = nothing 


concat-id' : ∀ (Δ) →  (Δ ++' •) ≡ Δ
concat-id' zero = refl
concat-id' (suc Δ) = cong suc (concat-id' Δ)


lookup'-down : ∀ {n Δ} → lookup' (suc n) (suc Δ) ≡ just (TVar (suc n)) → lookup' n Δ ≡ just (TVar n)
lookup'-down {n} {Δ} eq with n <ᵇ Δ
... | true = refl
... | false = case eq of λ ()

lookup'-size : ∀ {Δ n} → lookup' n Δ ≡ just (TVar n) → n < Δ
lookup'-size {zero} lookupN = case lookupN of λ ()
lookup'-size {suc Δ} {zero} _ = z<s
lookup'-size {suc Δ} {suc n} lookupN = s<s (lookup'-size {Δ} {n} (lookup'-down {n} {Δ} lookupN))



lookup'-rest : ∀ {Δ i} → i < Δ → lookup' i Δ ≡ just (TVar i)
lookup'-rest {Δ} {i} i<|Δ| with i <ᵇ Δ | <⇒<ᵇ i<|Δ|
... | true  | _ = refl
... | false | ()