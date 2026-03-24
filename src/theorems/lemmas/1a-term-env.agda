module theorems.lemmas.1a-term-env where

open import SystemF.definitions
open import theorems.lemmas.0-math


inc-Γ-∷ : ∀ {τ₁ Γ} → inc-Γ (τ₁ ∷ Γ) ≡ (inc-τ τ₁ ∷ inc-Γ Γ)
inc-Γ-∷ {τ₁} {∘} = refl
inc-Γ-∷ {τ₁} {Γ ,, τ'} = cong (λ x → x ,, inc-τ τ') (inc-Γ-∷ {τ₁} {Γ})

inc-Γ-distr : ∀ {Γ₁ Γ₂} → inc-Γ (Γ₁ ++ Γ₂) ≡ ((inc-Γ Γ₁) ++ (inc-Γ Γ₂))
inc-Γ-distr {∘} {Γ₂} = refl
inc-Γ-distr {Γ₁ ,, τ₁} {Γ₂} = trans (inc-Γ-distr {Γ₁} {τ₁ ∷ Γ₂}) (cong (λ x → (inc-Γ Γ₁) ++ x) (inc-Γ-∷ {τ₁} {Γ₂}))


|inc-Γ|≡|Γ| : ∀ {Γ} → size (inc-Γ Γ) ≡ size Γ
|inc-Γ|≡|Γ| {∘} = refl  
|inc-Γ|≡|Γ| {Γ ,, τ} = cong suc (|inc-Γ|≡|Γ| {Γ})



lookupᵧ : ∀ {Γ n i τ₁ τ₂} → lookup n Γ ≡ just τ₁ → lookup n (βᵧ Γ τ₂ i) ≡ just (β# τ₁ τ₂ i)
lookupᵧ {Γ} {n} {i} {τ₁} {τ₂} lookupN with Γ 
... | Γ' ,, τ₁' with n 
...             | zero  rewrite (just-injective lookupN) = refl
...             | suc n' = lookupᵧ {Γ'} {n'} {i} {τ₁} {τ₂} lookupN
    


