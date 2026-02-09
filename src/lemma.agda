module Lemma where

-- open import Context

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Bool using (true; false; T)
open import Data.Bool.Properties using (T?)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; sym; cong)
open import Function using (case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import SystemF.Types
open import SystemF.Terms
open import SystemF.Values
open import SystemF.Context
open import SystemF.Typing
open import SystemF.Semantics




-- fresh-nothing : ∀ (Γ : Context) (x : ℕ) → fresh? x Γ ≡ true → lookup x Γ ≡ nothing
-- fresh-nothing ∘ _ _ = refl
-- fresh-nothing (Γ ,[ y ⦂ _ ]) x fresh with x ≡ᵇ y
-- ... | false = fresh-nothing Γ x fresh


-- weakening : ∀ {Γ x y τ₁ τ₂} → (fresh? x Γ ≡ true) → 
--             (lookup y Γ ≡ just τ₁) → (lookup y (Γ ,[ x ⦂ τ₂ ]) ≡ just τ₁) 

-- weakening {Γ} {x} {y} {τ₁} {τ₂} fresh lookupY with y ≡ᵇ x in eq
-- ... | false = lookupY
-- ... | true = let y≡x = ≡ᵇ⇒≡ y x (subst T (sym eq) tt)
--                  lookup-X-just = subst (λ z → lookup z Γ ≡ just τ₁) y≡x lookupY
--                  lookup-X-nothing = fresh-nothing Γ x fresh
--                  just-is-nothing = (trans (sym lookup-X-just) lookup-X-nothing)
--              in  case just-is-nothing of (λ ())


-- Postulate for the lambda case (requires generalized substitution)




≢ᵇ⇒≢ : ∀ {m i} → (m ≡ᵇ i) ≡ false → m ≢ i
≢ᵇ⇒≢ {m} {i} p refl = subst T p (≡⇒≡ᵇ m m refl)

<suc⇒≤ : ∀ {m i} → m < suc i → m ≤ i
<suc⇒≤ {m} {i} m<sucI = ≤-pred m<sucI


τ-weakening : ∀ {Γ₁ Γ₂ e τ}  → (Γ₂ ⊢ e ⦂ τ) → ((Γ₁ ++ Γ₂) ⊢ e ⦂ τ)
τ-weakening τ-true = τ-true
τ-weakening τ-false = τ-false
τ-weakening τ-zero = τ-zero
τ-weakening {Γ₁} {Γ₂} (τ-suc τ₁) = τ-suc (τ-weakening {Γ₁} {Γ₂} τ₁)
τ-weakening {Γ₁} {Γ₂} (τ-pred τ₁) = τ-pred (τ-weakening {Γ₁} {Γ₂} τ₁)
τ-weakening {Γ₁} {Γ₂} (τ-zero? τ₁) = τ-zero? (τ-weakening {Γ₁} {Γ₂} τ₁)
τ-weakening {Γ₁} {Γ₂} (τ-if τ₁ τ₂ τ₃) = τ-if (τ-weakening {Γ₁} {Γ₂} τ₁) (τ-weakening {Γ₁} {Γ₂} τ₂) (τ-weakening {Γ₁} {Γ₂} τ₃)
τ-weakening {Γ₁} {Γ₂} (τ-cons τ₁ τ₂) = τ-cons (τ-weakening {Γ₁} {Γ₂} τ₁) (τ-weakening {Γ₁} {Γ₂} τ₂)
τ-weakening {Γ₁} {Γ₂} (τ-fst τ₁×₂) = τ-fst (τ-weakening {Γ₁} {Γ₂} τ₁×₂)
τ-weakening {Γ₁} {Γ₂} (τ-snd τ₁×₂) = τ-snd (τ-weakening {Γ₁} {Γ₂} τ₁×₂)
τ-weakening {Γ₁} {Γ₂} (τ-app fTy eTy) = τ-app (τ-weakening {Γ₁} {Γ₂} fTy) (τ-weakening {Γ₁} {Γ₂} eTy)
τ-weakening {Γ₁} {Γ₂} (τ-var lookupN) = τ-var (lookup-concat  {Γ₁} {Γ₂} lookupN)
τ-weakening {Γ₁} {Γ₂} {e} {τ₁} (τ-lam {Γ} {τ₃} {τ₄} {e'} bodyTy) = 
    let aa = concat-append {Γ₁} {Γ₂} {τ₃}
        bb = τ-weakening {Γ₁} {Γ , τ₃} bodyTy
    in τ-lam (subst (λ z → z ⊢ e' ⦂ τ₄) aa bb)



subst-τ : ∀ {Γ i τ₁ τ₂ body v} →
                 (size Γ ≡ i) →
                 ((τ₁ ∷ Γ) ⊢ body ⦂ τ₂) →
                 (∘ ⊢ v ⦂ τ₁) →
                 (Γ ⊢ (β body v i) ⦂ τ₂)
subst-τ |Γ|≡i (τ-true) vTy = τ-true
subst-τ |Γ|≡i (τ-false) vTy = τ-false
subst-τ |Γ|≡i (τ-zero) vTy = τ-zero
subst-τ |Γ|≡i (τ-suc τ₁) vTy = τ-suc (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-pred τ₁) vTy = τ-pred (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-zero? τ₁) vTy = τ-zero? (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-if τ₁ τ₂ τ₃) vTy = τ-if (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy) (subst-τ |Γ|≡i τ₃ vTy)
subst-τ |Γ|≡i (τ-cons τ₁ τ₂) vTy = τ-cons (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy)
subst-τ |Γ|≡i (τ-fst τ₁×₂) vTy = τ-fst (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-snd τ₁×₂) vTy = τ-snd (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-app fTy eTy) vTy = τ-app (subst-τ |Γ|≡i fTy vTy) (subst-τ |Γ|≡i eTy vTy)
subst-τ {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-var {Γ'} {m} lookupN) vTy with m ≡ᵇ i in eq
... | true  = 
    let m≡i = ≡ᵇ⇒≡ m i (subst T (sym eq) tt)
        lookupI1 = lookup-head {Γ} {τ₁} {i} |Γ|≡i
        lookupI2 = subst (λ z → lookup z (τ₁ ∷ Γ) ≡ just τ₂)  m≡i lookupN 
        τ₁≡τ₂ = just-injective (trans (sym lookupI1) lookupI2)
        ΓvTy =  subst (λ z → z ⊢ v ⦂ τ₁) (concat-id Γ) (τ-weakening {Γ} {∘} vTy)
    in subst (λ z → Γ ⊢ v ⦂ z) τ₁≡τ₂ ΓvTy
... | false =
    let m<|Γ'| = (lookup-size {Γ'} {m} lookupN)
        m≤|Γ| = <suc⇒≤ (subst (λ z → m < z) (size-head {Γ} {τ₁}) m<|Γ'|)
        m≢|Γ| = subst (λ z → m ≢ z) (sym |Γ|≡i) (≢ᵇ⇒≢ {m} {i} eq)
        m<|Γ| = ≤∧≢⇒< m≤|Γ| m≢|Γ|
        lookup-Γ-m = lookup-rest {Γ} {τ₁} {m} m<|Γ|
    in τ-var (trans (sym lookup-Γ-m) lookupN)
subst-τ {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-lam {Γ'} {τ₃} {τ₄} bodyTy) vTy  = 
    τ-lam  (subst-τ (cong suc |Γ|≡i) bodyTy vTy)
    




subst0-τ : ∀ {τ₁ τ₂ body v} →
            (∘ , τ₁ ⊢ body ⦂ τ₂) →
            (∘ ⊢ v ⦂ τ₁) →
            (∘ ⊢ body [ v ] ⦂ τ₂)
subst0-τ bodyTy vTy  = subst-τ refl bodyTy vTy

