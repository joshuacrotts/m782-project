module theorems.lemmas.3a-term-var-subst where

open import SystemF.definitions
open import theorems.lemmas.0-math
open import theorems.lemmas.1a-term-env
open import theorems.lemmas.1b-type
open import theorems.lemmas.2a-weakening


subst-τ : ∀ {Δ Γ i τ₁ τ₂ body v} →
                 (size Γ ≡ i) →
                 (Δ ⨟ (τ₁ ∷ Γ) ⊢ body ⦂ τ₂) →
                 (• ⨟ ∘ ⊢ v ⦂ τ₁) →
                 (Δ ⨟ Γ ⊢ (β body v i) ⦂ τ₂)
subst-τ |Γ|≡i (τ-true) vTy          = τ-true
subst-τ |Γ|≡i (τ-false) vTy         = τ-false
subst-τ |Γ|≡i (τ-zero) vTy          = τ-zero
subst-τ |Γ|≡i (τ-unit) vTy          = τ-unit
subst-τ |Γ|≡i (τ-suc τ₁) vTy        = τ-suc (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-pred τ₁) vTy       = τ-pred (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-zero? τ₁) vTy      = τ-zero? (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-if τ₁ τ₂ τ₃) vTy   = τ-if (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy) (subst-τ |Γ|≡i τ₃ vTy)
subst-τ |Γ|≡i (τ-cons τ₁ τ₂) vTy    = τ-cons (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy)
subst-τ |Γ|≡i (τ-fst τ₁×₂) vTy      = τ-fst (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-snd τ₁×₂) vTy      = τ-snd (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-app fTy eTy) vTy   = τ-app (subst-τ |Γ|≡i fTy vTy) (subst-τ |Γ|≡i eTy vTy)
subst-τ |Γ|≡i (τ-inl ΔTy τ₁) vTy    = τ-inl ΔTy (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-inr ΔTy τ₂) vTy    = τ-inr ΔTy (subst-τ |Γ|≡i τ₂ vTy)
subst-τ |Γ|≡i (τ-nil τ) vTy           = τ-nil τ
subst-τ |Γ|≡i (τ-nil? τ) vTy        = τ-nil? (subst-τ |Γ|≡i τ vTy)
subst-τ |Γ|≡i (τ-lcons τ₁ τ₂) vTy   = τ-lcons (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy)
subst-τ |Γ|≡i (τ-first τ) vTy       = τ-first (subst-τ |Γ|≡i τ vTy)
subst-τ |Γ|≡i (τ-rest τ) vTy        = τ-rest (subst-τ |Γ|≡i τ vTy)
subst-τ {Δ₁} {Γ₁} {i} {τ₁} {τ₂} {body = Fix τ e} {v = v} |Γ|≡i
        (τ-fix {τ = τ} {e = e} ΔTy bodyTy) vTy = 
  let
    bodyTy' : Δ₁ ⨟ (τ₁ ∷ (Γ₁ ,, τ)) ⊢ e ⦂ τ
    bodyTy' =
      subst (λ Γ → Δ₁ ⨟ Γ ⊢ e ⦂ τ)
            (∷assoc {Γ = Γ₁} {τ₁ = τ₁} {τ₂ = τ})
            bodyTy

    -- under Fix binder, index increases
    ih : Δ₁ ⨟ (Γ₁ ,, τ) ⊢ β e v (suc i) ⦂ τ
    ih = subst-τ (cong suc |Γ|≡i) bodyTy' vTy
  in
    τ-fix ΔTy ih
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-var {Δ} {Γ'} {m} ΔTy lookupN) vTy with m ≡ᵇ i in eq
... | true  = 
    let m≡i = ≡ᵇ⇒≡ m i (subst T (sym eq) tt)
        lookupI1 = lookup-head {Γ} {τ₁} {i} |Γ|≡i
        lookupI2 = subst (λ z → lookup z (τ₁ ∷ Γ) ≡ just τ₂)  m≡i lookupN 
        τ₁≡τ₂ = just-injective (trans (sym lookupI1) lookupI2)
        ΔΓvTy = weaken-closed vTy
    in subst (λ z → Δ ⨟ Γ ⊢ v ⦂ z) τ₁≡τ₂ ΔΓvTy
... | false =
    let m<|Γ'| = (lookup-size {Γ'} {m} lookupN)
        m≤|Γ| = <suc⇒≤ (subst (λ z → m < z) (size-head {Γ} {τ₁}) m<|Γ'|)
        m≢|Γ| = subst (λ z → m ≢ z) (sym |Γ|≡i) (≢ᵇ⇒≢ {m} {i} eq)
        m<|Γ| = ≤∧≢⇒< m≤|Γ| m≢|Γ|
        lookup-Γ-m = lookup-rest {Γ} {τ₁} {m} m<|Γ|
    in τ-var ΔTy (trans (sym lookup-Γ-m) lookupN)
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-lam {Γ'} {τ₃} {τ₄} ΔTy bodyTy) vTy  = 
    τ-lam ΔTy (subst-τ (cong suc |Γ|≡i) bodyTy vTy)
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-case cTy lTy rTy) vTy  = 
    let cTy' = subst-τ |Γ|≡i cTy vTy
        lTy' = subst-τ (cong suc |Γ|≡i) lTy vTy
        rTy' = subst-τ (cong suc |Γ|≡i) rTy vTy
    in τ-case cTy' lTy' rTy'
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-lamT {Δ'} {Γ'} {τ₃} {e} bodyTy) vTy  = 
    let |Γ'|≡i = trans (|inc-Γ|≡|Γ| {Γ}) |Γ|≡i
        τ₁ty = τ-ty vTy
        incτ₁≡τ₁ = inc-τ-no-op z≤n τ₁ty
        bodyTy' = subst (λ z → Δ ,★ ⨟ z ⊢ e ⦂ τ₃) inc-Γ-∷ bodyTy 
        bodyTy'' = subst (λ z → Δ ,★ ⨟ z ∷ inc-Γ Γ ⊢ e ⦂ τ₃) incτ₁≡τ₁ bodyTy'
    in 
    τ-lamT (subst-τ |Γ'|≡i bodyTy'' vTy)
subst-τ |Γ|≡i (τ-appT ΔTy bodyTy) vTy = τ-appT ΔTy (subst-τ |Γ|≡i bodyTy vTy)



subst0-τ : ∀ {τ₁ τ₂ body v} →
            (• ⨟ ∘ ,, τ₁ ⊢ body ⦂ τ₂) →
            (• ⨟ ∘ ⊢ v ⦂ τ₁) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₂)
subst0-τ bodyTy vTy  = subst-τ refl bodyTy vTy


subst0-τ-inl : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ ,, τ₁ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inl v) ⦂ τ₁ ⨁ τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inl bodyTy vTy with vTy
... | τ-inl ΔTy vTy' = subst0-τ bodyTy vTy' 


subst0-τ-inr : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ ,, τ₂ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inr v) ⦂ τ₁ ⨁ τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inr bodyTy vTy with vTy
... | τ-inr ΔTy vTy' = subst0-τ bodyTy vTy' 

