module theorems.lemmas.2a-weakening where

open import SystemF.definitions
open import theorems.lemmas.0-math
open import theorems.lemmas.1a-term-env
open import theorems.lemmas.1b-type



Γ-weaken : ∀ {Δ Γ₁ Γ₂ e τ} → (Δ ⨟ Γ₂ ⊢ e ⦂ τ) → (Δ ⨟ (Γ₁ ++ Γ₂) ⊢ e ⦂ τ)
Γ-weaken τ-true = τ-true
Γ-weaken τ-false = τ-false
Γ-weaken τ-zero = τ-zero
Γ-weaken τ-unit = τ-unit 
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-suc τ₁)        = τ-suc (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-pred τ₁)       = τ-pred (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-zero? τ₁)      = τ-zero? (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-if τ₁ τ₂ τ₃)   = τ-if (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₂) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₃)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-cons τ₁ τ₂)    = τ-cons (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-fst τ₁×₂)      = τ-fst (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁×₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-snd τ₁×₂)      = τ-snd (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁×₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-app fTy eTy)   = τ-app (Γ-weaken {Δ} {Γ₁} {Γ₂} fTy) (Γ-weaken {Δ} {Γ₁} {Γ₂} eTy)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-appT ΔTy fTy)   = τ-appT ΔTy (Γ-weaken {Δ} {Γ₁} {Γ₂} fTy)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inl ΔTy τ₁)        = τ-inl ΔTy (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inr ΔTy τ2)        = τ-inr ΔTy (Γ-weaken {Δ} {Γ₁}{ Γ₂} τ2)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-nil τ) = τ-nil τ
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-nil? τ) = τ-nil? (Γ-weaken {Δ} {Γ₁} {Γ₂} τ)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-lcons τ₁ τ₂) = τ-lcons (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-first τ₁) = τ-first (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-rest τ₁) = τ-rest (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)

Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) =
  let
    aa = concat-append {Γ₁} {Γ₂} {τ}
    bb = Γ-weaken {Δ} {Γ₁} {Γ₂ ,, τ} bodyTy
  in
    τ-fix ΔTy (subst (λ z → Δ ⨟ z ⊢ e ⦂ τ) aa bb)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-var ΔTy lookupN)   = τ-var ΔTy (lookup-concat  {Γ₁} {Γ₂} lookupN)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₃} (τ-case {Δ} {Γ₂} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) =
    let left   = concat-append {Γ₁} {Γ₂} {leftTy} in
    let right  = concat-append {Γ₁} {Γ₂} {rightTy} in
    let leftW  = (Γ-weaken {Δ} {Γ₁} {Γ₂ ,, leftTy} τ₁) in
    let rightW = (Γ-weaken {Δ} {Γ₁} {Γ₂ ,, rightTy} τ₂) in
    τ-case (Γ-weaken {Δ} {Γ₁} {Γ₂} e')
           (subst (λ z → Δ ⨟ z ⊢ el ⦂ τ₃) left leftW)
           (subst (λ z → Δ ⨟ z ⊢ er ⦂ τ₃) right rightW)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₁} (τ-lam {Δ} {Γ} {τ₃} {τ₄} {e'} ΔTy bodyTy) = 
    let aa = concat-append {Γ₁} {Γ₂} {τ₃}
        bb = Γ-weaken {Δ} {Γ₁} {Γ ,, τ₃} bodyTy
    in τ-lam ΔTy (subst (λ z → Δ ⨟ z ⊢ e' ⦂ τ₄) aa bb)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₁} (τ-lamT {Δ} {Γ} {τ₂} {e'} bodyTy) = 
    let inc-Γ₁Γ₂ = inc-Γ-distr {Γ₁} {Γ₂}
        bodyTy' = Γ-weaken {Δ ,★} {inc-Γ Γ₁} {inc-Γ Γ₂} bodyTy
    in τ-lamT (subst (λ z → Δ ,★ ⨟ z ⊢ e' ⦂ τ₂) (sym inc-Γ₁Γ₂) bodyTy')
    -- Γ-weaken {Δ ,★} {Γ₁} {Γ₂ } bodyTy)


Δ-weaken : ∀ {Δ₁ Δ₂ Γ e τ} → (Δ₂ ⨟ Γ ⊢ e ⦂ τ) → ((Δ₁ ++' Δ₂) ⨟ Γ ⊢ e ⦂ τ) 
Δ-weaken τ-true = τ-true
Δ-weaken τ-false = τ-false
Δ-weaken τ-zero = τ-zero
Δ-weaken τ-unit = τ-unit
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-suc τ₁) = τ-suc (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-pred τ₁) = τ-pred (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-zero? τ₁) = τ-zero? (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-if τ₁ τ₂ τ₃) = τ-if (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₃)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-cons τ₁ τ₂) = τ-cons (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-fst τ₁×₂) = τ-fst (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁×₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-snd τ₁×₂) = τ-snd (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁×₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-app fTy eTy) = τ-app (Δ-weaken {Δ₁} {Δ₂} {Γ} fTy) (Δ-weaken {Δ₁} {Δ₂} {Γ} eTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-appT ΔTy bodyTy) = τ-appT (ty-weaken ΔTy) (Δ-weaken {Δ₁} {Δ₂} {Γ} bodyTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inl ΔTy τ₁) = τ-inl (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inr ΔTy τ₂) = τ-inr (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-nil τ) = τ-nil (ty-weaken τ)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-nil? e) = τ-nil? (Δ-weaken {Δ₁} {Δ₂} {Γ} e)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lcons τ₁ τ₂) = τ-lcons (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-first τ₁) = τ-first (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-rest τ₁) = τ-rest (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) = τ-fix (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ ,, τ} bodyTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-var ΔTy lookupN) = τ-var (ty-weaken ΔTy) lookupN
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-case {Δ} {Γ₂} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) = 
    τ-case (Δ-weaken {Δ₁} {Δ₂} {Γ} e')
           (Δ-weaken {Δ₁} {Δ₂} {Γ ,, leftTy} τ₁)
           (Δ-weaken {Δ₁} {Δ₂} {Γ ,, rightTy} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lam {Δ'} {Γ'} {τ₁} ΔTy bodyTy) = τ-lam (ty-weaken ΔTy) (Δ-weaken {Δ₁} {Δ₂} {Γ ,, τ₁} bodyTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lamT {Δ'} {Γ'} {τ₁} {e} bodyTy) = 
    let 
        aa = (Δ-weaken {Δ₁} bodyTy)
        bb = Δ₁++'Δ₂,★ {Δ₁} {Δ₂}
    in τ-lamT ( subst (λ z → z ⨟ inc-Γ Γ ⊢ e ⦂ τ₁) (sym bb) aa)



ΔΓ-weaken : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ e τ} → (Δ₂ ⨟ Γ₂ ⊢ e ⦂ τ) → ((Δ₁ ++' Δ₂) ⨟ (Γ₁ ++ Γ₂) ⊢ e ⦂ τ)
ΔΓ-weaken {Δ₁} {Δ₂} {Γ₁} {Γ₂} eTy = Δ-weaken {Δ₁} {Δ₂} {Γ₁ ++ Γ₂} (Γ-weaken {Δ₂} {Γ₁} {Γ₂} eTy)


weaken-closed : ∀ {Δ Γ e τ} → (• ⨟ ∘ ⊢ e ⦂ τ) → (Δ ⨟ Γ ⊢ e ⦂ τ)
weaken-closed {Δ} {Γ} {e} {τ} te =
  let Δ'Γ' = ΔΓ-weaken {Δ} {•} {Γ} {∘} te
      ΔΓ' = subst (λ z → z ⨟ (Γ ++ ∘) ⊢ e ⦂ τ) (concat-id' Δ) Δ'Γ'
      ΔΓ = subst (λ z → Δ ⨟ z ⊢ e ⦂ τ) (concat-id Γ) ΔΓ'
  in ΔΓ
