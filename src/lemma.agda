{-# OPTIONS --allow-unsolved-metas #-}

module lemma where

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

open import SystemF.types
open import SystemF.terms
open import SystemF.values
open import SystemF.context
open import SystemF.typing
open import SystemF.semantics


-- Postulate for the lambda case (requires generalized substitution)

≢ᵇ⇒≢ : ∀ {m i} → (m ≡ᵇ i) ≡ false → m ≢ i
≢ᵇ⇒≢ {m} {i} p refl = subst T p (≡⇒≡ᵇ m m refl)

<suc⇒≤ : ∀ {m i} → m < suc i → m ≤ i
<suc⇒≤ {m} {i} m<sucI = ≤-pred m<sucI


Γ-weaken : ∀ {Δ Γ₁ Γ₂ e τ} → (Δ ⨟ Γ₂ ⊢ e ⦂ τ) → (Δ ⨟ (Γ₁ ++ Γ₂) ⊢ e ⦂ τ)
Γ-weaken τ-true = τ-true
Γ-weaken τ-false = τ-false
Γ-weaken τ-zero = τ-zero
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-suc τ₁)        = τ-suc (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-pred τ₁)       = τ-pred (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-zero? τ₁)      = τ-zero? (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-if τ₁ τ₂ τ₃)   = τ-if (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₂) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₃)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-cons τ₁ τ₂)    = τ-cons (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁) (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-fst τ₁×₂)      = τ-fst (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁×₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-snd τ₁×₂)      = τ-snd (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁×₂)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-app fTy eTy)   = τ-app (Γ-weaken {Δ} {Γ₁} {Γ₂} fTy) (Γ-weaken {Δ} {Γ₁} {Γ₂} eTy)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-appT ΔTy fTy)   = τ-appT ΔTy (Γ-weaken {Δ} {Γ₁} {Γ₂} fTy)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inl τ₁)        = τ-inl (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inr τ2)        = τ-inr (Γ-weaken {Δ} {Γ₁}{ Γ₂} τ2)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) =
  let
    aa = concat-append {Γ₁} {Γ₂} {τ}
    bb = Γ-weaken {Δ} {Γ₁} {Γ₂ , τ} bodyTy
  in
    τ-fix ΔTy (subst (λ z → Δ ⨟ z ⊢ e ⦂ τ) aa bb)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-var lookupN)   = τ-var (lookup-concat  {Γ₁} {Γ₂} lookupN)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₃} (τ-case {Δ} {Γ₂} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) =
    let left   = concat-append {Γ₁} {Γ₂} {leftTy} in
    let right  = concat-append {Γ₁} {Γ₂} {rightTy} in
    let leftW  = (Γ-weaken {Δ} {Γ₁} {Γ₂ , leftTy} τ₁) in
    let rightW = (Γ-weaken {Δ} {Γ₁} {Γ₂ , rightTy} τ₂) in
    τ-case (Γ-weaken {Δ} {Γ₁} {Γ₂} e')
           (subst (λ z → Δ ⨟ z ⊢ el ⦂ τ₃) left leftW)
           (subst (λ z → Δ ⨟ z ⊢ er ⦂ τ₃) right rightW)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₁} (τ-lam {Δ} {Γ} {τ₃} {τ₄} {e'} ΔTy bodyTy) = 
    let aa = concat-append {Γ₁} {Γ₂} {τ₃}
        bb = Γ-weaken {Δ} {Γ₁} {Γ , τ₃} bodyTy
    in τ-lam ΔTy (subst (λ z → Δ ⨟ z ⊢ e' ⦂ τ₄) aa bb)
Γ-weaken {Δ} {Γ₁} {Γ₂} {e} {τ₁} (τ-lamT {Δ} {Γ} {τ₂} {e'} bodyTy) = 
    τ-lamT (Γ-weaken {Δ ,★} {Γ₁} {Γ₂ } bodyTy)
    



ty-weaken : ∀ {Δ₁ Δ₂ τ} → (Δ₂ ⊢ τ ty) → ((Δ₁ ++' Δ₂) ⊢ τ ty)
ty-weaken ty-unit = ty-unit
ty-weaken ty-nat = ty-nat
ty-weaken ty-bool = ty-bool
ty-weaken {Δ₁} {Δ₂} (ty-var lookupN) = {!   !}
ty-weaken {Δ₁} {Δ₂} (ty-prod τ₁ τ₂) = ty-prod (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-sum τ₁ τ₂) = ty-sum (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-arr τ₁ τ₂) = ty-arr (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-all τ) = ty-all {!   !}


Δ-weaken : ∀ {Δ₁ Δ₂ Γ e τ} → (Δ₂ ⨟ Γ ⊢ e ⦂ τ) → ((Δ₁ ++' Δ₂) ⨟ Γ ⊢ e ⦂ τ) 
Δ-weaken τ-true = τ-true
Δ-weaken τ-false = τ-false
Δ-weaken τ-zero = τ-zero
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-suc τ₁) = τ-suc (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-pred τ₁) = τ-pred (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-zero? τ₁) = τ-zero? (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-if τ₁ τ₂ τ₃) = τ-if (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₃)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-cons τ₁ τ₂) = τ-cons (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁) (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-fst τ₁×₂) = τ-fst (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁×₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-snd τ₁×₂) = τ-snd (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁×₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-app fTy eTy) = τ-app (Δ-weaken {Δ₁} {Δ₂} {Γ} fTy) (Δ-weaken {Δ₁} {Δ₂} {Γ} eTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-appT ΔTy bodyTy) = τ-appT (ty-weaken ΔTy) (Δ-weaken {Δ₁} {Δ₂} {Γ} bodyTy)
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inl τ₁) = τ-inl (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inr τ₂) = τ-inr (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-fix {Δ} {Γ} {τ} {e} bodyTy) = τ-fix (Δ-weaken {Δ₁} {Δ₂} {Γ , τ} bodyTy)
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-var lookupN) = τ-var lookupN
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-case {Δ} {Γ₂} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) = {!   !}
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lam {Δ'} {Γ'} {τ₁} ΔTy bodyTy) = τ-lam ΔTy (Δ-weaken {Δ₁} {Δ₂} {Γ , τ₁} bodyTy)
-- Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lamT {Δ'} {Γ'} {τ₁} {e} bodyTy) = τ-lamT ?
Δ-weaken _ = {!   !}


ΔΓ-weaken : ∀ {Δ₁ Δ₂ Γ₁ Γ₂ e τ} → (Δ₂ ⨟ Γ₂ ⊢ e ⦂ τ) → ((Δ₁ ++' Δ₂) ⨟ (Γ₁ ++ Γ₂) ⊢ e ⦂ τ)
ΔΓ-weaken {Δ₁} {Δ₂} {Γ₁} {Γ₂} eTy = Δ-weaken {Δ₁} {Δ₂} {Γ₁ ++ Γ₂} (Γ-weaken {Δ₂} {Γ₁} {Γ₂} eTy)


--
-- If we have closed term (∘ ⊢ e ⦂ τ), we can weaken it to any context Γ.
--
weaken-closed : ∀ {Δ Γ e τ} → (• ⨟ ∘ ⊢ e ⦂ τ) → (Δ ⨟ Γ ⊢ e ⦂ τ)
weaken-closed {Δ} {Γ} {e} {τ} te =
  let Δ'Γ' = ΔΓ-weaken {Δ} {•} {Γ} {∘} te
      ΔΓ' = subst (λ z → z ⨟ (Γ ++ ∘) ⊢ e ⦂ τ) (concat-id' Δ) Δ'Γ'
      ΔΓ = subst (λ z → Δ ⨟ z ⊢ e ⦂ τ) (concat-id Γ) ΔΓ'
  in ΔΓ



subst-τ : ∀ {Δ Γ i τ₁ τ₂ body v} →
                 (size Γ ≡ i) →
                 (Δ ⨟ (τ₁ ∷ Γ) ⊢ body ⦂ τ₂) →
                 (• ⨟ ∘ ⊢ v ⦂ τ₁) →
                 (Δ ⨟ Γ ⊢ (β body v i) ⦂ τ₂)
subst-τ |Γ|≡i (τ-true) vTy          = τ-true
subst-τ |Γ|≡i (τ-false) vTy         = τ-false
subst-τ |Γ|≡i (τ-zero) vTy          = τ-zero
subst-τ |Γ|≡i (τ-suc τ₁) vTy        = τ-suc (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-pred τ₁) vTy       = τ-pred (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-zero? τ₁) vTy      = τ-zero? (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-if τ₁ τ₂ τ₃) vTy   = τ-if (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy) (subst-τ |Γ|≡i τ₃ vTy)
subst-τ |Γ|≡i (τ-cons τ₁ τ₂) vTy    = τ-cons (subst-τ |Γ|≡i τ₁ vTy) (subst-τ |Γ|≡i τ₂ vTy)
subst-τ |Γ|≡i (τ-fst τ₁×₂) vTy      = τ-fst (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-snd τ₁×₂) vTy      = τ-snd (subst-τ |Γ|≡i τ₁×₂ vTy)
subst-τ |Γ|≡i (τ-app fTy eTy) vTy   = τ-app (subst-τ |Γ|≡i fTy vTy) (subst-τ |Γ|≡i eTy vTy)
subst-τ |Γ|≡i (τ-inl τ₁) vTy        = τ-inl (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-inr τ₂) vTy        = τ-inr (subst-τ |Γ|≡i τ₂ vTy)
subst-τ {Δ₁} {Γ₁} {i} {τ₁} {τ₂} {body = Fix τ e} {v = v} |Γ|≡i
        (τ-fix {τ = τ} {e = e} ΔTy bodyTy) vTy = 
  let
    bodyTy' : Δ₁ ⨟ (τ₁ ∷ (Γ₁ , τ)) ⊢ e ⦂ τ
    bodyTy' =
      subst (λ Γ → Δ₁ ⨟ Γ ⊢ e ⦂ τ)
            (∷assoc {Γ = Γ₁} {τ₁ = τ₁} {τ₂ = τ})
            bodyTy

    -- under Fix binder, index increases
    ih : Δ₁ ⨟ (Γ₁ , τ) ⊢ β e v (suc i) ⦂ τ
    ih = subst-τ (cong suc |Γ|≡i) bodyTy' vTy
  in
    τ-fix ΔTy ih
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-var {Δ} {Γ'} {m} lookupN) vTy with m ≡ᵇ i in eq
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
    in τ-var (trans (sym lookup-Γ-m) lookupN)
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-lam {Γ'} {τ₃} {τ₄} ΔTy bodyTy) vTy  = 
    τ-lam ΔTy (subst-τ (cong suc |Γ|≡i) bodyTy vTy)
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-case cTy lTy rTy) vTy  = 
    let cTy' = subst-τ |Γ|≡i cTy vTy
        lTy' = subst-τ (cong suc |Γ|≡i) lTy vTy
        rTy' = subst-τ (cong suc |Γ|≡i) rTy vTy
    in τ-case cTy' lTy' rTy'
subst-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} {v} |Γ|≡i (τ-lamT {Δ'} {Γ'} {τ₃} bodyTy) vTy  =  
    τ-lamT (subst-τ |Γ|≡i  bodyTy vTy)
subst-τ |Γ|≡i (τ-appT ΔTy bodyTy) vTy = τ-appT ΔTy (subst-τ |Γ|≡i bodyTy vTy)



subst0-τ : ∀ {τ₁ τ₂ body v} →
            (• ⨟ ∘ , τ₁ ⊢ body ⦂ τ₂) →
            (• ⨟ ∘ ⊢ v ⦂ τ₁) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₂)
subst0-τ bodyTy vTy  = subst-τ refl bodyTy vTy


subst0-τ-inl : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ , τ₁ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inl v) ⦂ τ₁ + τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inl bodyTy vTy with vTy
... | τ-inl vTy' = subst0-τ bodyTy vTy' 


subst0-τ-inr : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ , τ₂ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inr v) ⦂ τ₁ + τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inr bodyTy vTy with vTy
... | τ-inr vTy' = subst0-τ bodyTy vTy' 





subst'-τ : ∀ {Δ Γ i τ₁ τ₂ body} →
                 (Δ ≡ i) →
                 (Δ ,★ ⨟ Γ ⊢ body ⦂ τ₂) →
                 (Δ ⨟ Γ ⊢ (β' body τ₁ i) ⦂ τ₂)
subst'-τ _ _  = {!   !}


subst0'-τ : ∀ {τ₁ τ₂ body} →
            (• ,★ ⨟ ∘ ⊢ body ⦂ τ₂) →
            (• ⨟ ∘ ⊢ body [ τ₁ ]' ⦂ τ₂)
subst0'-τ bodyTy  = subst'-τ refl bodyTy 