module theorems.lemmas.3c-type-var-subst where

open import SystemF.definitions
open import theorems.lemmas.0-math
open import theorems.lemmas.1a-term-env
open import theorems.lemmas.1b-type
open import theorems.lemmas.2a-weakening
open import theorems.lemmas.3b-type-subst



inc-Γᵧ : ∀ {Γ τ₁ i} → • ⊢ τ₁ ty → inc-Γ (βᵧ Γ τ₁ i) ≡ βᵧ (inc-Γ Γ) τ₁ (suc i)
inc-Γᵧ {∘} {τ₂} {i} •⊢τ₂ty = refl
inc-Γᵧ {Γ ,, τ₁} {τ₂} {i} •⊢τ₂ty  
    rewrite (inc-Γᵧ {Γ} {τ₂} {i} •⊢τ₂ty) rewrite (inc-τ-β≡ {τ₁} {τ₂} {i} {0} z≤n •⊢τ₂ty) 
    rewrite (inc-τ-no-op {j = 0} z≤n •⊢τ₂ty) 
    = refl
    
    


β#≡ : ∀ {τ₁ τ₂ τₐ Δ i j} →
     (Δ ≡ i) → (j ≤ Δ) → (suc (suc Δ) ⊢ τ₁ ty)  → (suc Δ ⊢ τ₂ ty)  → (• ⊢ τₐ ty)  →  
     β# (β# τ₁ τ₂ j) τₐ i ≡ β# (β# τ₁ τₐ (suc i)) (β# τ₂ τₐ i) j
β#≡ {τ₁} {τ₂} {τₐ} {Δ} {i} {j} Δ≡i j≤Δ Δ''τ₁ty  Δ'τ₂ty •τₐty with Δ''τ₁ty  
... | ty-unit = refl
... | ty-nat = refl
... | ty-bool = refl
... | ty-prod τ₂₁ τ₂₂ = cong₂ _×_ (β#≡  Δ≡i j≤Δ τ₂₁  Δ'τ₂ty •τₐty) (β#≡  Δ≡i j≤Δ  τ₂₂  Δ'τ₂ty •τₐty)
... | ty-arr τ₂₁ τ₂₂ = cong₂ _⇒_ (β#≡  Δ≡i j≤Δ τ₂₁  Δ'τ₂ty •τₐty) (β#≡  Δ≡i j≤Δ  τ₂₂  Δ'τ₂ty •τₐty)
... | ty-sum τ₂₁ τ₂₂ = cong₂ _⨁_ (β#≡  Δ≡i j≤Δ τ₂₁  Δ'τ₂ty •τₐty) (β#≡  Δ≡i j≤Δ  τ₂₂  Δ'τ₂ty •τₐty)
... | ty-list τ = cong List (β#≡  Δ≡i j≤Δ τ  Δ'τ₂ty •τₐty)
... | ty-all τall rewrite (inc-τ-β≡ {τ₂} {τₐ} {i} {0} z≤n •τₐty) =
    let 
        Δ'τ₂'ty = inc-τ-weaken0 Δ'τ₂ty 
        •τₐty' = subst (λ z → • ⊢ z ty) (sym (inc-τ-no-op z≤n •τₐty)) •τₐty
    in cong ∀'_ (β#≡  {j = suc j} (cong suc Δ≡i) (s≤s j≤Δ) τall  Δ'τ₂'ty  •τₐty')  
... | ty-var {Δ''} {n} lookupN with n ≡ᵇ j in n≡ᵇj 
... | true = 
    let n≡j = ≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt)
        n≤Δ = subst (λ z → z ≤ Δ) (sym n≡j) j≤Δ
        n≤i = subst (λ z → n ≤ z) Δ≡i n≤Δ
        n<i' = ≤⇒<suc n≤i
        stillτₐ = var-subst'-no-op n<i'
        rhs = var-subst'-just {τ = (β# τ₂ τₐ i)} n≡j
        rhs' = subst (λ z → (β# z (β# τ₂ τₐ i) j) ≡ (β# τ₂ τₐ i)) (sym stillτₐ) rhs
    in sym rhs'
... | false with n <ᵇ j in n<ᵇj
...             | true = 
    let 
        n<j = <ᵇ⇒< n j (subst T (sym n<ᵇj) tt)
        n<Δ = <-≤-trans n<j j≤Δ
        n<i = subst (λ z → n < z) Δ≡i n<Δ
        lhs = var-subst'-no-op {τ = τₐ} n<i
        n<i' = <-trans n<i (<suci {i})
        stillVarN = var-subst'-no-op {τ = τₐ} n<i'
        rhs = var-subst'-no-op {τ = (β# τ₂ τₐ i)} n<j
        rhs' = subst (λ z → (β# z (β# τ₂ τₐ i) j) ≡ TVar n) (sym stillVarN) rhs
    in trans lhs (sym rhs')
...             | false  with (n ≡ᵇ (suc i)) in n≡ᵇi' | n <ᵇ suc i in n<ᵇi'
...                       | true | _ rewrite (≡ᵇ⇒≡ n (suc i) (subst T (sym n≡ᵇi') tt)) = 
    let 
        n≡i' = ≡ᵇ⇒≡ n (suc i) (subst T (sym n≡ᵇi') tt)
        lhs = var-subst'-just {n = i} {τ = τₐ} {i = i} refl
        rhs = subst'-no-op {i = j} {τ₂ = (β# τ₂ τₐ i)} z≤n •τₐty
    in trans lhs (sym rhs)
...                       | false | true =
    let 
        n≢j = ≢ᵇ⇒≢ {n} {j} n≡ᵇj
        n≮j = λ n<j → subst T n<ᵇj (<⇒<ᵇ {n} {j} n<j)
        j≤n = ≮⇒≥ n≮j
        j<n = ≤∧≢⇒< j≤n (λ j≡n → n≢j (sym j≡n))
        n<i' = <ᵇ⇒< n (suc i) (subst T (sym n<ᵇi') tt)
        
        pn<i = <suc⇒pred< j<n n<i'
        lhs = var-subst'-pred {τ = τ₂} j<n
        lhs' = var-subst'-no-op {τ = τₐ} pn<i

        rhs = var-subst'-no-op {τ = τₐ} n<i'
        rhs' = var-subst'-pred {τ = (β# τ₂ τₐ i)} j<n
    in trans lhs' (sym rhs')
...                       | false | false =
    let 
        n<Δ'' = lookup'-size {Δ''} {n} lookupN
        n<i'' = subst (λ z → n < (suc (suc z))) Δ≡i n<Δ''
        n≤i' = <suc⇒≤ n<i''
        n≢i' = ≢ᵇ⇒≢ {n} {suc i} n≡ᵇi'
        n≮i' = λ n<i' → subst T n<ᵇi' (<⇒<ᵇ {n} {suc i} n<i')
    in ⊥-elim (n≮i' (≤∧≢⇒< n≤i' n≢i'))



subst'-τ : ∀ {Δ Γ i τ₁ τ₂ body} →
                 (• ⊢ τ₁ ty) →
                 (Δ ≡ i) →
                 ((★ ++' Δ) ⨟ Γ ⊢ body ⦂ τ₂) →
                 (Δ ⨟ (βᵧ Γ τ₁ i) ⊢ (β' body τ₁ i) ⦂ (β# τ₂ τ₁ i))
subst'-τ •⊢τ₁ty |Δ|≡i (τ-true)       = τ-true
subst'-τ •⊢τ₁ty |Δ|≡i (τ-false)       = τ-false
subst'-τ •⊢τ₁ty |Δ|≡i (τ-zero)        = τ-zero
subst'-τ •⊢τ₁ty |Δ|≡i (τ-unit)        = τ-unit
subst'-τ •⊢τ₁ty |Δ|≡i (τ-suc τ₁)       = τ-suc (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-pred τ₁)      = τ-pred (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-zero? τ₁)     = τ-zero? (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-if τ₁ τ₂ τ₃)  = τ-if (subst'-τ •⊢τ₁ty |Δ|≡i τ₁) (subst'-τ •⊢τ₁ty |Δ|≡i τ₂) (subst'-τ •⊢τ₁ty |Δ|≡i τ₃)      
subst'-τ •⊢τ₁ty |Δ|≡i (τ-cons τ₁ τ₂)   = τ-cons (subst'-τ •⊢τ₁ty |Δ|≡i τ₁) (subst'-τ •⊢τ₁ty |Δ|≡i τ₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-fst τ₁×₂)     = τ-fst (subst'-τ •⊢τ₁ty |Δ|≡i τ₁×₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-snd τ₁×₂)     = τ-snd (subst'-τ •⊢τ₁ty |Δ|≡i τ₁×₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-app fTy eTy)  = τ-app (subst'-τ •⊢τ₁ty |Δ|≡i fTy) (subst'-τ •⊢τ₁ty |Δ|≡i eTy)
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} •⊢τ₁ty |Δ|≡i (τ-nil τTy) =
  let
    Δ++•⊢τ₁ty = ty-weaken {Δ} {•} •⊢τ₁ty
    Δ⊢τ₁ty    = subst (λ z → z ⊢ τ₁ ty) (concat-id' Δ) Δ++•⊢τ₁ty
    i≤|Δ|     = ≤-reflexive (sym |Δ|≡i)
    τTy'      = subst'-ty i≤|Δ| τTy Δ⊢τ₁ty
  in
    τ-nil τTy'
subst'-τ •⊢τ₁ty |Δ|≡i (τ-nil? τ) = τ-nil? (subst'-τ •⊢τ₁ty |Δ|≡i τ)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-lcons τ₁ τ₂) = τ-lcons (subst'-τ •⊢τ₁ty |Δ|≡i τ₁) (subst'-τ •⊢τ₁ty |Δ|≡i τ₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-first τ) = τ-first (subst'-τ •⊢τ₁ty |Δ|≡i τ)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-rest τ) = τ-rest (subst'-τ •⊢τ₁ty |Δ|≡i τ)
subst'-τ  {Δ} {Γ} {i} {τ₁} {τ₂} •⊢τ₁ty |Δ|≡i (τ-inl  {Δ'} {Γ'} {e} {τ1} {τ2} ΔTy lTy) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
    in τ-inl (subst'-ty i≤|Δ| ΔTy Δ⊢τ₁ty) (subst'-τ •⊢τ₁ty |Δ|≡i lTy)
subst'-τ  {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-inr  {Δ'} {Γ'} {e} {τ1} {τ2} ΔTy rTy)  = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
    in τ-inr (subst'-ty i≤|Δ| ΔTy Δ⊢τ₁ty) (subst'-τ •⊢τ₁ty |Δ|≡i rTy)
subst'-τ {Δ₁} {Γ} {i} {τ₁} {τ₂} {Fix τ₂ e₁} •⊢τ₁ty |Δ|≡i (τ-fix {Δ = suc Δ₁} {Γ'} {τ} {e} ΔTy bodyTy) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ₁} {•} •⊢τ₁ty
        Δ₁⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ₁) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
        Δ₁⊢τ'ty = subst'-ty i≤|Δ| ΔTy Δ₁⊢τ₁ty
        ih = (subst'-τ •⊢τ₁ty |Δ|≡i bodyTy)
    in
    τ-fix Δ₁⊢τ'ty ih
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-var {Δ'} {Γ'} {n} {τ₃} ΔTy lookupN) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
        Δ⊢τ₂'ty = subst'-ty i≤|Δ| ΔTy Δ⊢τ₁ty
    in τ-var Δ⊢τ₂'ty (lookupᵧ {Γ} {n} {i} lookupN)
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-lam {Δ'} {Γ'} {τ₃} {τ₄} {e} ΔTy bodyTy) =
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
        Δ⊢τ₃'ty = subst'-ty  i≤|Δ| ΔTy Δ⊢τ₁ty
        ih = subst'-τ •⊢τ₁ty |Δ|≡i bodyTy 
    in τ-lam Δ⊢τ₃'ty ih
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body = Case e eₗ eᵣ} •⊢τ₁ty |Δ|≡i (τ-case {Δ'} {Γ'} {τₗ} {τᵣ} cTy lTy rTy) =
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        cTy' = subst'-τ •⊢τ₁ty |Δ|≡i cTy
        lTy' = subst'-τ •⊢τ₁ty |Δ|≡i lTy
        rTy' = subst'-τ •⊢τ₁ty |Δ|≡i rTy
    in τ-case cTy' lTy' rTy'
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-lamT {Δ'} {Γ'} {τ₃} {e} bodyTy) =
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        ih = subst'-τ •⊢τ₁ty (cong suc |Δ|≡i) bodyTy 
        ih' = subst (λ z → suc Δ ⨟ z ⊢ β' e τ₁ (suc i) ⦂ β# τ₃ τ₁ (suc i)) (sym (inc-Γᵧ {Γ} {τ₁} {i} •⊢τ₁ty)) ih
        ih'' = subst (λ z → suc Δ ⨟ inc-Γ (βᵧ Γ τ₁ i) ⊢ β' e τ₁ (suc i) ⦂ β# τ₃ z (suc i)) (sym (inc-τ-no-op z≤n •⊢τ₁ty)) ih'
    in τ-lamT ih'' 
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-appT {Δ'} {Γ'} {f} {τ₃} {τ₄} ΔTy bodyTy) = 
    let 
        Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        i≤|Δ| = ≤-reflexive (sym |Δ|≡i)
        Δ⊢τ₂'ty = subst'-ty i≤|Δ| ΔTy Δ⊢τ₁ty
        ih = subst'-τ •⊢τ₁ty |Δ|≡i bodyTy 
        ih' = subst (λ z → Δ ⨟ βᵧ Γ τ₁ i ⊢ β' f τ₁ i ⦂ ∀' β# τ₃ z (suc i)) (inc-τ-no-op z≤n •⊢τ₁ty) ih
        res = τ-appT {Δ} {βᵧ Γ τ₁ i} {β' f τ₁ i} {β# τ₃ τ₁ (suc i)} {β# τ₄ τ₁ i} Δ⊢τ₂'ty ih'
        Δ''τ₃ty = ∀bodyTy (τ-ty bodyTy)
        β≡ = β#≡ {τ₁ = τ₃ } {τ₂ = τ₄} {τₐ = τ₁} {Δ = Δ} {i = i} {j = 0} |Δ|≡i z≤n Δ''τ₃ty ΔTy •⊢τ₁ty
        res' = subst (λ z →  Δ ⨟ βᵧ Γ τ₁ i ⊢ AppT (β' f τ₁ i) (β# τ₄ τ₁ i) ⦂ z) (sym β≡) res
    in res'



subst0'-τ : ∀ {τ₁ τ₂ body} →
            (• ⊢ τ₁ ty) →
            (• ,★ ⨟ ∘ ⊢ body ⦂ τ₂) →
            (• ⨟ ∘ ⊢ body [ τ₁ ]' ⦂ τ₂ #[ τ₁ ])
subst0'-τ {τ₁} {τ₂} {body} τ₁Ty bodyTy  =  subst'-τ {•} {∘} {0} τ₁Ty refl bodyTy 
