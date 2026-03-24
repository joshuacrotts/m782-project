module theorems.lemmas.1b-type where

open import SystemF.definitions
open import theorems.lemmas.0-math


ty-weaken : ∀ {Δ₁ Δ₂ τ} → (Δ₂ ⊢ τ ty) → ((Δ₁ ++' Δ₂) ⊢ τ ty)
ty-weaken ty-unit = ty-unit
ty-weaken ty-nat = ty-nat
ty-weaken ty-bool = ty-bool
ty-weaken {Δ₁} {Δ₂} (ty-var {Δ = Δ₂} {n} lookupN) with n <ᵇ Δ₂ in n<Δ₂ | n <ᵇ (Δ₁ ++' Δ₂) in n<|Δ₁++Δ₂|
... | true | true = 
    let n<|Δ₁++Δ₂|' = <ᵇ⇒< n (Δ₁ ++' Δ₂) (subst T (sym n<|Δ₁++Δ₂|) tt) in ty-var (lookup'-rest n<|Δ₁++Δ₂|')
... | true | false = ⊥-elim (subst T n<|Δ₁++Δ₂| (<⇒<ᵇ (weaken Δ₁ (<ᵇ⇒< n Δ₂ (subst T (sym n<Δ₂) tt)))))
  where
    ≤-suc : ∀ {a b} → a ≤ b → a ≤ suc b
    ≤-suc z≤n = z≤n
    ≤-suc (s≤s p) = s≤s (≤-suc p)
    weaken : ∀ d → n < Δ₂ → n < (d ++' Δ₂)
    weaken zero lt = lt
    weaken (suc d) lt = ≤-suc (weaken d lt)
ty-weaken {Δ₁} {Δ₂} (ty-prod τ₁ τ₂) = ty-prod (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-sum τ₁ τ₂) = ty-sum (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-arr τ₁ τ₂) = ty-arr (ty-weaken τ₁) (ty-weaken τ₂)
ty-weaken {Δ₁} {Δ₂} (ty-list τ) = ty-list (ty-weaken τ)
ty-weaken {Δ₁} {Δ₂} {τ₁} (ty-all {Δ = Δ₂} {τ₂} ty) = ty-all (subst (λ z → z ⊢ τ₂ ty) (sym (++,★ {Δ₁} {Δ₂})) (ty-weaken {Δ₁} {Δ₂ ,★} ty))
    where
      ++,★ : ∀ {Δ₁ Δ₂} → ((Δ₁ ++' Δ₂) ,★) ≡ (Δ₁ ++' (Δ₂ ,★))
      ++,★ {zero} {Δ₂} = refl
      ++,★ {suc Δ₁} {Δ₂} = cong suc (++,★ {Δ₁} {Δ₂})



ty-weaken-suc : ∀ {Δ τ} → (Δ ⊢ τ ty) → ((suc Δ) ⊢ τ ty)
ty-weaken-suc {Δ} {τ}  ΔτTy = ty-weaken {★} {Δ} {τ} ΔτTy


-- Shifting a type whose free vars are all < Δ at any cutoff j ≥ Δ is a no-op.
inc-τ-no-op : ∀ {Δ τ j} → Δ ≤ j → (Δ ⊢ τ ty) → inc-τ-i τ j ≡ τ
inc-τ-no-op Δ≤j ty-unit = refl
inc-τ-no-op Δ≤j ty-nat = refl
inc-τ-no-op Δ≤j ty-bool = refl
inc-τ-no-op Δ≤j (ty-prod lTy rTy) = cong₂ _×_ (inc-τ-no-op Δ≤j lTy) (inc-τ-no-op Δ≤j rTy)
inc-τ-no-op Δ≤j (ty-sum lTy rTy) = cong₂ _⨁_ (inc-τ-no-op Δ≤j lTy) (inc-τ-no-op Δ≤j rTy)
inc-τ-no-op Δ≤j (ty-arr lTy rTy) = cong₂ _⇒_ (inc-τ-no-op Δ≤j lTy) (inc-τ-no-op Δ≤j rTy)
inc-τ-no-op Δ≤j (ty-list ty) = cong (List) (inc-τ-no-op Δ≤j ty)
inc-τ-no-op {Δ} {∀' τ'} {j} Δ≤j (ty-all ty) = cong ∀'_ (inc-τ-no-op (s≤s Δ≤j) ty)
inc-τ-no-op {Δ} {TVar n} {j} Δ≤j (ty-var {n = n} lookupN) with n <ᵇ j in eq
... | true = refl
... | false =
    let n<Δ = lookup'-size lookupN
        n<j = <-≤-trans n<Δ Δ≤j
    in ⊥-elim (subst T eq (<⇒<ᵇ n<j))




inc-τ-weaken : ∀ {Δ τ i} → i ≤ Δ → (Δ ⊢ τ ty) → ((Δ ,★) ⊢ inc-τ-i τ i ty)
inc-τ-weaken {Δ} {τ} {i} i≤Δ ty-unit = ty-unit
inc-τ-weaken {Δ} {τ} {i} i≤Δ ty-nat = ty-nat
inc-τ-weaken {Δ} {τ} {i} i≤Δ ty-bool = ty-bool
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-prod lTy rTy) = ty-prod (inc-τ-weaken i≤Δ lTy) (inc-τ-weaken i≤Δ rTy)
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-sum lTy rTy) = ty-sum (inc-τ-weaken i≤Δ lTy) (inc-τ-weaken i≤Δ rTy)
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-arr lTy rTy) = ty-arr (inc-τ-weaken i≤Δ lTy) (inc-τ-weaken i≤Δ rTy)
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-list ty) = ty-list (inc-τ-weaken i≤Δ ty)
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-all ty) = ty-all (inc-τ-weaken (s≤s i≤Δ) ty)
inc-τ-weaken {Δ} {τ} {i} i≤Δ (ty-var {Δ = Δ} {n} lookupN) with n <ᵇ i in n<ᵇi
... | true  = ty-weaken-suc (ty-var {Δ = Δ} {n} lookupN) 
... | false = 
    let n<Δ = lookup'-size {Δ} {n} lookupN
        n'<Δ' = <⇒suc<suc n<Δ
        lookupN' = lookup'-rest {suc Δ} {suc n} n'<Δ'
    in
    ty-var {Δ = (suc Δ)} {n = suc n} lookupN'



inc-τ-weaken0 : ∀ {Δ τ} →  (Δ ⊢ τ ty) → ((Δ ,★) ⊢ inc-τ τ ty)
inc-τ-weaken0 {Δ} {τ} Δty = inc-τ-weaken {Δ} {τ} (z≤n) Δty




subst'-ty : ∀ {Δ i τ₁ τ₂} →
                 (i ≤ Δ) →
                 ((★ ++' Δ) ⊢ τ₂ ty) →
                 (Δ ⊢ τ₁ ty) →
                 (Δ ⊢ (β# τ₂ τ₁ i) ty)
subst'-ty i≤Δ ty-unit τ₁Ty = ty-unit
subst'-ty i≤Δ ty-nat τ₁Ty = ty-nat 
subst'-ty i≤Δ ty-bool τ₁Ty = ty-bool 
subst'-ty i≤Δ (ty-list τ₂) τ₁Ty = ty-list (subst'-ty i≤Δ τ₂ τ₁Ty)
subst'-ty {Δ} {i} {τ₁} i≤Δ (ty-var {Δ'} {n} lookupN) τ₁Ty with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi 
... | true  | _   = τ₁Ty
... | false | true  with i ≤ᵇ Δ in i≤ᵇΔ
...                 | true  = 
    let n<i = <ᵇ⇒< n i (subst T (sym n<ᵇi) tt)
        n<Δ = <-≤-trans n<i i≤Δ
    in ty-var (lookup'-rest {Δ} {n} n<Δ)
...                 | false = ⊥-elim (subst T i≤ᵇΔ (≤⇒≤ᵇ i≤Δ))
subst'-ty {Δ} {i} {τ₁} i≤Δ (ty-var {Δ'} {n} lookupN) τ₁Ty | false | false with n 
...                 | suc m  = ty-var (lookup'-rest {Δ} {m} (≤-pred (lookup'-size lookupN)))
...                 | zero with i  
...                             | zero  = ⊥-elim (≢ᵇ⇒≢ {0} {0} n≡ᵇi refl)
...                             | suc j with n<ᵇi
...                                        | ()
subst'-ty i≤Δ (ty-prod  τ₂₁ τ₂₂) τ₁Ty = ty-prod (subst'-ty i≤Δ τ₂₁ τ₁Ty) (subst'-ty i≤Δ τ₂₂ τ₁Ty)
subst'-ty i≤Δ (ty-sum τ₂₁ τ₂₂) τ₁Ty = ty-sum (subst'-ty i≤Δ τ₂₁ τ₁Ty) (subst'-ty i≤Δ τ₂₂ τ₁Ty)
subst'-ty i≤Δ (ty-arr τ₂₁ τ₂₂) τ₁Ty = ty-arr (subst'-ty i≤Δ τ₂₁ τ₁Ty) (subst'-ty i≤Δ τ₂₂ τ₁Ty)
subst'-ty {Δ} {i} {τ₁}  i≤Δ (ty-all {Δ'} {τ₃} ty) τ₁Ty = ty-all (subst'-ty (s≤s i≤Δ) ty (inc-τ-weaken0 τ₁Ty))






τ-ty : ∀ {Δ Γ e τ} → (Δ ⨟ Γ ⊢ e ⦂ τ) → (Δ ⊢ τ ty)
τ-ty τ-true = ty-bool
τ-ty τ-false = ty-bool
τ-ty τ-zero = ty-nat
τ-ty τ-unit = ty-unit
τ-ty (τ-suc τ₁) = ty-nat
τ-ty (τ-pred τ₁) = ty-nat
τ-ty (τ-zero? τ₁) = ty-bool
τ-ty (τ-if _ τ₂ _) = τ-ty τ₂
τ-ty (τ-cons τ₁ τ₂) = ty-prod (τ-ty τ₁) (τ-ty τ₂)
τ-ty (τ-fst τ₁×₂) with τ-ty τ₁×₂ 
... | ty-prod τ₁ τ₂ = τ₁
τ-ty (τ-snd τ₁×₂) with τ-ty τ₁×₂
... | ty-prod τ₁ τ₂ = τ₂
τ-ty (τ-app fTy _) with τ-ty fTy
... | ty-arr argTy resTy = resTy
τ-ty {Δ} {Γ} (τ-appT {Δ = Δ} {Γ = Γ} {f} {τ1} {τ2} ΔTy fTy) with τ-ty fTy
... | ty-all bodyTy = subst'-ty z≤n bodyTy ΔTy  
τ-ty (τ-inl ΔTy τ₁) = ty-sum (τ-ty τ₁) ΔTy
τ-ty (τ-inr ΔTy τ₂) = ty-sum ΔTy (τ-ty τ₂)
τ-ty (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) = ΔTy
τ-ty (τ-var ΔTy lookupN) = ΔTy
τ-ty (τ-case {Δ} {Γ} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) = τ-ty τ₁
τ-ty (τ-lam {Δ} {Γ} {τ₁} ΔTy bodyTy) = ty-arr ΔTy (τ-ty bodyTy)
τ-ty (τ-lamT x) = ty-all (τ-ty x)
τ-ty (τ-nil τ) = ty-list τ
τ-ty (τ-nil? e) = ty-bool
τ-ty (τ-lcons τ₁ τ₂) = ty-list (τ-ty τ₁)
τ-ty (τ-first τ₁) with τ-ty τ₁
... | ty-list τTy = ty-sum ty-unit τTy
τ-ty (τ-rest τ₁) with τ-ty τ₁
... | ty-list τTy = ty-list τTy




∀bodyTy : ∀ {Δ τ} → Δ ⊢ ∀' τ ty → (suc Δ) ⊢ τ ty
∀bodyTy {Δ} {τ} Δ∀τTy with Δ∀τTy
... | ty-all τ = τ