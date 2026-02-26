{-# OPTIONS --allow-unsolved-metas #-}

module lemma where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤∧≢⇒<; <ᵇ⇒<; ≤ᵇ⇒≤; <⇒<ᵇ; ≤-pred; <-irrefl; <-≤-trans; ≤-reflexive; m≤n⇒m≤1+n; <-trans; ≮⇒≥)
open import Data.Bool using (true; false; T)
open import Data.Bool.Properties using (T?)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; sym; cong; cong₂)
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

≤⇒<suc : ∀ {m i}  → m ≤ i → m < suc i
≤⇒<suc {m} {i} m≤i = s≤s m≤i


<suc⇒pred< : ∀ {n j i} → j < n → n < suc i → pred n < i
<suc⇒pred< {zero} () _
<suc⇒pred< {suc n} {j} {i} _ n<si = ≤-pred n<si



inc-Γ-∷ : ∀ {τ₁ Γ} → inc-Γ (τ₁ ∷ Γ) ≡ (inc-τ τ₁ ∷ inc-Γ Γ)
inc-Γ-∷ {τ₁} {∘} = refl
inc-Γ-∷ {τ₁} {Γ , τ'} = cong (λ x → x , inc-τ τ') (inc-Γ-∷ {τ₁} {Γ})

inc-Γ-distr : ∀ {Γ₁ Γ₂} → inc-Γ (Γ₁ ++ Γ₂) ≡ ((inc-Γ Γ₁) ++ (inc-Γ Γ₂))
inc-Γ-distr {∘} {Γ₂} = refl
inc-Γ-distr {Γ₁ , τ₁} {Γ₂} = trans (inc-Γ-distr {Γ₁} {τ₁ ∷ Γ₂}) (cong (λ x → (inc-Γ Γ₁) ++ x) (inc-Γ-∷ {τ₁} {Γ₂}))


|inc-Γ|≡|Γ| : ∀ {Γ} → size (inc-Γ Γ) ≡ size Γ
|inc-Γ|≡|Γ| {∘} = refl  
|inc-Γ|≡|Γ| {Γ , τ} = cong suc (|inc-Γ|≡|Γ| {Γ})


    
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
ty-weaken {Δ₁} {Δ₂} {τ₁} (ty-all {Δ = Δ₂} {τ₂} ty) = ty-all (subst (λ z → z ⊢ τ₂ ty) (sym (++,★ {Δ₁} {Δ₂})) (ty-weaken {Δ₁} {Δ₂ ,★} ty))
    where
      ++,★ : ∀ {Δ₁ Δ₂} → ((Δ₁ ++' Δ₂) ,★) ≡ (Δ₁ ++' (Δ₂ ,★))
      ++,★ {zero} {Δ₂} = refl
      ++,★ {suc Δ₁} {Δ₂} = cong suc (++,★ {Δ₁} {Δ₂})



ty-weaken-suc : ∀ {Δ τ} → (Δ ⊢ τ ty) → ((suc Δ) ⊢ τ ty)
ty-weaken-suc {Δ} {τ}  ΔτTy = ty-weaken {★} {Δ} {τ} ΔτTy


inc-τ-no-op : ∀ {Δ τ i} → i ≤ Δ → (Δ ⊢ τ ty) → inc-τ-i τ i ≡ τ
inc-τ-no-op {Δ} {τ} {i} i≤Δ ty-unit = refl
inc-τ-no-op {Δ} {τ} {i} i≤Δ ty-nat = refl
inc-τ-no-op {Δ} {τ} {i} i≤Δ ty-bool = refl
inc-τ-no-op {Δ} {τ} {i} i≤Δ (ty-prod {Δ = Δ} {τ₁} {τ₂} lTy rTy) = cong₂ _×_ (inc-τ-no-op i≤Δ lTy) (inc-τ-no-op i≤Δ rTy)
inc-τ-no-op {Δ} {τ} {i} i≤Δ (ty-sum {Δ = Δ} {τ₁} {τ₂} lTy rTy) = cong₂ _⨁_ (inc-τ-no-op i≤Δ lTy) (inc-τ-no-op i≤Δ rTy)
inc-τ-no-op {Δ} {τ} {i} i≤Δ (ty-arr {Δ = Δ} {τ₁} {τ₂} lTy rTy) = cong₂ _⇒_ (inc-τ-no-op i≤Δ lTy) (inc-τ-no-op i≤Δ rTy)
inc-τ-no-op {Δ} {τ} {i} i≤Δ (ty-all {Δ = Δ} {τ'} ty) = 
    cong ∀'_ (inc-τ-no-op {Δ ,★} {τ'} {suc i} (s≤s i≤Δ) ty)
inc-τ-no-op {Δ} {τ} {i} i≤Δ (ty-var {Δ = Δ} {n} lookupN) with n <ᵇ i in n<i
... | true  = refl
... | false = case lookupN of λ ()




inc-τ-weaken : ∀ {Δ τ i} → i ≤ Δ → (Δ ⊢ τ ty) → ((Δ ,★) ⊢ inc-τ-i τ i ty)
inc-τ-weaken {Δ} {τ} {i} i≤Δ Δty = 
    let incτnoop = inc-τ-no-op {Δ} {τ} {i} i≤Δ Δty
        Δty' = ty-weaken {★} {Δ} Δty 
    in subst (λ z → (suc Δ) ⊢ z ty) (sym incτnoop) Δty'


inc-τ-weaken0 : ∀ {Δ τ} →  (Δ ⊢ τ ty) → ((Δ ,★) ⊢ inc-τ τ ty)
inc-τ-weaken0 {Δ} {τ} Δty = inc-τ-weaken {Δ} {τ} (z≤n) Δty




subst'-ty : ∀ {Δ i τ₁ τ₂} →
                 ((★ ++' Δ) ⊢ τ₂ ty) →
                 (Δ ⊢ τ₁ ty) →
                 (Δ ⊢ (β# τ₂ τ₁ i) ty)
subst'-ty ty-unit τ₁Ty = ty-unit
subst'-ty ty-nat τ₁Ty = ty-nat 
subst'-ty ty-bool τ₁Ty = ty-bool 
subst'-ty {Δ} {i} {τ₁} (ty-var {Δ'} {n} lookupN) τ₁Ty with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi 
... | true  | _   = τ₁Ty
... | false | true  with i ≤ᵇ Δ in i≤Δ
...                 | true  = 
    let i≤Δ = ≤ᵇ⇒≤ i Δ (subst T (sym i≤Δ) tt) 
        n<i = <ᵇ⇒< n i (subst T (sym n<ᵇi) tt)
        n<Δ = <-≤-trans n<i i≤Δ
    in ty-var (lookup'-rest {Δ} {n} n<Δ)
...                 | false with n <ᵇ Δ in n<ᵇΔ
...                             | true  = let n<Δ = <ᵇ⇒< n Δ (subst T (sym n<ᵇΔ) tt) 
                                          in ty-var (lookup'-rest {Δ} {n} n<Δ)
...                             | false = case lookupN of λ ()
subst'-ty {Δ} {i} {τ₁} (ty-var {Δ'} {n} lookupN) τ₁Ty | false | false with n 
...                 | suc m  = ty-var (lookup'-rest {Δ} {m} (≤-pred (lookup'-size lookupN)))
...                 | zero with n≡ᵇi | n<ᵇi | i  
...                             | eq1 | eq2 | zero  = case eq1 of λ ()
...                             | eq1 | eq2 | suc _ = case eq2 of λ ()
subst'-ty (ty-prod  τ₂₁ τ₂₂) τ₁Ty =
    ty-prod (subst'-ty τ₂₁ τ₁Ty) (subst'-ty τ₂₂ τ₁Ty)
subst'-ty (ty-sum τ₂₁ τ₂₂) τ₁Ty = ty-sum (subst'-ty τ₂₁ τ₁Ty) (subst'-ty τ₂₂ τ₁Ty)
subst'-ty (ty-arr τ₂₁ τ₂₂) τ₁Ty = ty-arr (subst'-ty τ₂₁ τ₁Ty) (subst'-ty τ₂₂ τ₁Ty)
subst'-ty {Δ} {i} {τ₁} (ty-all {Δ'} {τ₃} ty) τ₁Ty =  
    let tyall' = ty-all (subst'-ty ty (ty-weaken τ₁Ty))
        incτ₁≡τ₁ = inc-τ-no-op {Δ} {τ₁} {0} z≤n τ₁Ty
        tyall'' = subst (λ z → Δ ⊢ ∀' β# τ₃ z (suc i) ty) (sym incτ₁≡τ₁) tyall'
    in tyall''






τ-ty : ∀ {Δ Γ e τ} → (Δ ⨟ Γ ⊢ e ⦂ τ) → (Δ ⊢ τ ty)
τ-ty τ-true = ty-bool
τ-ty τ-false = ty-bool
τ-ty τ-zero = ty-nat
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
... | ty-all bodyTy = subst'-ty bodyTy ΔTy   
τ-ty (τ-inl ΔTy τ₁) = ty-sum (τ-ty τ₁) ΔTy
τ-ty (τ-inr ΔTy τ₂) = ty-sum ΔTy (τ-ty τ₂)
τ-ty (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) = ΔTy
τ-ty (τ-var ΔTy lookupN) = ΔTy
τ-ty (τ-case {Δ} {Γ} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) = τ-ty τ₁
τ-ty (τ-lam {Δ} {Γ} {τ₁} ΔTy bodyTy) = ty-arr ΔTy (τ-ty bodyTy)
τ-ty (τ-lamT x) = ty-all (τ-ty x)





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
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inl ΔTy τ₁)        = τ-inl ΔTy (Γ-weaken {Δ} {Γ₁} {Γ₂} τ₁)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-inr ΔTy τ2)        = τ-inr ΔTy (Γ-weaken {Δ} {Γ₁}{ Γ₂} τ2)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) =
  let
    aa = concat-append {Γ₁} {Γ₂} {τ}
    bb = Γ-weaken {Δ} {Γ₁} {Γ₂ , τ} bodyTy
  in
    τ-fix ΔTy (subst (λ z → Δ ⨟ z ⊢ e ⦂ τ) aa bb)
Γ-weaken {Δ} {Γ₁} {Γ₂} (τ-var ΔTy lookupN)   = τ-var ΔTy (lookup-concat  {Γ₁} {Γ₂} lookupN)
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
    let inc-Γ₁Γ₂ = inc-Γ-distr {Γ₁} {Γ₂}
        bodyTy' = Γ-weaken {Δ ,★} {inc-Γ Γ₁} {inc-Γ Γ₂} bodyTy
    in τ-lamT (subst (λ z → Δ ,★ ⨟ z ⊢ e' ⦂ τ₂) (sym inc-Γ₁Γ₂) bodyTy')
    -- Γ-weaken {Δ ,★} {Γ₁} {Γ₂ } bodyTy)
    





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
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inl ΔTy τ₁) = τ-inl (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₁)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-inr ΔTy τ₂) = τ-inr (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-fix {Δ} {Γ} {τ} {e} ΔTy bodyTy) = τ-fix (ty-weaken ΔTy)  (Δ-weaken {Δ₁} {Δ₂} {Γ , τ} bodyTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-var ΔTy lookupN) = τ-var (ty-weaken ΔTy) lookupN
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-case {Δ} {Γ₂} {leftTy} {rightTy} {τ₃} {τₑ} {el} {er} e' τ₁ τ₂) = 
    τ-case (Δ-weaken {Δ₁} {Δ₂} {Γ} e')
           (Δ-weaken {Δ₁} {Δ₂} {Γ , leftTy} τ₁)
           (Δ-weaken {Δ₁} {Δ₂} {Γ , rightTy} τ₂)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lam {Δ'} {Γ'} {τ₁} ΔTy bodyTy) = τ-lam (ty-weaken ΔTy) (Δ-weaken {Δ₁} {Δ₂} {Γ , τ₁} bodyTy)
Δ-weaken {Δ₁} {Δ₂} {Γ} (τ-lamT {Δ'} {Γ'} {τ₁} {e} bodyTy) = 
    let 
        aa = (Δ-weaken {Δ₁} bodyTy)
        bb = Δ₁++'Δ₂,★ {Δ₁} {Δ₂}
    in τ-lamT ( subst (λ z → z ⨟ inc-Γ Γ ⊢ e ⦂ τ₁) (sym bb) aa)





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
subst-τ |Γ|≡i (τ-inl ΔTy τ₁) vTy        = τ-inl ΔTy (subst-τ |Γ|≡i τ₁ vTy)
subst-τ |Γ|≡i (τ-inr ΔTy τ₂) vTy        = τ-inr ΔTy (subst-τ |Γ|≡i τ₂ vTy)
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
            (• ⨟ ∘ , τ₁ ⊢ body ⦂ τ₂) →
            (• ⨟ ∘ ⊢ v ⦂ τ₁) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₂)
subst0-τ bodyTy vTy  = subst-τ refl bodyTy vTy


subst0-τ-inl : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ , τ₁ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inl v) ⦂ τ₁ ⨁ τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inl bodyTy vTy with vTy
... | τ-inl ΔTy vTy' = subst0-τ bodyTy vTy' 


subst0-τ-inr : ∀ {τ₁ τ₂ τ₃ body v} →
            (• ⨟ ∘ , τ₂ ⊢ body ⦂ τ₃) →
            (• ⨟ ∘ ⊢ (Inr v) ⦂ τ₁ ⨁ τ₂) →
            (• ⨟ ∘ ⊢ body [ v ] ⦂ τ₃)
subst0-τ-inr bodyTy vTy with vTy
... | τ-inr ΔTy vTy' = subst0-τ bodyTy vTy' 










subst'-no-op : ∀ {Δ i τ₁ τ₂} →
                 (Δ ≤ i) →
                 (Δ ⊢ τ₁ ty) →
                 ((β# τ₁ τ₂ i) ≡ τ₁)
subst'-no-op |Δ|≤i ty-unit = refl
subst'-no-op |Δ|≤i ty-nat = refl
subst'-no-op |Δ|≤i ty-bool = refl
subst'-no-op {Δ} {i} |Δ|≤i (ty-var {Δ = Δ} {n} lookupN) with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi
... | true | _ = 
    let n≡i = ≡ᵇ⇒≡ n i (subst T (sym n≡ᵇi) tt)
        |Δ|≤n = subst (λ z → Δ ≤ z) (sym n≡i) |Δ|≤i
        n<|Δ| = lookup'-size {Δ} {n} lookupN
    in ⊥-elim (<-irrefl refl (<-≤-trans n<|Δ| |Δ|≤n))
... | false | true = refl
... | false | false = 
    let  n<|Δ| = lookup'-size {Δ} {n} lookupN
         n<i = <-≤-trans n<|Δ| |Δ|≤i
    in ⊥-elim (subst T n<ᵇi (<⇒<ᵇ n<i))
subst'-no-op |Δ|≤i (ty-prod τ₂₁ τ₂₂) = cong₂ _×_ (subst'-no-op |Δ|≤i τ₂₁) (subst'-no-op |Δ|≤i τ₂₂)
subst'-no-op |Δ|≤i (ty-sum τ₂₁ τ₂₂) = cong₂ _⨁_ (subst'-no-op |Δ|≤i τ₂₁) (subst'-no-op |Δ|≤i τ₂₂)
subst'-no-op |Δ|≤i (ty-arr τ₂₁ τ₂₂) = cong₂ _⇒_ (subst'-no-op |Δ|≤i τ₂₁) (subst'-no-op |Δ|≤i τ₂₂)
subst'-no-op |Δ|≤i (ty-all τ₂) = cong ∀'_ (subst'-no-op (s≤s |Δ|≤i) τ₂)








lookupᵧ : ∀ {Γ n i τ₁ τ₂} → lookup n Γ ≡ just τ₁ → lookup n (βᵧ Γ τ₂ i) ≡ just (β# τ₁ τ₂ i)
lookupᵧ {Γ} {n} {i} {τ₁} {τ₂} lookupN with Γ 
... | Γ' , τ₁' with n 
...             | zero  rewrite (just-injective lookupN) = refl
...             | suc n' = lookupᵧ {Γ'} {n'} {i} {τ₁} {τ₂} lookupN



n+0 : ∀ {n} → n + 0 ≡ n
n+0 {zero} = refl
n+0 {suc n} = cong suc (n+0 {n})


-- TODO:
-- this lemma is subject to future updates; for example, 
-- MAYBE we need more premises to make it proceed
inc-τ-β≡ : ∀ {τ₁ τ₂ i j} → (inc-τ-i (β# τ₁ τ₂ i) j) ≡ β# (inc-τ-i τ₁ j) (inc-τ-i τ₂ j) (suc (i + j))
inc-τ-β≡ {τ₁} {τ₂} {i} {j} with τ₁
... | Unit = refl
... | Nat = refl
... | Bool = refl
... | ty₁ × ty₂ = cong₂ _×_ (inc-τ-β≡ {ty₁} {τ₂} {i}) (inc-τ-β≡ {ty₂} {τ₂} {i})
... | ty₁ ⨁ ty₂ = cong₂ _⨁_ (inc-τ-β≡ {ty₁} {τ₂} {i}) (inc-τ-β≡ {ty₂} {τ₂} {i})
... | ty₁ ⇒ ty₂ = cong₂ _⇒_ (inc-τ-β≡ {ty₁} {τ₂} {i}) (inc-τ-β≡ {ty₂} {τ₂} {i})
... | ∀' τ = {!   !}
... | TVar n = {!   !}




inc-Γᵧ : ∀ {Γ τ₁ i} → • ⊢ τ₁ ty → inc-Γ (βᵧ Γ τ₁ i) ≡ βᵧ (inc-Γ Γ) τ₁ (suc i)
inc-Γᵧ {∘} {τ₂} {i} •⊢τ₂ty = refl
inc-Γᵧ {Γ , τ₁} {τ₂} {i} •⊢τ₂ty
    rewrite (inc-Γᵧ {Γ} {τ₂} {i} •⊢τ₂ty) rewrite (inc-τ-β≡ {τ₁} {τ₂} {i} {0})
    rewrite (inc-τ-no-op z≤n •⊢τ₂ty) rewrite (n+0 {i}) = refl
    

var-subst'-no-op : ∀ {n τ i} → n < i →  (β# (TVar n) τ i) ≡ TVar n
var-subst'-no-op {n} {τ} {i} n<i with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi
... | true | _ = ⊥-elim (<-irrefl (≡ᵇ⇒≡ n i (subst T (sym n≡ᵇi) tt)) n<i)
... | false | true = refl
... | false | false = ⊥-elim (subst T n<ᵇi (<⇒<ᵇ n<i))


var-subst'-just : ∀ {n τ i} → n ≡ i →  (β# (TVar n) τ i) ≡ τ
var-subst'-just {n} {τ} {i} n≡i with n ≡ᵇ i in n≡ᵇi
... | true = refl
... | false = ⊥-elim (subst T n≡ᵇi (≡⇒≡ᵇ n i n≡i))


var-subst'-pred : ∀ {n τ j} → j < n → (β# (TVar n) τ j) ≡ TVar (pred n)
var-subst'-pred {n} {τ} {j} j<n with n ≡ᵇ j in n≡ᵇj | n <ᵇ j in n<ᵇj
... | true | _ = ⊥-elim (<-irrefl (sym (≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt))) j<n)
... | false | true = ⊥-elim (<-irrefl refl (<-trans j<n (<ᵇ⇒< n j (subst T (sym n<ᵇj) tt))))
... | false | false = refl


var-subst'-dec : ∀ {n τ i j} → n ≡ suc i → j < n → (β# (TVar n) τ j) ≡ TVar i
var-subst'-dec {n} {τ} {i} {j} n≡i' j<n with n ≡ᵇ j in n≡ᵇj | n <ᵇ j in n<ᵇj
... | true | _ = ⊥-elim (<-irrefl (sym (≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt))) j<n)
... | false | true = ⊥-elim (<-irrefl refl (<-trans j<n (<ᵇ⇒< n j (subst T (sym n<ᵇj) tt))))
... | false | false = cong TVar (cong pred n≡i')

<suci : ∀ {i} → i < suc i
<suci {i} = s≤s (≤-reflexive refl)

-- TODO: 
-- this lemma should have one last case for discussion.
-- unfortunately, the TVar case can be tricky since we need to discuss the relation among n, i, j.
-- as a reminder, these premises MAYBE redundant, and they are subject to future updates.
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
... | ty-all τall rewrite (inc-τ-β≡ {τ₂} {τₐ} {i} {0}) rewrite (n+0 {i}) =
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



∀bodyTy : ∀ {Δ τ} → Δ ⊢ ∀' τ ty → (suc Δ) ⊢ τ ty
∀bodyTy {Δ} {τ} Δ∀τTy with Δ∀τTy
... | ty-all τ = τ


subst'-τ : ∀ {Δ Γ i τ₁ τ₂ body} →
                 (• ⊢ τ₁ ty) →
                 (Δ ≡ i) →
                 ((★ ++' Δ) ⨟ Γ ⊢ body ⦂ τ₂) →
                 (Δ ⨟ (βᵧ Γ τ₁ i) ⊢ (β' body τ₁ i) ⦂ (β# τ₂ τ₁ i))
subst'-τ •⊢τ₁ty |Δ|≡i (τ-true)       = τ-true
subst'-τ •⊢τ₁ty |Δ|≡i (τ-false)       = τ-false
subst'-τ •⊢τ₁ty |Δ|≡i (τ-zero)        = τ-zero
subst'-τ •⊢τ₁ty |Δ|≡i (τ-suc τ₁)       = τ-suc (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-pred τ₁)      = τ-pred (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-zero? τ₁)     = τ-zero? (subst'-τ •⊢τ₁ty |Δ|≡i τ₁)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-if τ₁ τ₂ τ₃)      = τ-if (subst'-τ •⊢τ₁ty |Δ|≡i τ₁) (subst'-τ •⊢τ₁ty |Δ|≡i τ₂) (subst'-τ •⊢τ₁ty |Δ|≡i τ₃)      
subst'-τ •⊢τ₁ty |Δ|≡i (τ-cons τ₁ τ₂) = τ-cons (subst'-τ •⊢τ₁ty |Δ|≡i τ₁) (subst'-τ •⊢τ₁ty |Δ|≡i τ₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-fst τ₁×₂)     = τ-fst (subst'-τ •⊢τ₁ty |Δ|≡i τ₁×₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-snd τ₁×₂)     = τ-snd (subst'-τ •⊢τ₁ty |Δ|≡i τ₁×₂)
subst'-τ •⊢τ₁ty |Δ|≡i (τ-app fTy eTy)      = τ-app (subst'-τ •⊢τ₁ty |Δ|≡i fTy) (subst'-τ •⊢τ₁ty |Δ|≡i eTy)
subst'-τ  {Δ} {Γ} {i} {τ₁} {τ₂} •⊢τ₁ty |Δ|≡i (τ-inl  {Δ'} {Γ'} {e} {τ1} {τ2} ΔTy lTy) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
    in τ-inl (subst'-ty  ΔTy Δ⊢τ₁ty) (subst'-τ •⊢τ₁ty |Δ|≡i lTy)
subst'-τ  {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-inr  {Δ'} {Γ'} {e} {τ1} {τ2} ΔTy rTy)  = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
    in τ-inr (subst'-ty  ΔTy Δ⊢τ₁ty) (subst'-τ •⊢τ₁ty |Δ|≡i rTy)
subst'-τ {Δ₁} {Γ} {i} {τ₁} {τ₂} {Fix τ₂ e₁} •⊢τ₁ty |Δ|≡i (τ-fix {Δ = suc Δ₁} {Γ'} {τ} {e} ΔTy bodyTy) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ₁} {•} •⊢τ₁ty
        Δ₁⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ₁) Δ++•⊢τ₁ty
        Δ₁⊢τ'ty = subst'-ty  ΔTy Δ₁⊢τ₁ty
        ih = (subst'-τ •⊢τ₁ty |Δ|≡i bodyTy)
    in
    τ-fix Δ₁⊢τ'ty ih
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-var {Δ'} {Γ'} {n} {τ₃} ΔTy lookupN) = 
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        Δ⊢τ₂'ty = subst'-ty ΔTy Δ⊢τ₁ty
    in τ-var Δ⊢τ₂'ty (lookupᵧ {Γ} {n} {i} lookupN)
subst'-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-lam {Δ'} {Γ'} {τ₃} {τ₄} {e} ΔTy bodyTy) =
    let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
        Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
        Δ⊢τ₃'ty = subst'-ty ΔTy Δ⊢τ₁ty
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
        Δ⊢τ₂'ty = subst'-ty ΔTy Δ⊢τ₁ty
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



-- subst''-τ : ∀ {Δ Γ i τ₁ τ₂ body} →
--                  (• ⊢ τ₁ ty) →
--                  (Δ ≡ i) →
--                  ((★ ++' Δ) ⨟ Γ ⊢ body ⦂ τ₂) →
--                  (Δ ⨟ Γ ⊢ (β' body τ₁ i) ⦂ (β# τ₂ τ₁ i))
-- subst''-τ {Δ} {Γ} {i} {τ₁} {τ₂} {body} •⊢τ₁ty |Δ|≡i (τ-lam {Δ'} {Γ'} {τ₃} {τ₄} {e} ΔTy bodyTy) =
--     --     let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
--     --     Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
--     --     Δ⊢τ₃'ty = subst'-ty ΔTy Δ⊢τ₁ty
--     --     ih = subst'-τ •⊢τ₁ty |Δ|≡i bodyTy 
--     -- in τ-lam Δ⊢τ₃'ty ih
--     let Δ++•⊢τ₁ty = ty-weaken {Δ} {•} {τ₁} •⊢τ₁ty
--         Δ⊢τ₁ty = subst (λ z → (z ⊢ τ₁ ty)) (concat-id' Δ) Δ++•⊢τ₁ty
--         Δ⊢τ₃'ty = subst'-ty ΔTy Δ⊢τ₁ty
--         ih = subst''-τ •⊢τ₁ty |Δ|≡i bodyTy
--     in τ-lam Δ⊢τ₃'ty {!   !}
-- subst''-τ •⊢τ₁ty |Δ|≡i _      = {!   !}