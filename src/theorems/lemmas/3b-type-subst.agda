module theorems.lemmas.3b-type-subst where

open import SystemF.definitions
open import theorems.lemmas.0-math
open import theorems.lemmas.1a-term-env
open import theorems.lemmas.1b-type
open import theorems.lemmas.2a-weakening



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




inc-τ-var-inc : ∀ {n i} → n ≡ i → (inc-τ-i (TVar n) i) ≡ TVar (suc n)
inc-τ-var-inc {n} {i} n≡i with n <ᵇ i in n<ᵇi
... | true = ⊥-elim (<-irrefl n≡i (<ᵇ⇒< n i (subst T (sym n<ᵇi) tt)))
... | false = refl



inc-τ-var-inc2 : ∀ {n i} → (n <ᵇ i) ≡ false → (inc-τ-i (TVar n) i) ≡ TVar (suc n)
inc-τ-var-inc2 {n} {i} n≢ᵇi with n <ᵇ i
... | true = ⊥-elim (subst T n≢ᵇi tt)
... | false = refl




inc-τ-var-no-op : ∀ {n i} → n < i → (inc-τ-i (TVar n) i) ≡ TVar n
inc-τ-var-no-op {n} {i} n<i with n <ᵇ i in n<ᵇi
... | true = refl
... | false = ⊥-elim (subst T n<ᵇi (<⇒<ᵇ n<i))



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
subst'-no-op |Δ|≤i (ty-list τ) = cong List (subst'-no-op |Δ|≤i τ)
subst'-no-op |Δ|≤i (ty-arr τ₂₁ τ₂₂) = cong₂ _⇒_ (subst'-no-op |Δ|≤i τ₂₁) (subst'-no-op |Δ|≤i τ₂₂)
subst'-no-op |Δ|≤i (ty-all τ₂) = cong ∀'_ (subst'-no-op (s≤s |Δ|≤i) τ₂)




inc-τ-β≡ : ∀ {τ₁ τ₂ i j} → j ≤ i → • ⊢ τ₂ ty → (inc-τ-i (β# τ₁ τ₂ i) j) ≡ β# (inc-τ-i τ₁ j) (inc-τ-i τ₂ j) (suc i)
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty with τ₁
... | Unit = refl
... | Nat = refl
... | Bool = refl
... | ty₁ × ty₂ = cong₂ _×_ (inc-τ-β≡ {ty₁} {τ₂} {i} {j} j≤i •⊢τ₂ty) (inc-τ-β≡ {ty₂} {τ₂} {i} {j} j≤i •⊢τ₂ty)
... | ty₁ ⨁ ty₂ = cong₂ _⨁_ (inc-τ-β≡ {ty₁} {τ₂} {i} {j} j≤i •⊢τ₂ty) (inc-τ-β≡ {ty₂} {τ₂} {i} {j} j≤i •⊢τ₂ty)
... | ty₁ ⇒ ty₂ = cong₂ _⇒_ (inc-τ-β≡ {ty₁} {τ₂} {i} {j} j≤i •⊢τ₂ty) (inc-τ-β≡ {ty₂} {τ₂} {i} {j} j≤i •⊢τ₂ty)
... | List ty   = cong List (inc-τ-β≡ {ty} {τ₂} {i} {j} j≤i •⊢τ₂ty)
... | ∀' ty =
    let
        -- closedness: inc-τ τ₂ ≡ τ₂ and inc-τ-i τ₂ (suc j) ≡ τ₂
        p0 : inc-τ-i τ₂ 0 ≡ τ₂
        p0 = inc-τ-no-op {j = 0} z≤n •⊢τ₂ty

        psj : inc-τ-i τ₂ (suc j) ≡ τ₂
        psj = inc-τ-no-op {j = suc j} z≤n •⊢τ₂ty

        pj : inc-τ-i τ₂ j ≡ τ₂
        pj = inc-τ-no-op {j = j} z≤n •⊢τ₂ty

        •incτ₂ty : • ⊢ inc-τ τ₂ ty
        •incτ₂ty = subst (λ z → • ⊢ z ty) (sym p0) •⊢τ₂ty

        ih : inc-τ-i (β# ty (inc-τ τ₂) (suc i)) (suc j) ≡
             β# (inc-τ-i ty (suc j)) (inc-τ-i (inc-τ τ₂) (suc j)) (suc (suc i))
        ih = inc-τ-β≡ {ty} {inc-τ τ₂} {suc i} {suc j} (s≤s j≤i) •incτ₂ty

        comm : inc-τ-i (inc-τ τ₂) (suc j) ≡ inc-τ (inc-τ-i τ₂ j)
        comm = trans (trans (cong (λ z → inc-τ-i z (suc j)) p0) psj)
                     (sym (trans (cong inc-τ pj) p0))

        ih' : inc-τ-i (β# ty (inc-τ τ₂) (suc i)) (suc j) ≡
              β# (inc-τ-i ty (suc j)) (inc-τ (inc-τ-i τ₂ j)) (suc (suc i))
        ih' = subst (λ σ → inc-τ-i (β# ty (inc-τ τ₂) (suc i)) (suc j) ≡
                           β# (inc-τ-i ty (suc j)) σ (suc (suc i)))
                    comm ih
    in cong ∀'_ ih'
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty | TVar n rewrite  (inc-τ-no-op {j = j} z≤n •⊢τ₂ty) with n ≡ᵇ j in n≡ᵇj 
... | true with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi
...                      | true | _ = 
    let lhs = inc-τ-no-op {j = j} z≤n •⊢τ₂ty
        n≡j = ≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt)
        n≡i = ≡ᵇ⇒≡ n i (subst T (sym n≡ᵇi) tt)
        rhs : β# (TVar (suc n)) τ₂ (suc i) ≡ τ₂
        rhs = var-subst'-just (cong suc n≡i)
        rhs' = subst (λ z → β# z τ₂ (suc i) ≡ τ₂) (sym (inc-τ-var-inc n≡j)) rhs
    in trans lhs (sym rhs')
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty  | TVar n | true  | false | true with n <ᵇ j in n<ᵇj
... | true = 
    let n≡j = ≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt)
        n<j = <ᵇ⇒< n j (subst T (sym n<ᵇj) tt)
    in ⊥-elim (<-irrefl n≡j n<j)
... | false = 
    let n≢i = ≢ᵇ⇒≢ {n} {i} n≡ᵇi
        n<i = <ᵇ⇒< n i (subst T (sym n<ᵇi) tt)
        n'<i' = <⇒suc<suc n<i
    in sym (var-subst'-no-op {τ = τ₂} n'<i')
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty  | TVar n | true  | false | false = 
    let 
        n≡j = ≡ᵇ⇒≡ n j (subst T (sym n≡ᵇj) tt)
        n≤i = subst (λ z → z ≤ i) (sym n≡j) j≤i
    in ⊥-elim (subst T n<ᵇi (<⇒<ᵇ (≤∧≢⇒< n≤i (≢ᵇ⇒≢ n≡ᵇi))))
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty  | TVar n | false with n <ᵇ j in n<ᵇj
... | true with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi
...                        | true | _ = 
    let n<j = <ᵇ⇒< n j (subst T (sym n<ᵇj) tt)
        n<i = <-≤-trans n<j j≤i
        n≡i = ≡ᵇ⇒≡ n i (subst T (sym n≡ᵇi) tt)
    in ⊥-elim (<-irrefl n≡i n<i)
...                        | false | false = 
    let n<j = <ᵇ⇒< n j (subst T (sym n<ᵇj) tt)
        n<i = <-≤-trans n<j j≤i
        n≰i = subst T n<ᵇi (<⇒<ᵇ n<i)
    in ⊥-elim n≰i
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty  | TVar n | false | true  | false | true with n ≡ᵇ suc i in n≡ᵇi' | n <ᵇ suc i in n<ᵇi'
... | true | _ = 
    let n<j = <ᵇ⇒< n j (subst T (sym n<ᵇj) tt)
        n<i = <-≤-trans n<j j≤i
        n≡i' = ≡ᵇ⇒≡ n (suc i) (subst T (sym n≡ᵇi') tt)
    in ⊥-elim (<-irrefl refl (<-trans (subst (λ z → z < i) n≡i' n<i) <suci))
... | false | true = inc-τ-var-no-op (<ᵇ⇒< n j (subst T (sym n<ᵇj) tt))
... | false | false = 
    let n<i = <ᵇ⇒< n i (subst T (sym n<ᵇi) tt)
        n<i' = <-trans n<i (<suci {i})
        n≰i' = subst T n<ᵇi' (<⇒<ᵇ n<i')
    in ⊥-elim n≰i'
inc-τ-β≡ {τ₁} {τ₂} {i} {j} j≤i •⊢τ₂ty  | TVar n | false | false with n ≡ᵇ i in n≡ᵇi | n <ᵇ i in n<ᵇi
... | true | _ = inc-τ-no-op z≤n •⊢τ₂ty
... | false | true = inc-τ-var-inc2 {n} {j} n<ᵇj
... | false | false with n
...                     | zero =  ⊥-elim (subst T n<ᵇj (<⇒<ᵇ  (≤∧≢⇒< {n = j} z≤n (≢ᵇ⇒≢ n≡ᵇj))))
...                     | suc n' = 
    let j<sn' : j < suc n'
        j<sn' = ≤∧≢⇒< (≮⇒≥ (λ p → subst T n<ᵇj (<⇒<ᵇ p))) (λ eq → ≢ᵇ⇒≢ n≡ᵇj (sym eq))
        j≤n' = <suc⇒≤ j<sn'
        n'≮j = ≤⇒≮ᵇ j≤n'
    in inc-τ-var-inc2 {n = n'} {i = j} n'≮j

