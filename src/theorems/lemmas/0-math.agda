module theorems.lemmas.0-math where

open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Maybe.Properties using (just-injective) public 
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _<_; _≤_; s≤s; z≤n) public
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤∧≢⇒<; <ᵇ⇒<; ≤ᵇ⇒≤; <⇒<ᵇ; ≤⇒≤ᵇ; ≤-pred; <-irrefl; <-≤-trans; ≤-reflexive; m≤n⇒m≤1+n; <-trans; ≮⇒≥) public
open import Data.Bool using (true; false; T) public
open import Data.Bool.Properties using (T?) public
open import Data.Unit using (tt) public
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; sym; cong; cong₂) public
open import Function using (case_of_) public
open import Data.Empty using (⊥; ⊥-elim) public

open import SystemF.definitions


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

<⇒suc<suc : ∀ {m i} → m < i → suc m < suc i
<⇒suc<suc {m} {i} m<i = s≤s m<i

<suci : ∀ {i} → i < suc i
<suci {i} = s≤s (≤-reflexive refl)

n+0 : ∀ {n} → n + 0 ≡ n
n+0 {zero} = refl
n+0 {suc n} = cong suc (n+0 {n})

≤⇒≮ᵇ : ∀ {m n} → n ≤ m → (m <ᵇ n) ≡ false
≤⇒≮ᵇ {m} {n} n≤m with m <ᵇ n | <ᵇ⇒< m n
... | false | _ = refl
... | true  | p = ⊥-elim (<-irrefl refl (<-≤-trans (p tt) n≤m))