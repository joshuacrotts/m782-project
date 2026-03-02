module examples.prelude where

open import Data.Nat using (ℕ; zero; suc) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Bool using (true; false) renaming (Bool to 𝔹) public
open import Data.Product using (Σ; Σ-syntax; _,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public

open import SystemF.terms public
open import SystemF.types public
open import SystemF.typing public
open import SystemF.values public
open import SystemF.semantics public
open import progress public
open import preservation public
open import lemma using (weaken-closed) public

import SystemF.context as C
open C using (TypeContext; •; TermContext; ∘; lookup) public

open import examples.eval-driver public