module examples.prelude where

open import Data.Nat using (ℕ; zero; suc) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.Bool using (true; false) renaming (Bool to 𝔹) public
open import Data.Product using (Σ; Σ-syntax; _,_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl) public

open import SystemF.definitions public
open import theorems.progress public
open import theorems.preservation public
open import theorems.lemmas.summary public

open import examples.eval-driver public