{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Var

module GenericSubProperties {V : Set} (S : Substable V) where

open SNF
open Substable S
open GenericSub V var→val shift
open ComposeGenSubst V var→val shift ⦑_⦒ public

inc-suc : ∀ ρ x → ⧼ gen-inc ρ ⧽ x ≡ shift (⧼ ρ ⧽ x)
inc-suc (↑ k) x = var→val-suc-shift
inc-suc (x₁ • ρ) zero = refl
inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x

extend-suc : ∀ σ v x → ⧼ extend σ v ⧽ (suc x) ≡ shift (⧼ σ ⧽ x)
extend-suc σ v x = inc-suc σ x


sub-tail : ∀{σ : Substitution V}{v : V}
   → (↑ 1 ⨟ v • σ) ≡ σ
sub-tail {↑ k}{v} = refl
sub-tail {w • σ}{v} = refl

inc=⨟↑ : ∀ σ → gen-inc σ ≡ σ ⨟ ↑ 1
inc=⨟↑ (↑ k) rewrite +-comm k 1 = refl
inc=⨟↑ (v • σ) = cong₂ _•_ (shift-⦑↑1⦒ v) (inc=⨟↑ σ)

extend-cons-shift : ∀ σ v → extend σ v ≡ (v • (σ ⨟ ↑ 1))
extend-cons-shift (↑ k) v rewrite +-comm k 1 = refl
extend-cons-shift (w • σ) v rewrite inc=⨟↑ σ | shift-⦑↑1⦒ w = refl

sub-η : ∀ (σ : Substitution V) (x : Var)
      → ⧼ (⦑ σ ⦒ (var→val 0) • (↑ 1 ⨟ σ)) ⧽ x ≡ ⧼ σ ⧽ x
sub-η σ 0 rewrite sub-var→val σ 0 = refl
sub-η σ (suc x) = drop-add 1 σ

sub-idL : (σ : Substitution V)
       → id ⨟ σ ≡ σ
sub-idL (↑ k) = refl
sub-idL (M • σ) = refl

sub-dist :  ∀ {σ : Substitution V} {τ : Substitution V} {M : V}
         → ((M • σ) ⨟ τ) ≡ ((⦑ τ ⦒ M) • (σ ⨟ τ))
sub-dist = refl

seq-subst : ∀ σ τ x → ⧼ σ ⨟ τ ⧽ x ≡ ⦑ τ ⦒ (⧼ σ ⧽ x)
seq-subst (↑ k) τ x rewrite drop-add {x} k τ | sub-var→val τ (k + x) = refl
seq-subst (M • σ) τ zero = refl
seq-subst (M • σ) τ (suc x) = seq-subst σ τ x

extend-id : ∀{σ : Substitution V}
   → (∀ x → ⧼ σ ⧽ x ≡ var→val x)
   → (∀ x → ⧼ extend σ (var→val 0) ⧽ x ≡ var→val x)
extend-id {σ} is-id zero
    rewrite extend-cons-shift σ (var→val 0) = refl
extend-id {σ} is-id (suc x)
    rewrite extend-cons-shift σ (var→val 0) | seq-subst σ (↑ 1) x
    | inc-suc σ x | is-id x | var→val-suc-shift {x} = refl

drop-seq : ∀ k ρ ρ' → drop k (ρ ⨟ ρ') ≡ (drop k ρ ⨟ ρ')
drop-seq k (↑ k₁) ρ' = sym (drop-drop k k₁ ρ')
drop-seq zero (x • ρ) ρ' = refl
drop-seq (suc k) (x • ρ) ρ' = drop-seq k ρ ρ'

