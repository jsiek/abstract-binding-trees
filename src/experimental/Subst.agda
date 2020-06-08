{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_)
open import experimental.ScopedTuple
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Syntax using (Substitution; ↑; _•_; id)
open import Var

module experimental.Subst (Op : Set) (sig : Op → List ℕ) where

open import experimental.ABT Op sig
open import experimental.Map Op sig
open import experimental.Rename Op sig

Subst : Set
Subst = Substitution ABT

SubstIsMap : Map ABT
SubstIsMap = record { “_” = λ M → M ; var→val = `_ ; shift = rename (↑ 1)
                    ; var→val-suc-shift = refl
                    ; “_”-0 = refl }
open Map SubstIsMap renaming (map-abt to ⟪_⟫; map-arg to ⟪_⟫ₐ) public
open Map.S SubstIsMap renaming (⧼_⧽ to ⟦_⟧; g-ext to exts) public
open Map.S SubstIsMap renaming (g-inc to incs;
    g-drop to drops; g-drop-inc to drops-incs; g-drop-add to drop-add)
open ComposeMaps SubstIsMap SubstIsMap ⟪_⟫ using (_⨟_) public

subst-zero : ABT → Subst
subst-zero M = M • id

sub-η : ∀ (σ : Subst) (x : Var)  →  ⟦ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟧ x ≡ ⟦ σ ⟧ x
sub-η σ 0 = refl
sub-η σ (suc x) = drop-add 1 σ
{-# REWRITE sub-η #-}

rename→subst : Rename → Subst
rename→subst (↑ k) = ↑ k 
rename→subst (x • ρ) = ` x • rename→subst ρ

private
  incs-rename-inc : ∀ ρ → incs (rename→subst ρ) ≡ rename→subst (inc ρ)
  incs-rename-inc (↑ k) = refl
  incs-rename-inc (x • ρ) = cong (_•_ (` suc x)) (incs-rename-inc ρ)

exts-rename-ext : ∀ ρ → exts (rename→subst ρ) ≡ rename→subst (ext ρ)
exts-rename-ext (↑ k) = refl
exts-rename-ext (x • ρ) = cong (λ □ → (` 0) • (` suc x) • □) (incs-rename-inc ρ)

rename-subst-interp : ∀ ρ x → (` ⦉ ρ ⦊ x) ≡ ⟦ rename→subst ρ ⟧ x
rename-subst-interp (↑ k) x = refl
rename-subst-interp (y • ρ) zero = refl
rename-subst-interp (y • ρ) (suc x) = rename-subst-interp ρ x

rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
ren-arg-subst : ∀ {n} ρ A → ren-arg {n} ρ A ≡ ⟪ (rename→subst ρ) ⟫ₐ A
ren-args-subst : ∀ ρ bs (As : Tuple bs (λ _ → ABT)) →
    map (λ {b} → ren-arg ρ b) As ≡ map (λ {b} → ⟪ rename→subst ρ ⟫ₐ b) As

rename-subst (↑ k) (` x) = refl
rename-subst (y • ρ) (` zero) = refl
rename-subst (y • ρ) (` suc x) = rename-subst-interp ρ x
rename-subst ρ (op ⦅ As ⦆) = cong (λ □ → op ⦅ □ ⦆) (ren-args-subst ρ (sig op) As)

ren-arg-subst ρ arg = ?
ren-args-subst ρ bs args = ?
