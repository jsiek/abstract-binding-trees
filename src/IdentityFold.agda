open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to eq-subst)

module IdentityFold (Op : Set) (sig : Op → List ℕ) where

  open import AbstractBindingTree Op sig
  open import Substitution
  open Rename Op sig
  open Subst Op sig
  open import Fold
  open ArgResult ABT ABT
  open import Preserve Op sig

{-
  open GenericSub2 ABT `_ shift subst (λ {x} → refl) (λ σ x → refl)
-}
  
  res→arg : ∀{b} → ArgRes b → Arg b
  res→arg {zero} M = ast M
  res→arg {suc b} r = bind (res→arg (r (` 0)))

  res→args : ∀{bs} → ArgsRes bs → Args bs
  res→args {[]} rnil = nil
  res→args {b ∷ bs} (rcons r rs) = cons (res→arg r) (res→args rs)
      
  id-is-foldable : Foldable ABT ABT Op sig (Substitution ABT)
  id-is-foldable = record { env = subst-is-env ; ret = λ M → M ;
            fold-free-var = `_ ; fold-op = λ o rs → o ⦅ res→args rs ⦆ }
{-
  open Foldable id-is-foldable renaming (extend to extend-env)
-}

  open Folder id-is-foldable
      renaming (fold to id-fold; fold-arg to id-arg; fold-args to id-args)

  _⊢v_↝_⦂_ : List ⊤ → ABT → ABT → ⊤ → Set
  Δ ⊢v M ↝ M′ ⦂ tt = M ≡ M′
  
  _⊢c_↝_⦂_ : List ⊤ → ABT → ABT → ⊤ → Set
  Δ ⊢c M ↝ M′ ⦂ tt = M ≡ M′

  _⦂_⇒_ : Substitution ABT → List ⊤ → List ⊤ → Set
  σ ⦂ Γ ⇒ Δ = ∀ x → Γ ∋ x ⦂ tt → ⟦ σ ⟧ x ≡ ` x

  extend-pres : ∀ {M′ : ABT}{σ : Substitution ABT}{Γ Δ : List ⊤}{A : ⊤}{M : ABT}
      → (A ∷ Δ) ⊢v M ↝ M′ ⦂ A
      → M ≡ (` 0) × M′ ≡ (` 0)
      → σ ⦂ Γ ⇒ Δ
      → exts σ M′ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {.(` 0)} {σ} {M = .(` 0)} M↝M′ ⟨ refl , refl ⟩ σ⦂ zero ∋x = refl
  extend-pres {.(` 0)} {σ} {M = .(` 0)} M↝M′ ⟨ refl , refl ⟩ σ⦂ (suc x) ∋x
      rewrite extend-suc σ (` 0) x | σ⦂ x ∋x = refl

  id-is-preservable : Preservable ⊤ id-is-foldable
  id-is-preservable = record
                     { 𝒫 = λ x x₁ x₂ → ⊤
                     ; 𝒜 = λ _ M M′ _ → (M ≡ ` 0) × (M′ ≡ ` 0)
                     ; _⦂_⇒_ = _⦂_⇒_
                     ; _⊢v_↝_⦂_ = _⊢v_↝_⦂_
                     ; _⊢c_↝_⦂_ = _⊢c_↝_⦂_
                     ; lookup-pres = λ {σ}{Γ}{Δ}{x} σ⦂ ∋x → sym (σ⦂ x ∋x)
                     ; extend-pres = λ {M′}{σ}{Γ}{Δ} → extend-pres {M′}{σ}{Γ}{Δ}
                     ; ret-pres = λ {v} {Δ} {A} {M} z → z
                     ; var-pres = λ {x} {Δ} {A} _ → refl
                     ; op-pres = {!!}
                     }
