{-# OPTIONS --without-K #-}
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Sig
open import Var 

module Substitution where

open import Structures hiding (module WithOpSig) public
open import GSubst public
open import GenericSubstitution public
open import Renaming public

module ABTOps (Op : Set) (sig : Op → List Sig)  where

  open import AbstractBindingTree Op sig
  open Renaming.WithOpSig Op sig public
  open import Map Op sig
  open import MapFusion Op sig
  open Composition Op sig using (ComposableProps; compose-sub; drop-seq)
  
  Subst : Set
  Subst = GSubst ABT

  ⟪_⟫ : Subst → ABT → ABT
  ⟪_⟫ = map

  ⟪_⟫ₐ : Subst → {b : Sig} → Arg b → Arg b
  ⟪_⟫ₐ = map-arg

  ⟪_⟫₊ : Subst → {bs : List Sig} → Args bs → Args bs
  ⟪_⟫₊ = map-args

  instance
    ABT³-Composable : Composable ABT ABT ABT
    ABT³-Composable = record { ⌈_⌉ = ⟪_⟫ ; val₂₃ = λ M → M
                      ; ⌈⌉-var→val = λ σ x → refl }
    ABT³-ComposableProps : ComposableProps ABT ABT ABT
    ABT³-ComposableProps = record { var→val₂₃ = λ x → refl
          ; quote-val₂₃ = λ v₂ → refl ; val₂₃-shift = λ v₂ → refl
          ; quote-var→val₁ = λ x → refl ; quote-map = λ σ₂ v₁ → refl }

  sub-up-seq : ∀ k (σ : Subst) → ↑ k ⨟ σ ≡ drop k σ
  sub-up-seq k σ = up-seq k σ

  sub-cons-seq : ∀ x σ₁ σ₂ → (x • σ₁) ⨟ σ₂ ≡ ⟪ σ₂ ⟫ x • (σ₁ ⨟ σ₂)
  sub-cons-seq x σ₁ σ₂ rewrite cons-seq x σ₁ σ₂ = refl

  sub-head : ∀ M (σ : Subst) → (M • σ) 0 ≡ M
  sub-head M σ = refl

  sub-tail : ∀ (M : ABT) (σ : Subst) → (↑ 1 ⨟ M • σ) ≡ σ
  sub-tail M σ = sub-up-seq 1 (M • σ)

  sub-suc : ∀ (M : ABT) σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
  sub-suc M σ x = refl

  shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
  shift-eq x k = refl

  sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
  sub-idL σ = sub-up-seq 0 σ

  sub-dist :  ∀ σ τ M → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist σ τ M rewrite sub-cons-seq M σ τ = refl

  sub-op : ∀ (σ : Subst) op args → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args  ⦆
  sub-op σ op args = refl

  sub-nil : ∀ (σ : Subst) → ⟪ σ ⟫₊ nil ≡ nil
  sub-nil σ = refl

  sub-cons : ∀ (σ : Subst) b bs (arg : Arg b) (args : Args bs)
     → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
  sub-cons σ b bs arg args = refl

  sub-ast : ∀ (σ : Subst) (M : ABT)
     → ⟪ σ ⟫ₐ (ast M) ≡ ast (⟪ σ ⟫ M)
  sub-ast σ M = refl

  sub-bind : ∀ (σ : Subst) {b} (arg : Arg b)
     → ⟪ σ ⟫ₐ (bind arg) ≡ bind (⟪ ext σ ⟫ₐ arg)
  sub-bind σ M = refl

  sub-η : ∀ σ x → (⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ)) x ≡ (σ) x
  sub-η σ 0 = refl
  sub-η σ (suc x) = refl

  rename→subst : Rename → Subst
  rename→subst ρ x = ` (ρ x)

  rename→subst≃ : (ρ : Rename) → ρ ≃ rename→subst ρ
  rename→subst≃ ρ x = refl
  
  rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
  rename-subst ρ M = map-cong M (rename→subst≃ ρ) MCE 
      where
      MCE : ∀ {ρ : Rename} {σ : Subst} → ρ ≃ σ → ext ρ ≃ ext σ
      MCE {ρ} {σ} ρ≃σ zero = refl
      MCE {ρ} {σ} ρ≃σ (suc x) rewrite sym (ρ≃σ x) = refl

  incs=⨟↑ : ∀ (σ : Subst) → ⟰ σ ≡ σ ⨟ ↑ 1
  incs=⨟↑ σ = extensionality G
      where
      G : (x : Var) → ⟰ σ x ≡ (σ ⨟ ↑ 1) x
      G x = rename-subst suc (σ x)

  exts-cons-shift : ∀ (σ : Subst) → ext σ ≡ (` 0 • (σ ⨟ ↑ 1))
  exts-cons-shift σ rewrite incs=⨟↑ σ = refl 

  exts-suc : ∀ (σ : Subst) x → (ext σ) (suc x) ≡ (σ ⨟ ↑ 1) x
  exts-suc σ x = rename-subst suc (σ x)
  
  seq-subst : ∀ σ τ x → (σ ⨟ τ) x ≡ ⟪ τ ⟫ ((σ) x)
  seq-subst σ τ x = refl
  
  sub-id : ∀ {M : ABT} → ⟪ id ⟫ M ≡ M
  sub-id {M} = (sub-shift0 M λ x → refl)
    where
    sub-shift0 : ∀{σ : Subst} (M : ABT) → Shift 0 σ → ⟪ σ ⟫ M ≡ M
    ss0-arg  : ∀{σ} → Shift 0 σ → (b : Sig) → (arg : Arg b) 
       → ⟪ σ ⟫ₐ {b} arg ≡ arg
    ss0-args  : ∀{σ} → Shift 0 σ → (bs : List Sig) → (args : Args bs) 
       → ⟪ σ ⟫₊ {bs} args ≡ args
    sub-shift0 {σ}(` x) σ0 rewrite Shift-var σ 0 x σ0 = cong `_ refl
    sub-shift0 {σ}(op ⦅ args ⦆) σ0 = cong (_⦅_⦆ op) (ss0-args σ0 (sig op) args)
    ss0-arg σ0 b (ast arg) = cong ast (sub-shift0 arg σ0)
    ss0-arg {σ} σ0 (ν b) (bind arg) = {- (shift-• (inc-Shift σ0) refl) -}
        cong bind (ss0-arg S0 b arg)
        where
        S0 : Shift 0 (ext σ)
        S0 zero = refl
        S0 (suc x) rewrite σ0 x = refl
    ss0-arg σ0 b (clear arg) = refl
    ss0-args σ0 [] nil = refl
    ss0-args σ0 (b ∷ bs) (cons arg args) =
        cong₂ cons (ss0-arg σ0 b arg) (ss0-args σ0 bs args)

  rename-id : {M : ABT} → rename (↑ 0) M ≡ M
  rename-id {M} rewrite rename-subst (↑ 0) M | sub-id {M} = refl

  sub-idR : ∀ (σ : Subst) → σ ⨟ id ≡ σ 
  sub-idR σ = extensionality (λ _ → sub-id)

  exts-0 : ∀ (σ : Subst) → (ext σ) 0 ≡ ` 0
  exts-0 σ = refl

  exts-suc' : ∀ (σ : Subst) x → (ext σ) (suc x) ≡ rename (↑ 1) ((σ) x)
  exts-suc' σ x = refl

  exts-suc-rename : ∀(σ : Subst) x → (ext σ)(suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))
  exts-suc-rename σ x = refl

  sub-sub : ∀ {M : ABT}{σ₁ σ₂ : Subst} → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
  sub-sub {M}{σ₁}{σ₂} = map-map-fusion M (λ x → sym (compose-sub σ₁ σ₂ x))

  sub-assoc : ∀ {σ τ θ : Subst} → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  sub-assoc {σ}{τ}{θ} = extensionality (λ x → sub-sub {σ x}{τ}{θ})

  subst-zero : ABT → Subst
  subst-zero M = M • id

  _[_] : ABT → ABT → ABT
  N [ M ] =  ⟪ M • id ⟫ N
  
  subst-zero-exts-cons : ∀{σ : Subst}{M : ABT} → ext σ ⨟ subst-zero M ≡ M • σ
  subst-zero-exts-cons {σ}{M} = begin
     ext σ ⨟ subst-zero M  ≡⟨ cong(λ □ → □  ⨟ subst-zero M)(exts-cons-shift σ) ⟩
     (` 0 • (σ ⨟ ↑ 1)) ⨟ (M • id) ≡⟨ sub-cons-seq _ _ _ ⟩
     M • ((σ ⨟ ↑ 1) ⨟ (M • id))   ≡⟨ cong (_•_ M) (sub-assoc{σ}{↑ 1}{M • id}) ⟩
     M • (σ ⨟ (↑ 1 ⨟ (M • id)))   ≡⟨ cong (λ □ → M • (σ ⨟ □)) (sub-tail M _) ⟩
     M • (σ ⨟ id)                 ≡⟨ cong (_•_ M) (sub-idR _) ⟩
     M • σ                        ∎
  
  subst-commute : ∀{N M σ} → (⟪ ext σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
  subst-commute {N}{M}{σ} =  begin
    (⟪ ext σ ⟫ N) [ ⟪ σ ⟫ M ]           ≡⟨ sub-sub {N}{ext σ} ⟩
    ⟪ ext σ ⨟ subst-zero (⟪ σ ⟫ M) ⟫ N
                          ≡⟨ cong (λ □ → ⟪ □ ⟫ N) subst-zero-exts-cons ⟩
    ⟪ (⟪ σ ⟫ M) • σ ⟫ N    ≡⟨ cong (λ □ → ⟪ ⟪ σ ⟫ M • □ ⟫ N) (sym (sub-idL _)) ⟩
    ⟪ ⟪ σ ⟫ M • (id ⨟ σ) ⟫ N ≡⟨ cong (λ □ → ⟪ □ ⟫ N)(sym (sub-cons-seq _ _ _)) ⟩
    ⟪ M • id ⨟ σ ⟫ N                     ≡⟨⟩
    ⟪ subst-zero M ⨟ σ ⟫ N               ≡⟨ sym (sub-sub {N}{subst-zero M}{σ}) ⟩
    ⟪ σ ⟫ (⟪ subst-zero M ⟫ N)           ≡⟨⟩
    ⟪ σ ⟫ (N [ M ])      ∎

  commute-subst : ∀{N M σ} → ⟪ σ ⟫ (N [ M ]) ≡ (⟪ ext σ ⟫ N) [ ⟪ σ ⟫ M ]
  commute-subst {N}{M}{σ} = sym (subst-commute {N}{M}{σ})

  rename→subst-inc : ∀ ρ → rename→subst (⟰ ρ) ≡ ⟰ (rename→subst ρ)
  rename→subst-inc ρ = refl

  rename-subst-commute : ∀{N M ρ}
     → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
  rename-subst-commute {N}{M}{ρ} = begin
      (rename (ext ρ) N) [ rename ρ M ]
          ≡⟨ cong₂ _[_] (rename-subst (ext ρ) N) (rename-subst ρ M) ⟩
      (⟪ rename→subst ((var→val 0) • ⟰ ρ) ⟫ N) [ ⟪ rename→subst ρ ⟫ M ]
          ≡⟨ cong (λ □ → ⟪ ⟪ rename→subst ρ ⟫ M • id ⟫ (⟪ □ ⟫ N))
                  (extensionality EQ1) ⟩
      ⟪ ⟪ rename→subst ρ ⟫ M • id ⟫ (⟪ (` 0) • rename→subst (⟰ ρ) ⟫ N)
                 ≡⟨ cong (λ □ → ⟪ ⟪ rename→subst ρ ⟫ M • id ⟫ (⟪ (` 0) • □ ⟫ N))
                         (rename→subst-inc ρ) ⟩
      ⟪ ⟪ rename→subst ρ ⟫ M • id ⟫ (⟪ (` 0) • ⟰ (rename→subst ρ) ⟫ N)
          ≡⟨⟩
      (⟪ ext (rename→subst ρ) ⟫ N) [ ⟪ rename→subst ρ ⟫ M ]
          ≡⟨ subst-commute {N}{M}{rename→subst ρ}  ⟩
      ⟪ rename→subst ρ ⟫ (N [ M ])
          ≡⟨ sym (rename-subst ρ (N [ M ])) ⟩
      rename ρ (N [ M ])          ∎
      where
      EQ1 : (x : Var) → rename→subst ((var→val 0) • ⟰ ρ) x
                        ≡ ((` 0) • rename→subst (⟰ ρ)) x
      EQ1 zero = refl
      EQ1 (suc x) = refl

  _〔_〕 : ABT → ABT → ABT
  _〔_〕 N M = ⟪ ext (subst-zero M) ⟫ N

  substitution : ∀{M N L} → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
  substitution {M}{N}{L} = commute-subst{N = M}{M = N}{σ = subst-zero L}

  exts-sub-cons : ∀ σ N V → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
  exts-sub-cons σ N V  = begin
     (⟪ ext σ ⟫ N) [ V ]                 ≡⟨⟩
     ⟪ subst-zero V ⟫ (⟪ ext σ ⟫ N)      ≡⟨ sub-sub {N}{ext σ}{subst-zero V} ⟩
     ⟪ ext σ ⨟ subst-zero V ⟫ N
                  ≡⟨ cong (λ □ → ⟪ □ ⨟ subst-zero V ⟫ N) (exts-cons-shift σ) ⟩
     ⟪ (` 0 • (σ ⨟ ↑ 1)) ⨟ (V • id) ⟫ N
                               ≡⟨ cong (λ □ → ⟪ □ ⟫ N) (sub-cons-seq _ _ _) ⟩
     ⟪ V • ((σ ⨟ ↑ 1) ⨟ (V • id)) ⟫ N
         ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) (sub-assoc{σ}{↑ 1}{V • id}) ⟩
     ⟪ V • (σ ⨟ (↑ 1 ⨟ (V • id))) ⟫ N
            ≡⟨ cong (λ □ → ⟪ V • (σ ⨟ □) ⟫ N) (sub-tail N _) ⟩
     ⟪ V • (σ ⨟ id) ⟫ N           ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) (sub-idR _)  ⟩
     ⟪ V • σ ⟫ N             ∎

  subst-cong : ∀{M : ABT}{σ τ : Subst}
      → (∀ x → σ x ≡ τ x)
      → ⟪ σ ⟫ M ≡ ⟪ τ ⟫ M
  subst-cong {M} {σ} {τ} eq = map-cong M eq ext-cong
