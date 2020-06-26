open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Var 

module Substitution where

open import Environment using (Env)
open Env {{...}}
open import GenericSubstitution public
open import Renaming public

module ABTOps (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig public
  open import Environment
  open Renaming.WithOpSig Op sig public
  open import Map Op sig
  open import MapFusion Op sig
  open Composition Op sig using (ComposableProps; compose-sub; drop-seq)
  
  Subst : Set
  Subst = GSubst ABT

  ⟪_⟫ : Subst → ABT → ABT
  ⟪_⟫ = map

  ⟪_⟫ₐ : Subst → {b : ℕ} → Arg b → Arg b
  ⟪_⟫ₐ = map-arg

  ⟪_⟫₊ : Subst → {bs : List ℕ} → Args bs → Args bs
  ⟪_⟫₊ = map-args

  instance
    Subst-Composable : Composable ABT ABT ABT
    Subst-Composable = record { ⌈_⌉ = ⟪_⟫ ; val₂₃ = λ M → M }

  sub-up-seq : ∀ k (σ : Subst) → ↑ k ⨟ σ ≡ drop k σ
  sub-up-seq k σ rewrite up-seq k σ | map-sub-id (drop k σ) = refl

  sub-cons-seq : ∀ x σ₁ σ₂ → (x • σ₁) ⨟ σ₂ ≡ ⟪ σ₂ ⟫ x • (σ₁ ⨟ σ₂)
  sub-cons-seq x σ₁ σ₂ rewrite cons-seq x σ₁ σ₂ = refl

  sub-head : ∀ M (σ : Subst) → ⟅ M • σ ⟆ 0 ≡ M
  sub-head M σ = refl

  sub-tail : ∀ (M : ABT) (σ : Subst) → (↑ 1 ⨟ M • σ) ≡ σ
  sub-tail M σ rewrite sub-up-seq 1 (M • σ) | drop-0 σ = refl

  sub-suc : ∀ (M : ABT) σ x → ⟪ M • σ ⟫ (` suc x) ≡ ⟪ σ ⟫ (` x)
  sub-suc M σ x = refl

  shift-eq : ∀ x k → ⟪ ↑ k ⟫ (` x) ≡ ` (k + x)
  shift-eq x k = refl

  sub-idL : (σ : Subst) → id ⨟ σ ≡ σ
  sub-idL σ rewrite sub-up-seq 0 σ | drop-0 σ = refl

  sub-dist :  ∀ σ τ M → ((M • σ) ⨟ τ) ≡ ((⟪ τ ⟫ M) • (σ ⨟ τ))
  sub-dist σ τ M rewrite sub-cons-seq M σ τ = refl

  sub-op : ∀ (σ : Subst) op args → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args  ⦆
  sub-op σ op args = refl

  sub-nil : ∀ (σ : Subst) → ⟪ σ ⟫₊ nil ≡ nil
  sub-nil σ = refl

  sub-cons : ∀ (σ : Subst) b bs (arg : Arg b) (args : Args bs)
    → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
  sub-cons σ b bs arg args = refl

  sub-η : ∀ σ x → ⟅ ⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ) ⟆ x ≡ ⟅ σ ⟆ x
  sub-η σ 0 = refl
  sub-η σ (suc x) rewrite sub-up-seq 1 σ | drop-add 1 σ x = refl

  rename→subst : Rename → Subst
  rename→subst (↑ k) = ↑ k 
  rename→subst (x • ρ) = ` x • rename→subst ρ

  rename→subst≈ : (ρ : Rename) → ρ ≈ rename→subst ρ
  rename→subst≈ (↑ k) = λ x → refl
  rename→subst≈ (x • ρ) zero = refl
  rename→subst≈ (x • ρ) (suc y) = rename→subst≈ ρ y
  
  rename-subst : ∀ ρ M → rename ρ M ≡ ⟪ rename→subst ρ ⟫ M
  rename-subst ρ M = map-cong M (rename→subst≈ ρ) MCE
      where
      MCE : ∀ {ρ : Rename} {σ : Subst} → ρ ≈ σ → ext ρ ≈ ext σ
      MCE {ρ} {σ} ρ≈σ zero = refl
      MCE {ρ} {σ} ρ≈σ (suc x) rewrite inc-shift ρ x | inc-shift σ x
          | sym (ρ≈σ x) = refl
    
  incs=⨟↑ : ∀ σ → ⟰ σ ≡ σ ⨟ ↑ 1
  incs=⨟↑ (↑ k) rewrite sub-up-seq k (↑ 1) | +-comm k 1 = refl
  incs=⨟↑ (M • σ) = begin
      ⟰ (M • σ)              ≡⟨⟩
      (rename (↑ 1) M • ⟰ σ) ≡⟨ cong₂ _•_ (rename-subst (↑ 1) M)(incs=⨟↑ σ) ⟩
      ⟪ ↑ 1 ⟫ M • (σ ⨟ ↑ 1)     ≡⟨ sym (sub-cons-seq M σ (↑ 1)) ⟩
      M • σ ⨟ ↑ 1  ∎

  exts-cons-shift : ∀ (σ : Subst) → ext σ ≡ (` 0 • (σ ⨟ ↑ 1))
  exts-cons-shift σ rewrite incs=⨟↑ σ = refl 

  exts-suc : ∀ (σ : Subst) x → ⟅ ext σ ⟆ (suc x) ≡ ⟅ σ ⨟ ↑ 1 ⟆ x
  exts-suc σ x rewrite incs=⨟↑ σ = refl

  seq-subst : ∀ σ τ x → ⟅ σ ⨟ τ ⟆ x ≡ ⟪ τ ⟫ (⟅ σ ⟆ x)
  seq-subst (↑ k) τ x rewrite sub-up-seq k τ | drop-add k τ x = refl
  seq-subst (M • σ) τ zero rewrite sub-cons-seq M σ τ = refl
  seq-subst (M • σ) τ (suc x) rewrite sub-cons-seq M σ τ
      | seq-subst σ τ x = refl


  private
    sub-shift0 : ∀{σ : Subst} (M : ABT) → Shift 0 σ → ⟪ σ ⟫ M ≡ M
    ss0-arg  : ∀{σ} → Shift 0 σ → (b : ℕ) → (arg : Arg b) 
       → ⟪ σ ⟫ₐ {b} arg ≡ arg
    ss0-args  : ∀{σ} → Shift 0 σ → (bs : List ℕ) → (args : Args bs) 
       → ⟪ σ ⟫₊ {bs} args ≡ args
    sub-shift0 {σ}(` x) σ0 rewrite Shift-var σ 0 x σ0 = cong `_ refl
    sub-shift0 {σ}(op ⦅ args ⦆) σ0 = cong (_⦅_⦆ op) (ss0-args σ0 (sig op) args)
    ss0-arg σ0 zero (ast arg) = cong ast (sub-shift0 arg σ0)
    ss0-arg {σ} σ0 (suc b) (bind arg) =
        cong bind (ss0-arg (shift-• (inc-Shift σ0) refl) b arg)
    ss0-args σ0 [] nil = refl
    ss0-args σ0 (b ∷ bs) (cons arg args) =
        cong₂ cons (ss0-arg σ0 b arg) (ss0-args σ0 bs args)
        
  ids : Subst
  ids = id

  sub-id : ∀ {M : ABT} → ⟪ ids ⟫ M ≡ M
  sub-id {M} = (sub-shift0 M (shift-up {k = 0}))

  rename-id : {M : ABT} → rename (↑ 0) M ≡ M
  rename-id {M} rewrite rename-subst (↑ 0) M | sub-id {M} = refl

  sub-idR : ∀ σ → σ ⨟ id ≡ σ 
  sub-idR (↑ k) rewrite sub-up-seq k id | +-comm k 0 = refl
  sub-idR (M • σ) rewrite sub-cons-seq M σ id | sub-idR σ | sub-id {M} = refl

  exts-0 : ∀ (σ : Subst) → ⟅ ext σ ⟆ 0 ≡ ` 0
  exts-0 σ = refl

  exts-suc' : ∀ (σ : Subst) x → ⟅ ext σ ⟆ (suc x) ≡ rename (↑ 1) (⟅ σ ⟆ x)
  exts-suc' σ x rewrite inc-shift σ x = refl

  exts-suc-rename : ∀ σ x → ⟅ ext σ ⟆ (suc x) ≡ rename (↑ 1) (⟪ σ ⟫ (` x))
  exts-suc-rename σ x rewrite inc-shift σ x = refl

  instance
    _ : Composable ABT ABT ABT
    _ = record { ⌈_⌉ = ⟪_⟫ ; val₂₃ = λ M → M }

    _ : ComposableProps ABT ABT ABT
    _ = record { var→val₂₃ = λ x → refl ; quote-val₂₃ = λ v₂ → refl
          ; val₂₃-shift = λ v₂ → refl ; quote-var→val₁ = λ x → refl
          ; quote-map = λ σ₂ v₁ → refl }

  sub-sub : ∀ {M σ₁ σ₂} → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
  sub-sub {M}{σ₁}{σ₂} = map-map-fusion M (λ x → sym (compose-sub σ₁ σ₂ x))

  sub-assoc : ∀ {σ τ θ} → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  sub-assoc {↑ k} {τ} {θ}= begin
    (↑ k ⨟ τ) ⨟ θ     ≡⟨ cong (λ □ → □ ⨟ θ) (sub-up-seq _ _) ⟩
    (drop k τ) ⨟ θ    ≡⟨ sym (drop-seq _ _ _) ⟩
    drop k (τ ⨟ θ)    ≡⟨ sym (sub-up-seq _ _) ⟩
    ↑ k ⨟ (τ ⨟ θ)      ∎
  sub-assoc {M • σ} {τ} {θ} {- rewrite sub-assoc {σ}{τ}{θ}-} = begin
    (M • σ ⨟ τ) ⨟ θ                  ≡⟨ cong (λ □ → □ ⨟ θ) (sub-cons-seq _ _ _) ⟩
    (⟪ τ ⟫ M • (σ ⨟ τ)) ⨟ θ           ≡⟨ sub-cons-seq _ _ _ ⟩
    ⟪ θ ⟫ (⟪ τ ⟫ M) • ((σ ⨟ τ) ⨟ θ)
                                 ≡⟨ cong (λ □ → ⟪ θ ⟫ (⟪ τ ⟫ M) • □) sub-assoc ⟩
    ⟪ θ ⟫ (⟪ τ ⟫ M) • (σ ⨟ (τ ⨟ θ))
                         ≡⟨ cong (λ □ → □ • (σ ⨟ (τ ⨟ θ))) (sub-sub {M}{τ}{θ}) ⟩
    ⟪ τ ⨟ θ ⟫ M • (σ ⨟ (τ ⨟ θ))       ≡⟨ sym (sub-cons-seq _ _ _) ⟩ 
    (M • σ) ⨟ (τ ⨟ θ)                 ∎

  subst-zero : ABT → Subst
  subst-zero M = M • id

  _[_] : ABT → ABT → ABT
  N [ M ] =  ⟪ subst-zero M ⟫ N

  subst-zero-exts-cons : ∀{σ M} → ext σ ⨟ subst-zero M ≡ M • σ
  subst-zero-exts-cons {σ}{M} = begin
     ext σ ⨟ subst-zero M  ≡⟨ cong(λ □ → □  ⨟ subst-zero M)(exts-cons-shift _) ⟩
     (` 0 • (σ ⨟ ↑ 1)) ⨟ (M • id) ≡⟨ sub-cons-seq _ _ _ ⟩
     M • ((σ ⨟ ↑ 1) ⨟ (M • id))   ≡⟨ cong (_•_ M) sub-assoc ⟩
     M • (σ ⨟ (↑ 1 ⨟ (M • id)))   ≡⟨ cong (λ □ → M • (σ ⨟ □)) (sub-tail _ _) ⟩
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

  _〔_〕 : ABT → ABT → ABT
  _〔_〕 N M = ⟪ ext (subst-zero M) ⟫ N

  substitution : ∀{M N L} → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
  substitution {M}{N}{L} = commute-subst{N = M}{M = N}{σ = subst-zero L}

  exts-sub-cons : ∀ σ N V → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
  exts-sub-cons σ N V {-rewrite exts-cons-shift σ -} = begin
     (⟪ ext σ ⟫ N) [ V ]                 ≡⟨⟩
     ⟪ subst-zero V ⟫ (⟪ ext σ ⟫ N)      ≡⟨ sub-sub {N}{ext σ}{subst-zero V} ⟩
     ⟪ ext σ ⨟ subst-zero V ⟫ N
                  ≡⟨ cong (λ □ → ⟪ □ ⨟ subst-zero V ⟫ N) (exts-cons-shift σ) ⟩
     ⟪ (` 0 • (σ ⨟ ↑ 1)) ⨟ (V • id) ⟫ N
                               ≡⟨ cong (λ □ → ⟪ □ ⟫ N) (sub-cons-seq _ _ _) ⟩
     ⟪ V • ((σ ⨟ ↑ 1) ⨟ (V • id)) ⟫ N    ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) sub-assoc ⟩
     ⟪ V • (σ ⨟ (↑ 1 ⨟ (V • id))) ⟫ N
                            ≡⟨ cong (λ □ → ⟪ V • (σ ⨟ □) ⟫ N) (sub-tail _ _) ⟩
     ⟪ V • (σ ⨟ id) ⟫ N           ≡⟨ cong (λ □ → ⟪ V • □ ⟫ N) (sub-idR _)  ⟩
     ⟪ V • σ ⟫ N             ∎

  exts-ext : ∀ σ τ → ((x : ℕ) → ⟅ σ ⟆ x ≡ ⟅ τ ⟆ x)
           → ((x : ℕ) → ⟅ ext σ ⟆ x ≡ ⟅ ext τ ⟆ x)
  exts-ext σ τ eq 0
      rewrite exts-cons-shift σ | exts-cons-shift τ = refl
  exts-ext σ τ eq (suc x)
      rewrite exts-cons-shift σ | exts-cons-shift τ
            | seq-subst σ (↑ 1) x | seq-subst τ (↑ 1) x
            | inc-shift σ x | inc-shift τ x | eq x = refl

  subst-extensionality : ∀{M : ABT}{σ τ : Subst}
      → (∀ x → ⟅ σ ⟆ x ≡ ⟅ τ ⟆ x)
      → ⟪ σ ⟫ M ≡ ⟪ τ ⟫ M
  sub-arg-ext : ∀{n} {A : Arg n} {σ τ : Subst}
           → (∀ x → ⟅ σ ⟆ x ≡ ⟅ τ ⟆ x)
           → ⟪ σ ⟫ₐ A ≡ ⟪ τ ⟫ₐ A
  sub-args-ext : ∀{S} {Ms : Args S} {σ τ : Subst}
           → (∀ x → ⟅ σ ⟆ x ≡ ⟅ τ ⟆ x)
           → ⟪ σ ⟫₊ Ms ≡ ⟪ τ ⟫₊ Ms

  abstract 
    subst-extensionality {` x} {σ} {τ} eq = eq x
    subst-extensionality {op ⦅ As ⦆} {σ} {τ} eq =
        cong (λ □ → op ⦅ □ ⦆) (sub-args-ext eq)

    sub-arg-ext {A = ast M}{σ}{τ} eq =
        cong ast (subst-extensionality {M}{σ}{τ} eq)
    sub-arg-ext {A = bind A}{σ}{τ} eq
        with exts-ext σ τ eq
    ... | ee = cong bind (sub-arg-ext ee)

    sub-args-ext {Ms = nil} eq = refl
    sub-args-ext {Ms = cons A Ms} eq =
        cong₂ cons (sub-arg-ext eq) (sub-args-ext eq)
