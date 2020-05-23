{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Syntax
open import Generic

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-step)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig hiding (rename)

  data WS-arg : ℕ → {b : ℕ} → Arg b → Set
  data WS-args : ℕ → {bs : List ℕ} → Args bs → Set 
  data WS : ℕ → ABT → Set 

  data WS-arg where
    WS-ast : ∀ {n} {M} → WS n M → WS-arg n (ast M)
    WS-bind : ∀ {n b} {A : Arg b} → WS-arg (suc n) A → WS-arg n (bind A)

  data WS-args where
    WS-nil : ∀{n} → WS-args n nil
    WS-cons : ∀{n b bs} {A : Arg b} {As : Args bs}
            → WS-arg n A → WS-args n As → WS-args n (cons A As)

  data WS where
    WS-var : ∀ {n} x → x < n → WS n (` x)
    WS-op : ∀ {n} {op : Op} {args : Args (sig op)}
          → WS-args n args
          → WS n (op ⦅ args ⦆)

  open GenericSub Var (λ x → x) suc

  WSRename : ℕ → Rename → ℕ → Set
  WSRename Γ ρ Δ = ∀ {x} → x < Γ → (⧼ ρ ⧽  x) < Δ

  open Rename Op sig

  Γ∋x→x<Γ : ∀{x : ℕ} {Γ : List ⊤}{A}
     → Γ ∋ x ⦂ A
     → x < length Γ
  Γ∋x→x<Γ {zero} {B ∷ Γ} refl = s≤s z≤n
  Γ∋x→x<Γ {suc x} {B ∷ Γ} Γ∋x = s≤s (Γ∋x→x<Γ {x}{Γ} Γ∋x)

  x<Γ→Γ∋x : ∀{x : ℕ} {Γ : List ⊤}{A}
     → x < length Γ
     → Γ ∋ x ⦂ A
  x<Γ→Γ∋x {zero} {B ∷ Γ}{A} x<Γ = refl
  x<Γ→Γ∋x {suc x} {B ∷ Γ} (s≤s x<Γ) = x<Γ→Γ∋x {x} {Γ} x<Γ

  {- move to new sister module of GenericSub. -Jeremy -}
  inc-suc : ∀ ρ x → ⧼ inc ρ ⧽ x ≡ suc (⧼ ρ ⧽ x)
  inc-suc (↑ k) x = refl
  inc-suc (x₁ • ρ) zero = refl
  inc-suc (x₁ • ρ) (suc x) = inc-suc ρ x
  
  WS-extend : ∀{v : Var} {σ : Substitution Var} {Γ Δ : List ⊤} {A : ⊤}
      → v < length Δ →
      (WSRename (length Γ) σ (length Δ)) →
      (WSRename (length (A ∷ Γ)) (extend σ v) (length (A ∷ Δ)))
  WS-extend v<Δ σΓΔ {zero} (s≤s x<Γ) = ≤-step v<Δ
  WS-extend {v}{σ} v<Δ σΓΔ {suc x} (s≤s x<Γ) rewrite inc-suc σ x = s≤s (σΓΔ x<Γ)

  _⊢_⦂_ : List ⊤ → ABT → ⊤ → Set
  Γ ⊢ M ⦂ _ = WS (length Γ) M
  _⊢v_⦂_ : List ⊤ → Var → ⊤ → Set
  Γ ⊢v x ⦂ _ = x < length Γ
  _⊢c_⦂_ : List ⊤ → ABT → ⊤ → Set
  Γ ⊢c M ⦂ _ = WS (length Γ) M

  open ArgResult Var ABT
  open PresArgResult Op sig _⊢_⦂_ _⊢v_⦂_ _⊢c_⦂_
  open Foldable R

  op-pres : ∀ {op : Op} {Rs : ArgsRes (sig op)} {Γ : List ⊤} {A : ⊤} {As : List ⊤}
     → sig op ∣ Γ ⊢ Rs ⦂ As
     → WS (length Γ) (fold-op op Rs)
  op-pres {op}{Rs}{Γ}{A}{As} ⊢Rs = WS-op (G ⊢Rs)
      where
      H : ∀{b}{R : ArgRes b}{A}{Γ} → b ∣ Γ ⊢r R ⦂ A → WS-arg (b + length Γ) (r-arg R)
      H {zero} {R} {A}{Γ} ⊢R = WS-ast ⊢R
      H {suc b} {R} {A}{Γ} ⊢R =
         let r0 = R 0 in
         let rr = ⊢R {!!} in
         let IH = H {b}{Γ = A ∷ Γ} rr in
         WS-bind {!!}
      G : ∀{bs}{Rs : ArgsRes bs}{As} → bs ∣ Γ ⊢ Rs ⦂ As → WS-args (length Γ) (r-args Rs)
      G {[]} {ArgResult.rnil} PresArgResult.rnilp = WS-nil
      G {b ∷ bs} {ArgResult.rcons R Rs} (PresArgResult.rconsp ⊢R ⊢Rs) = WS-cons {!!} (G {bs} {Rs} ⊢Rs)

  WSPres : Preservable ⊤ R
  WSPres = record
             { _⊢_⦂_ = _⊢_⦂_
             ; _⦂_⇒_ = λ σ Γ Δ → WSRename (length Γ) σ (length Δ)
             ; _⊢v_⦂_ = _⊢v_⦂_
             ; _⊢c_⦂_ = _⊢c_⦂_
             ; lookup-pres = λ {σ}{Γ}{Δ}{x} σΓΔ Γ∋x → σΓΔ (Γ∋x→x<Γ {Γ = Γ} Γ∋x)
             ; extend-pres = λ {v}{σ}{Γ}{Δ}{A} → WS-extend {Γ = Γ}{Δ}
             ; ret-pres = λ {v} {Γ} {A} → WS-var v
             ; var-pres = λ {x} {Γ} Γ∋x → Γ∋x→x<Γ {x}{Γ} Γ∋x
             ; op-pres = op-pres
             ; var-inv = λ { {Γ}{x}{A} (WS-var x x<Γ) → x<Γ→Γ∋x {x}{Γ} x<Γ }
             ; op-inv = {!!}
             }
  open Preservation R WSPres

  mkenv : ℕ → List ⊤
  mkenv 0 = []
  mkenv (suc n) = tt ∷ mkenv n

  len-mkenv : ∀ n → Data.List.foldr (λ _ → suc) 0 (mkenv n) ≡ n
  len-mkenv zero = refl
  len-mkenv (suc n) = cong suc (len-mkenv n)

  {-# REWRITE len-mkenv #-}

  WS-rename : ∀ {Γ Δ ρ M} → WSRename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
  WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM = preserve {M}{ρ}{mkenv Γ}{mkenv Δ} WSM ΓρΔ
