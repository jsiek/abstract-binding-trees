{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Syntax
open import Generic

open import Data.Nat using (ℕ; zero; suc; _+_; pred; _≤_; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-step; suc-injective)
open import Data.List using (List; []; _∷_; length)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

module WellScoped (Op : Set) (sig : Op → List ℕ) where

  open OpSig Op sig hiding (rename)

{-
  data WS : ℕ → ABT → Set 
  data WS-arg : ℕ → {b : ℕ} → Arg b → Set
  data WS-args : ℕ → {bs : List ℕ} → Args bs → Set 

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
-}
  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  len-mk-list : ∀ n → Data.List.foldr (λ _ → suc) 0 (mk-list n) ≡ n
  len-mk-list zero = refl
  len-mk-list (suc n) = cong suc (len-mk-list n)

  {-# REWRITE len-mk-list #-}

  WS : ℕ → ABT → Set
  WS-arg : ℕ → {b : ℕ} → Arg b → Set
  WS-args : ℕ → {bs : List ℕ} → Args bs → Set
  
  𝒫 : Op → List ⊤ → ⊤ → Set
  𝒫 op Γ A = ⊤
  _⊢v_⦂_ : List ⊤ → Var → ⊤ → Set
  Γ ⊢v x ⦂ _ = x < length Γ
  _⊢c_⦂_ : List ⊤ → ABT → ⊤ → Set
  Γ ⊢c M ⦂ _ = WS (length Γ) M

  open ArgResult Var ABT
  open PresArgResult Op sig 𝒫 _⊢v_⦂_ _⊢c_⦂_
  open Rename Op sig
  open Foldable R

  len : ∀{bs} → Args bs → ℕ
  len nil = 0
  len (cons _ args) = suc (len args)

  WS n M = (mk-list n) ⊢ M ⦂ tt
  WS-arg n {b} arg = b ∣ (mk-list n) ⊢a arg ⦂ tt
  WS-args n {bs} args = bs ∣ (mk-list n) ⊢as args ⦂ (mk-list (len args))
  
  open GenericSub Var (λ x → x) suc using (⧼_⧽; inc)

  WSRename : ℕ → Rename → ℕ → Set
  WSRename Γ ρ Δ = ∀ {x} → x < Γ → (⧼ ρ ⧽  x) < Δ


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
      → v < length (A ∷ Δ) →
      (WSRename (length Γ) σ (length Δ)) →
      (WSRename (length (A ∷ Γ)) (extend σ v) (length (A ∷ Δ)))
  WS-extend v<Δ σΓΔ {zero} (s≤s x<Γ) = v<Δ
  WS-extend {v}{σ} v<Δ σΓΔ {suc x} (s≤s x<Γ) rewrite inc-suc σ x = s≤s (σΓΔ x<Γ)

  list-eq : ∀(l₁ l₂ : List ⊤) → length l₁ ≡ length l₂ → l₁ ≡ l₂
  list-eq [] [] len = refl
  list-eq (x ∷ l₁) (y ∷ l₂) len = cong₂ _∷_ refl (list-eq l₁ l₂ (suc-injective len))

  op-pres : ∀ {op : Op} {Rs : ArgsRes (sig op)} {Δ : List ⊤} {A : ⊤} {As : List ⊤}
     → sig op ∣ Δ ⊢rs Rs ⦂ As
     → 𝒫 op As A
     → WS (length Δ) (fold-op op Rs)
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs 𝒫op =    
         op-op (subst (λ □ → sig op ∣ □ ⊢as r-args Rs ⦂ As) (sym eq1) {!!}) tt

     where
     eq1 : (mk-list (length Δ)) ≡ Δ
     eq1 = list-eq (mk-list (length Δ)) Δ (len-mk-list (length Δ))
     
{-
      WS-op (G ⊢Rs)
      where
      H : ∀{b}{R : ArgRes b}{A}{Δ} → b ∣ Δ ⊢r R ⦂ A → WS-arg (length Δ) (r-arg R)
      H {.0} {M} {A} {Δ} (ast-r WSM) = WS-ast WSM
      H {.(suc _)} {R} {A} {Δ} (bind-r f) =
          let ⊢R = f {0} (s≤s z≤n) in
          WS-bind (H ⊢R)
      G : ∀{bs}{Rs : ArgsRes bs}{As} → bs ∣ Δ ⊢rs Rs ⦂ As → WS-args (length Δ) (r-args Rs)
      G {.[]} {.rnil} {.[]} nil-r = WS-nil
      G {.(_ ∷ _)} {.(rcons _ _)} {.(_ ∷ _)} (cons-r ⊢R ⊢Rs) = WS-cons (H ⊢R) (G ⊢Rs)
-}

  WSPres : Preservable ⊤ R
  WSPres = record
             { 𝒫 = 𝒫
             ; _⦂_⇒_ = λ σ Γ Δ → WSRename (length Γ) σ (length Δ)
             ; _⊢v_⦂_ = _⊢v_⦂_
             ; _⊢c_⦂_ = _⊢c_⦂_
             ; lookup-pres = λ {σ}{Γ}{Δ}{x} σΓΔ Γ∋x → σΓΔ (Γ∋x→x<Γ {Γ = Γ} Γ∋x)
             ; extend-pres = λ {v}{σ}{Γ}{Δ}{A} → WS-extend {Γ = Γ}{Δ} 
             ; ret-pres = λ {v} {Γ} {A} → {!!} {- WS-var v -}
             ; var-pres = λ {x} {Γ} Γ∋x → Γ∋x→x<Γ {x}{Γ} Γ∋x
             ; op-pres = op-pres
             }
  open Preservation R WSPres

  {- This proof is terrible! Longer than the original one! -Jeremy -}

  WS-rename : ∀ {Γ Δ ρ M} → WSRename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
  WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM = {!!}
{-
    let p = preserve {M}{ρ}{mk-list Γ}{mk-list Δ} {!!} ΓρΔ
    in p
-}
