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
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)

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
      → v < length (A ∷ Δ) →
      (WSRename (length Γ) σ (length Δ)) →
      (WSRename (length (A ∷ Γ)) (extend σ v) (length (A ∷ Δ)))
  WS-extend v<Δ σΓΔ {zero} (s≤s x<Γ) = v<Δ
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

  op-pres : ∀ {op : Op} {Rs : ArgsRes (sig op)} {Δ : List ⊤} {A : ⊤} {As : List ⊤}
     → sig op ∣ Δ ⊢rs Rs ⦂ As
     → WS (length Δ) (fold-op op Rs)
  op-pres {op}{Rs}{Δ}{A}{As} ⊢Rs = WS-op (G ⊢Rs)
      where
      H : ∀{b}{R : ArgRes b}{A}{Δ} → b ∣ Δ ⊢r R ⦂ A → WS-arg (length Δ) (r-arg R)
      H {.0} {M} {A} {Δ} (ast-r WSM) = WS-ast WSM
      H {.(suc _)} {R} {A} {Δ} (bind-r f) =
          let ⊢R = f {0} (s≤s z≤n) in
          WS-bind (H ⊢R)
      G : ∀{bs}{Rs : ArgsRes bs}{As} → bs ∣ Δ ⊢rs Rs ⦂ As → WS-args (length Δ) (r-args Rs)
      G {.[]} {.rnil} {.[]} nil-r = WS-nil
      G {.(_ ∷ _)} {.(rcons _ _)} {.(_ ∷ _)} (cons-r ⊢R ⊢Rs) = WS-cons (H ⊢R) (G ⊢Rs)

  mkenv : ℕ → List ⊤
  mkenv 0 = []
  mkenv (suc n) = tt ∷ mkenv n

  len-mkenv : ∀ n → Data.List.foldr (λ _ → suc) 0 (mkenv n) ≡ n
  len-mkenv zero = refl
  len-mkenv (suc n) = cong suc (len-mkenv n)

  {-# REWRITE len-mkenv #-}

  op-inv : ∀ {Γ : List ⊤} {op : Op} {args : Args (sig op)} {A : ⊤}
     → WS (length Γ) (op ⦅ args ⦆)
     → ∃[ As ] ((sig op) ∣ Γ ⊢as args ⦂ As)
  op-inv {Γ} {op} {As} {A} (WS-op WS-As) = ⟨ mkenv (length (sig op)) , G WS-As ⟩
      where
      H : ∀{b}{Γ}{A : Arg b}
         → WS-arg (length Γ) A
         → b ∣ Γ ⊢a A ⦂ tt
      H {.0} {Γ} {ast M} (WS-ast WSM) = ast-a WSM
      H {.(suc _)} {Γ} {.(bind _)} (WS-bind WS-A) = bind-a (H WS-A)
      
      G : ∀{bs}{Γ}{As : Args bs}
         → WS-args (length Γ) As
         → bs ∣ Γ ⊢as As ⦂ mkenv (length bs)
      G {.[]} {Γ} {.nil} WS-nil = nil-a
      G {.(_ ∷ _)} {Γ} {.(cons _ _)} (WS-cons WS-A WS-As) = cons-a (H WS-A) (G WS-As)


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
             ; op-inv = op-inv
             }
  open Preservation R WSPres

  WS-rename : ∀ {Γ Δ ρ M} → WSRename Γ ρ Δ → WS Γ M → WS Δ (rename ρ M)
  WS-rename {Γ}{Δ}{ρ}{M} ΓρΔ WSM = preserve {M}{ρ}{mkenv Γ}{mkenv Δ} WSM ΓρΔ
