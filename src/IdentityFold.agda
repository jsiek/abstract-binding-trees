open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; m≤m⊔n; n≤m⊔n)
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

  res→arg : ∀{b} → ArgRes b → Arg b
  res→arg {zero} M = ast M
  res→arg {suc b} r = bind (res→arg (r (` 0)))

  res→args : ∀{bs} → ArgsRes bs → Args bs
  res→args {[]} rnil = nil
  res→args {b ∷ bs} (rcons r rs) = cons (res→arg r) (res→args rs)
      
  id-is-foldable : Foldable ABT ABT Op sig (Substitution ABT)
  id-is-foldable = record { env = subst-is-env ; ret = λ M → M ;
            fold-free-var = `_ ; fold-op = λ o rs → o ⦅ res→args rs ⦆ }

  open Foldable id-is-foldable using (fold-op)

  open Folder id-is-foldable
      renaming (fold to id-fold; fold-arg to id-arg; fold-args to id-args)

  𝒫 : Op → List ⊤ → ⊤ → Set
  𝒫 _ _ _ = ⊤
  
  𝒜 : List ⊤ → ABT → ABT → ⊤ → Set
  𝒜 _ M M′ _ = (M ≡ ` 0) × (M′ ≡ ` 0)

  _⊢v_↝_⦂_ : List ⊤ → ABT → ABT → ⊤ → Set
  Δ ⊢v M ↝ M′ ⦂ tt = M ≡ M′
  
  _⊢c_↝_⦂_ : List ⊤ → ABT → ABT → ⊤ → Set
  Δ ⊢c M ↝ M′ ⦂ tt = M ≡ M′

  _⦂_⇒_ : Substitution ABT → List ⊤ → List ⊤ → Set
  σ ⦂ Γ ⇒ Δ = ∀ x → Γ ∋ x ⦂ tt → ⟦ σ ⟧ x ≡ ` x

  open PresArgResult 𝒫 𝒜 _⊢v_↝_⦂_ _⊢c_↝_⦂_ 

  extend-pres : ∀ {M′ : ABT}{σ : Substitution ABT}{Γ Δ : List ⊤}{A : ⊤}{M : ABT}
      → (A ∷ Δ) ⊢v M ↝ M′ ⦂ A
      → M ≡ (` 0) × M′ ≡ (` 0)
      → σ ⦂ Γ ⇒ Δ
      → exts σ M′ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
  extend-pres {.(` 0)} {σ} {M = .(` 0)} M↝M′ ⟨ refl , refl ⟩ σ⦂ zero ∋x = refl
  extend-pres {.(` 0)} {σ} {M = .(` 0)} M↝M′ ⟨ refl , refl ⟩ σ⦂ (suc x) ∋x
      rewrite extend-suc σ (` 0) x | σ⦂ x ∋x = refl

  op-pres : {op : Op} {Rs : ArgsRes (sig op)} {Δ : List ⊤} {A : ⊤}
            {As : List ⊤} {args : Args (sig op)}
     → (sig op) ∣ Δ ⊢rs args ↝ Rs ⦂ As
     → 𝒫 op As A
     → Δ ⊢c op ⦅ args ⦆ ↝ fold-op op Rs ⦂ A
  op-pres {op}{Rs}{Δ} ⊢Rs tt = cong (_⦅_⦆ op) (G ⊢Rs)
      where
      H : ∀{b}{arg : Arg b}{R : ArgRes b}{A : ⊤}{Δ}
         → b ∣ Δ ⊢r arg ↝ R ⦂ A
         → arg ≡ res→arg R
      H {zero} (ast-r refl) = refl
      H {suc b}{A = tt}{Δ = Δ} (bind-r {B = B} f) =
          cong bind (H {Δ = B ∷ Δ} (f refl ⟨ refl , refl ⟩))
      G : ∀{bs}{args : Args bs}{Rs : ArgsRes bs}{As : List ⊤}
         → bs ∣ Δ ⊢rs args ↝ Rs ⦂ As
         → args ≡ res→args Rs
      G nil-r = refl
      G (cons-r ⊢arg ⊢args) = cong₂ cons (H ⊢arg) (G ⊢args)


  id-is-preservable : Preservable ⊤ id-is-foldable
  id-is-preservable = record
                     { 𝒫 = 𝒫 
                     ; 𝒜 = 𝒜
                     ; _⦂_⇒_ = _⦂_⇒_
                     ; _⊢v_↝_⦂_ = _⊢v_↝_⦂_
                     ; _⊢c_↝_⦂_ = _⊢c_↝_⦂_
                     ; lookup-pres = λ {σ}{Γ}{Δ}{x} σ⦂ ∋x → sym (σ⦂ x ∋x)
                     ; extend-pres = λ {M′}{σ}{Γ}{Δ} → extend-pres {M′}{σ}{Γ}{Δ}
                     ; ret-pres = λ {v} {Δ} {A} {M} z → z
                     ; var-pres = λ {x} {Δ} {A} _ → refl
                     ; op-pres = op-pres
                     }

  open Preservation id-is-foldable id-is-preservable
  open ABTPred 𝒫

  mk-list : ℕ → List ⊤
  mk-list 0 = []
  mk-list (suc n) = tt ∷ mk-list n

  len-mk-list : ∀ n → length (mk-list n) ≡ n
  len-mk-list zero = refl
  len-mk-list (suc n) = cong suc (len-mk-list n)

  id-is-id : ∀ (M : ABT)
     → id-fold id M ≡ M
  id-is-id M =
    let n = suc (max-var M) in
    let p = preserve {M}{σ = ↑ 0}{mk-list n}{mk-list n} (G M (mk-list n)
               (s≤s (≤-reflexive (sym (len-mk-list (max-var M))))))
               (λ x _ → refl) in
    sym p
    where
    G : ∀ M Γ → suc (max-var M) ≤ length Γ → Γ ⊢ M ⦂ tt
    K : ∀ {b} {arg : Arg b} {Γ} → suc (max-var-arg arg) ≤ length Γ
       → b ∣ Γ ⊢a arg ⦂ tt
    J : ∀ {bs} {args : Args bs} {Γ} → suc (max-var-args args) ≤ length Γ
       → bs ∣ Γ ⊢as args ⦂ mk-list (length bs)

    suc∸1 : ∀ m x 
       → suc (m ∸ 1) ≤ x
       → m ≤ x
    suc∸1 zero x lt = z≤n
    suc∸1 (suc m) x lt = lt    

    H : ∀ x Γ → suc (max-var (` x)) ≤ length Γ → Γ ∋ x ⦂ tt
    H zero (tt ∷ Γ) lt = refl
    H (suc x) (tt ∷ Γ) (s≤s lt) = H x Γ lt

    K {zero} {ast M} {Γ} lt = ast-a (G M Γ lt)
    K {suc b} {bind arg} {Γ} lt =
        let s = suc∸1 (max-var-arg arg) (length Γ) lt in
        bind-a (K {b} {arg}{tt ∷ Γ} (s≤s s))

    J {[]} {nil} {Γ} lt = nil-a
    J {b ∷ bs} {cons arg args} {Γ} lt =
        let xx = s≤s (m≤m⊔n (max-var-arg arg) (max-var-args args)) in
        let yy = s≤s (n≤m⊔n (max-var-arg arg) (max-var-args args)) in
        cons-a (K (≤-trans xx lt)) (J (≤-trans yy lt))

    G (` x) Γ lt = var-p (H x Γ lt)
    G (op ⦅ args ⦆) Γ lt = op-op (J lt) tt
