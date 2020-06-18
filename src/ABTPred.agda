open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s; _+_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Var

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module ABTPred {I : Set}
  (Op : Set) (sig : Op → List ℕ)
  (𝑉 : List I → Var → I → Set)
  (𝑃 : (op : Op) → Vec I (length (sig op)) → BTypes I (sig op) → I → Set) where

  open import AbstractBindingTree Op sig

  data _⊢_⦂_ : List I → ABT → I → Set
  data _∣_∣_⊢ₐ_⦂_ : (b : ℕ) → List I → BType I b → Arg b → I → Set 
  data _∣_∣_⊢₊_⦂_ : (bs : List ℕ) → List I → BTypes I bs → Args bs
                  → Vec I (length bs) → Set
  
  data _⊢_⦂_ where
    var-p : ∀{Γ x A}
       → Γ ∋ x ⦂ A  →  𝑉 Γ x A
       → Γ ⊢ ` x ⦂ A
    op-p : ∀{Γ op}{args : Args (sig op)}{A}{As : Vec I (length (sig op))}
             {Bs : BTypes I (sig op)}
       → (sig op) ∣ Γ ∣ Bs ⊢₊ args ⦂ As
       → 𝑃 op As Bs A
       → Γ ⊢ op ⦅ args ⦆ ⦂ A

  data _∣_∣_⊢ₐ_⦂_ where
    ast-p : ∀{Γ}{M}{A}  →  Γ ⊢ M ⦂ A  →  0 ∣ Γ ∣ tt ⊢ₐ ast M ⦂ A
       
    bind-p : ∀{b}{B Bs Γ arg A} → b ∣ (B ∷ Γ) ∣ Bs ⊢ₐ arg ⦂ A
       → (suc b) ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢ₐ bind arg ⦂ A

  data _∣_∣_⊢₊_⦂_ where
    nil-p : ∀{Γ} → [] ∣ Γ ∣ tt ⊢₊ nil ⦂ []̌ 
    cons-p : ∀{b bs}{arg args}{Γ}{A}{As}{Bs}{Bss}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
       → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args ⦂ (A ∷̌ As)
