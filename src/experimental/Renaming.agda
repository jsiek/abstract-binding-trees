open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; suc-injective)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Var 

module experimental.Renaming where

open import experimental.Environment using (Shiftable)
open import experimental.GSubst
open Shiftable {{...}}
open import experimental.GenericSubstitution 
    
{----------------------------------------------------------------------------
                             Renaming
 ---------------------------------------------------------------------------}

Rename : Set
Rename = GSubst Var

ext-0 : ∀ (ρ : Rename) → (ext ρ) 0 ≡ 0
ext-0 ρ = refl

ext-suc : ∀ (ρ : Rename) x → (ext ρ) (suc x) ≡ suc ((ρ) x)
ext-suc ρ x = refl

module WithOpSig (Op : Set) (sig : Op → List ℕ)  where

  open import AbstractBindingTree Op sig
  open import experimental.Environment

  open import experimental.Map Op sig

  instance
    _ : Quotable Var
    _ = Var-is-Quotable
    
  rename : Rename → ABT → ABT
  rename = map

  ren-arg : Rename → {b : ℕ} → Arg b → Arg b
  ren-arg = map-arg

  ren-args : Rename → {bs : List ℕ} → Args bs → Args bs
  ren-args = map-args

  open Composition Op sig using (ComposableProps)
  
  instance
    Ren-Composable : Composable Var Var Var
    Ren-Composable = record { ⌈_⌉ = λ f x → f x ; val₂₃ = λ x → x
                     ; ⌈⌉-var→val = λ σ x → refl }

    Ren-ComposableProps : ComposableProps Var Var Var
    Ren-ComposableProps = record { var→val₂₃ = λ x → refl
        ; quote-val₂₃ = λ v₂ → refl ; val₂₃-shift = λ v₂ → refl
        ; quote-var→val₁ = λ x → refl ; quote-map = λ σ₂ v₁ → refl }

  instance
    ABT-is-Shiftable : Shiftable ABT
    ABT-is-Shiftable = record { var→val = `_ ; ⇑ = rename (↑ 1)
                       ; var→val-suc-shift = λ {x} → refl }
    ABT-is-Quotable : Quotable ABT
    ABT-is-Quotable = record { “_” = λ x → x }

  ren-up-seq : ∀ k (ρ : Rename) → ↑ k ⨟ ρ ≡ drop k ρ
  ren-up-seq k ρ rewrite up-seq k ρ | map-sub-id (drop k ρ) = refl

  ren-cons-seq : ∀ x (ρ₁ ρ₂ : Rename) → (x • ρ₁) ⨟ ρ₂ ≡ (ρ₂) x • (ρ₁ ⨟ ρ₂)
  ren-cons-seq x ρ₁ ρ₂ rewrite cons-seq x ρ₁ ρ₂ = refl

  ren-head : ∀ (ρ : Rename) x → rename (x • ρ) (` 0) ≡ ` x
  ren-head ρ x = refl

  ren-tail : ∀ (ρ : Rename) x → (↑ 1 ⨟ x • ρ) ≡ ρ
  ren-tail ρ x rewrite ren-up-seq 1 (x • ρ) | drop-0 ρ = refl

  inc=⨟ᵣ↑ : ∀ (ρ : Rename) → ⟰ ρ ≡ ρ ⨟ ↑ 1
  inc=⨟ᵣ↑ ρ = refl

  ext-cons-shift : ∀ (ρ : Rename) → ext ρ ≡ (0 • (ρ ⨟ ↑ 1))
  ext-cons-shift ρ = refl

  ren-η : ∀ (ρ : Rename) x → ((ρ) 0 • (↑ 1 ⨟ ρ)) x ≡ (ρ) x
  ren-η ρ 0 = refl
  ren-η ρ (suc x) = refl

  ren-idL : ∀ (ρ : Rename) → id ⨟ ρ ≡ ρ
  ren-idL ρ = refl

  ren-dist :  ∀ x (ρ : Rename) τ → ((x • ρ) ⨟ τ) ≡ (((τ) x) • (ρ ⨟ τ))
  ren-dist x ρ τ rewrite ren-cons-seq x ρ τ = refl

  open Composition Op sig using (compose-sub; drop-seq)

  seq-rename : ∀ (ρ₁ ρ₂ : Rename) x → (ρ₁ ⨟ ρ₂) x ≡ ρ₂ (ρ₁ x)
  seq-rename ρ₁ ρ₂ x = var-injective (compose-sub ρ₁ ρ₂ x)

  ren-assoc : ∀ (σ τ θ : Rename) → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  ren-assoc σ τ θ = refl

  {------ Composing renamings -------}

  ren-map-fusion-ext : ∀{ρ₁ : Rename}{ρ₂ : Rename}{ρ₃ : Rename}
                → ρ₂ ∘ ρ₁ ≈ ρ₃ → ext ρ₂ ∘ ext ρ₁ ≈ ext ρ₃
  ren-map-fusion-ext {ρ₁} {ρ₂} {ρ₃} ρ₂∘ρ₁≈ρ₃ zero = refl
  ren-map-fusion-ext {ρ₁} {ρ₂} {ρ₃} ρ₂∘ρ₁≈ρ₃ (suc x) = 
     cong `_ (cong suc (var-injective (ρ₂∘ρ₁≈ρ₃ x)))

{-
{-
  With the addition of the permutation Arg,
  it becomes difficult to prove that renamings compose:

     rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ ρ₂) M

  For that, one needs to prove

     ρ₂ ∘ ρ₁ ≈ ρ₃ → π xs ρ₂ ∘ π xs ρ₁ ≈ π xs ρ₃

  The premise means:

     ∀ x → (` (ρ₂) ((ρ₁) x)) ≡ (` (ρ₃) x)

  and we need to show 
     
     (` (ρ₂) (f ((ρ₁) (f x)))) ≡ (` (ρ₃) (f x))

  but that doesn't follow in general, AFAIK.

-}

  ren-map-fusion-perm : ∀{ρ₁ : Rename}{ρ₂ : Rename}{ρ₃ : Rename}{xs : List Var}
                → ρ₂ ∘ ρ₁ ≈ ρ₃ → π xs ρ₂ ∘ π xs ρ₁ ≈ π xs ρ₃
  ren-map-fusion-perm {ρ₁}{ρ₂}{ρ₃}{xs} ρ₂∘ρ₁≈ρ₃ x
      rewrite lookup-permute ρ₁ xs x | lookup-permute ρ₃ xs x
      | lookup-permute ρ₂ xs ((ρ₁)ˢ (l→f xs x)) =
      {!!}
-}

  compose-rename : ∀ (ρ₁ : Rename) (ρ₂ : Rename) M
     → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₁ ⨟ ρ₂) M
  compose-rename ρ₁ ρ₂ M =
      map-map-fusion-ext M (λ x → sym (cong `_ (seq-rename ρ₁ ρ₂ x)))
          ren-map-fusion-ext {-(λ {σ₁}{σ₂}{σ₃}{xs} σ₂∘σ₁≈σ₃ x →
                               ren-map-fusion-perm{σ₁}{σ₂}{σ₃}{xs} σ₂∘σ₁≈σ₃ x)-}

  commute-↑1 : ∀ ρ M
     → rename (ext ρ) (rename (↑ 1) M) ≡ rename (↑ 1) (rename ρ M)
  commute-↑1 ρ M = begin
      rename (ext ρ) (rename (↑ 1) M)  ≡⟨ compose-rename (↑ 1) (ext ρ) M ⟩
      rename (↑ 1 ⨟ (ext ρ)) M
                        ≡⟨ cong (λ □ → rename (↑ 1 ⨟ □) M) (ext-cons-shift _) ⟩
      rename (↑ 1 ⨟ (0 • (ρ ⨟ ↑ 1))) M
                                  ≡⟨ cong (λ □ → rename □ M) (ren-tail _ zero) ⟩
      rename (ρ ⨟ ↑ 1) M           ≡⟨ sym (compose-rename ρ (↑ 1) M) ⟩
      rename (↑ 1) (rename ρ M)    ∎

  rename-cong : ∀ ρ₁ ρ₂ M
     → (∀ x → (ρ₁) x ≡ (ρ₂) x)
     → rename ρ₁ M ≡ rename ρ₂ M
  rename-cong ρ₁ ρ₂ M f =
      map-cong M (λ x → cong `_ (f x))
              (λ ρ₁≈ρ₂ x → cong `_ (ext-cong (λ x → var-injective (ρ₁≈ρ₂ x)) x))

  FV-rename : ∀ (ρ : Rename) M x → FV (map ρ M) x
     → Σ[ y ∈ Var ] (ρ) y ≡ x × FV M y
  FV-rename ρ (` y) x refl = ⟨ y , ⟨ refl , refl ⟩ ⟩
  FV-rename ρ (op ⦅ args ⦆) x fv = fvr-args ρ (sig op) args x fv
    where
    fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) x
        → FV-arg (map-arg ρ arg) x → Σ[ y ∈ Var ] (ρ) y ≡ x × FV-arg arg y
    fvr-args : ∀ (ρ : Rename) bs (args : Args bs) x
        → FV-args (map-args ρ args) x → Σ[ y ∈ Var ] (ρ) y ≡ x × FV-args args y
    fvr-arg ρ b (ast M) x fv = FV-rename ρ M x fv 
    fvr-arg ρ (suc b) (bind arg) x fv 
        with fvr-arg (ext ρ) b arg (suc x) fv
    ... | ⟨ 0 , eq ⟩  
        with eq
    ... | ()
    fvr-arg ρ (suc b) (bind arg) x fv 
        | ⟨ suc y , ⟨ eq , sy∈arg ⟩ ⟩ =
          ⟨ y , ⟨ suc-injective eq , sy∈arg ⟩ ⟩
{-
    fvr-arg ρ b (perm xs arg) x fv = {!!}
-}
    fvr-args ρ [] nil x ()
    fvr-args ρ (b ∷ bs) (cons arg args) x (inj₁ fv)
        with fvr-arg ρ b arg x fv
    ... | ⟨ y , ⟨ ρy , y∈arg ⟩ ⟩ = 
          ⟨ y , ⟨ ρy , (inj₁ y∈arg) ⟩ ⟩
    fvr-args ρ (b ∷ bs) (cons arg args) x (inj₂ fv)
        with fvr-args ρ bs args x fv
    ... | ⟨ y , ⟨ ρy , y∈args ⟩ ⟩ = 
          ⟨ y , ⟨ ρy , (inj₂ y∈args) ⟩ ⟩

  rename-FV-⊥ : ∀ x (ρ : Rename) M → (∀ y → (ρ) y ≢ x) → FV (rename ρ M) x → ⊥
  rename-FV-⊥ x ρ M ρy≢x fvρM 
      with FV-rename ρ M x fvρM
  ... | ⟨ y , ⟨ ρyx , y∈M ⟩ ⟩ = ⊥-elim (ρy≢x y ρyx)
  
  FV-↑1-0 : ∀ M → FV (rename (↑ 1) M) 0 → ⊥
  FV-↑1-0 M = rename-FV-⊥ 0 (↑ 1) M (λ { y () })
