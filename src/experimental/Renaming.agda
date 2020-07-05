{----------------------------------------------------------------------------
                             Renaming
 ---------------------------------------------------------------------------}
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; suc-injective)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import experimental.Structures
open import experimental.GSubst
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)
open Eq.≡-Reasoning
open import Var 

module experimental.Renaming where

Rename : Set
Rename = GSubst Var

ext-0 : ∀ (ρ : Rename) → (ext ρ) 0 ≡ 0
ext-0 ρ = refl

ext-suc : ∀ (ρ : Rename) x → (ext ρ) (suc x) ≡ suc ((ρ) x)
ext-suc ρ x = refl

module WithOpSig (Op : Set) (sig : Op → List ℕ)  where

  open import experimental.AbstractBindingTree Op sig
  open import experimental.Map Op sig renaming (_∘_≈_ to _○_≈_)

  rename : Rename → ABT → ABT
  rename = map
  ren-arg : Rename → {b : ℕ} →  Arg b → Arg b
  ren-arg = map-arg
  ren-args : Rename → {bs : List ℕ} →  Args bs → Args bs
  ren-args = map-args
  
  instance
    ABT-is-Shiftable : Shiftable ABT
    ABT-is-Shiftable = record { var→val = `_ ; ⇑ = rename (↑ 1)
                       ; var→val-suc-shift = λ {x} → refl }

    ABT-is-Renameable : Renameable ABT
    ABT-is-Renameable = record { ren = rename }

  ren-up-seq : ∀ (k : ℕ) (ρ : Rename) → ↑ k ⨟ ρ ≡ drop k ρ
  ren-up-seq k ρ rewrite up-seq k ρ | map-sub-id (drop k ρ) = refl

  ren-cons-seq : ∀ x (ρ₁ ρ₂ : Rename) → (x • ρ₁) ⨟ ρ₂ ≡ (ρ₂) x • (ρ₁ ⨟ ρ₂)
  ren-cons-seq x ρ₁ ρ₂ rewrite cons-seq x ρ₁ ρ₂ = refl

  ren-head : ∀ (ρ : Rename) x → rename (x • ρ) (` 0) ≡ ` x
  ren-head ρ x = refl

  ren-tail : ∀ (ρ : Rename) x → (↑ 1 ⨟ x • ρ) ≡ ρ
  ren-tail ρ x = refl

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

  ren-assoc : ∀ (σ τ θ : Rename) → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  ren-assoc σ τ θ = refl

  seq-rename : ∀ (ρ₁ ρ₂ : Rename) x → (ρ₁ ⨟ ρ₂) x ≡ ρ₂ (ρ₁ x)
  seq-rename ρ₁ ρ₂ x = refl

  compose-rename : ∀ (ρ₁ : Rename) (ρ₂ : Rename) (M : ABT)
     → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M
  compose-rename ρ₁ ρ₂ M =
    map-map-fusion-ext M (λ x → refl) ren-ext
        (λ{ρ₁}{ρ₂}{ρ₃}{f}{f⁻¹} → ren-perm{ρ₁}{ρ₂}{ρ₃}{f}{f⁻¹})
    where
    ren-ext : ∀{ρ₁ ρ₂ ρ₃ : Rename} → ρ₂ ○ ρ₁ ≈ ρ₃ → (ext ρ₂) ○ (ext ρ₁) ≈ ext ρ₃
    ren-ext ρ₂○ρ₁≈ρ₃ zero = refl
    ren-ext {ρ₁}{ρ₂}{ρ₃} ρ₂○ρ₁≈ρ₃ (suc x) rewrite var-injective (ρ₂○ρ₁≈ρ₃ x) =
       refl

    ren-perm : {ρ₁ ρ₂ ρ₃ : Rename} {f f⁻¹ : Var → Var} →
      (∀ x → f⁻¹ (f x) ≡ x) → (∀ y → f (f⁻¹ y) ≡ y) →
      ρ₂ ○ ρ₁ ≈ ρ₃ → (f ∘ ρ₂ ∘ f⁻¹) ○ f ∘ ρ₁ ∘ f⁻¹ ≈ (f ∘ ρ₃ ∘ f⁻¹)
    ren-perm {ρ₁}{ρ₂}{ρ₃}{f}{f⁻¹} inv inv' ρ₂○ρ₁≈ρ₃ x
        rewrite inv (ρ₁ (f⁻¹ x)) | var-injective (ρ₂○ρ₁≈ρ₃ (f⁻¹ x)) = refl

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

  FV-rename : ∀ (ρ : Rename) M y → FV (rename ρ M) y
     → Σ[ x ∈ Var ] ρ x ≡ y × FV M x
  FV-rename ρ (` x) y refl = ⟨ x , ⟨ refl , refl ⟩ ⟩
  FV-rename ρ (op ⦅ args ⦆) y fv = fvr-args ρ (sig op) args y fv
    where
    fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
        → FV-arg (ren-arg ρ arg) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-arg arg x
    fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
        → FV-args (ren-args ρ args) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-args args x
    fvr-arg ρ b (ast M) y fv = FV-rename ρ M y fv 
    fvr-arg ρ (suc b) (bind arg) y fv 
        with fvr-arg (ext ρ) b arg (suc y) fv
    ... | ⟨ 0 , eq ⟩  
        with eq
    ... | ()
    fvr-arg ρ (suc b) (bind arg) y fv 
        | ⟨ suc x , ⟨ eq , sx∈arg ⟩ ⟩ =
          ⟨ x , ⟨ suc-injective eq , sx∈arg ⟩ ⟩
          
    fvr-arg ρ b (perm f f⁻¹ inv inv' arg) y fy∈arg
        with fvr-arg (f ∘ ρ ∘ f⁻¹) b arg (f y) fy∈arg
    ... | ⟨ x' , ⟨ fρf⁻¹x=fy , x∈arg ⟩  ⟩ = 
        ⟨ f⁻¹ x' , ⟨ ρf⁻¹x=y , FVff⁻¹x ⟩ ⟩
        where
        ρf⁻¹x=y : ρ (f⁻¹ x') ≡ y
        ρf⁻¹x=y = begin
            ρ (f⁻¹ x') ≡⟨ sym (inv (ρ (f⁻¹ x'))) ⟩
            f⁻¹ (f (ρ (f⁻¹ x'))) ≡⟨ cong f⁻¹ fρf⁻¹x=fy ⟩
            f⁻¹ (f y) ≡⟨ inv y ⟩
            y   ∎
        FVff⁻¹x : FV-arg arg (f (f⁻¹ x'))
        FVff⁻¹x rewrite inv' x' = x∈arg

    fvr-args ρ [] nil y ()
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fv)
        with fvr-arg ρ b arg y fv
    ... | ⟨ x , ⟨ ρx , x∈arg ⟩ ⟩ = 
          ⟨ x , ⟨ ρx , (inj₁ x∈arg) ⟩ ⟩
    fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fv)
        with fvr-args ρ bs args y fv
    ... | ⟨ x , ⟨ ρx , x∈args ⟩ ⟩ = 
          ⟨ x , ⟨ ρx , (inj₂ x∈args) ⟩ ⟩

  rename-FV-⊥ : ∀ y (ρ : Rename) M → (∀ x → (ρ) x ≢ y) → FV (rename ρ M) y → ⊥
  rename-FV-⊥ y ρ M ρx≢y fvρM 
      with FV-rename ρ M y fvρM
  ... | ⟨ x , ⟨ ρxy , x∈M ⟩ ⟩ = ⊥-elim (ρx≢y x ρxy)
  
  FV-↑1-0 : ∀ M → FV (rename (↑ 1) M) 0 → ⊥
  FV-↑1-0 M = rename-FV-⊥ 0 (↑ 1) M (λ { x () })

{-
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

  open Composition Op sig using (compose-sub; drop-seq)

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

  rename-cong : ∀ ρ₁ ρ₂ M
     → (∀ x → (ρ₁) x ≡ (ρ₂) x)
     → rename ρ₁ M ≡ rename ρ₂ M
  rename-cong ρ₁ ρ₂ M f =
      map-cong M (λ x → cong `_ (f x))
              (λ ρ₁≈ρ₂ x → cong `_ (ext-cong (λ x → var-injective (ρ₁≈ρ₂ x)) x))

-}
