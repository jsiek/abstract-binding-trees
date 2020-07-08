open import Data.List using (List; []; _∷_; length; map; foldl)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred;
    m≤m⊔n; n≤m⊔n; m≤n⇒m<n∨m≡n; m≤n⇒m≤o⊔n)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open import ListAux
open import Var

{----- Predicate on ABT's (e.g. type system for expressions) -----}

module ABTPredicate {I : Set}
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

  {-
   Γ -- f --> Δ

   But is f surjective? If not, then for a variable x in Δ that
   is not in the image of f, we don't know that f⁻¹ x is in Γ.

   -}
  image-max : (Γ : List I) → (f : Var → Var)
      → Σ[ m ∈ ℕ ] (∀ x → x < length Γ → f x ≤ m)
  image-max [] f = ⟨ 0 , (λ _ ()) ⟩
  image-max (A ∷ Γ) f
      with image-max Γ f
  ... | ⟨ m , x<Γ→fx≤m ⟩ =
        ⟨ f (length Γ) ⊔ m , G ⟩
      where
      G : (x : ℕ) → suc x ≤ suc (length Γ)
                  → f x ≤ f (length Γ) ⊔ m
      G x (s≤s lt)
          with m≤n⇒m<n∨m≡n lt
      ... | inj₁ x<Γ = m≤n⇒m≤o⊔n (f (length Γ)) (x<Γ→fx≤m x x<Γ)
      ... | inj₂ refl = m≤m⊔n (f (length Γ)) m

  ren-ctx : (f⁻¹ : Var → Var) → (Γ : List I) → (n : ℕ)
      → (n≤ : n ≤ length Γ)
      → (f⁻¹< : ∀ k → k < length Γ → f⁻¹ k < length Γ)
      → List I
  ren-ctx f⁻¹ Γ zero n≤ f< = []
  ren-ctx f⁻¹ Γ (suc n) n≤ f< =
      nth Γ (f⁻¹ n) {f< n n≤}
          ∷ ren-ctx f⁻¹ Γ n (≤-trans (≤-step ≤-refl) n≤) f<

  data _∣_∣_⊢ₐ_⦂_ where
    ast-p : ∀{Γ}{M}{A}  →  Γ ⊢ M ⦂ A  →  0 ∣ Γ ∣ tt ⊢ₐ ast M ⦂ A
       
    bind-p : ∀{b}{B Bs Γ arg A} → b ∣ (B ∷ Γ) ∣ Bs ⊢ₐ arg ⦂ A
       → (suc b) ∣ Γ ∣ ⟨ B , Bs ⟩ ⊢ₐ bind arg ⦂ A

    perm-p : ∀{b : ℕ}{f f⁻¹ : Var → Var}{Bs Γ Δ arg A}
       → (inv : ∀ x → f⁻¹ (f x) ≡ x)
       → (inv' : ∀ y → f (f⁻¹ y) ≡ y)
       → (f-bnd : (k : ℕ) → k < length Γ → f⁻¹ k < length Γ)
       → Δ ≡ ren-ctx f⁻¹ Γ (length Γ) ≤-refl f-bnd
       → b ∣ Δ ∣ Bs ⊢ₐ arg ⦂ A
       → b ∣ Γ ∣ Bs ⊢ₐ perm f f⁻¹ inv inv' arg ⦂ A

  data _∣_∣_⊢₊_⦂_ where
    nil-p : ∀{Γ} → [] ∣ Γ ∣ tt ⊢₊ nil ⦂ []̌ 
    cons-p : ∀{b bs}{arg args}{Γ}{A}{As}{Bs}{Bss}
       → b ∣ Γ ∣ Bs ⊢ₐ arg ⦂ A  →  bs ∣ Γ ∣ Bss ⊢₊ args ⦂ As
       → (b ∷ bs) ∣ Γ ∣ ⟨ Bs , Bss ⟩ ⊢₊ cons arg args ⦂ (A ∷̌ As)
