open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import experimental.Structures
open import experimental.GenericSubstitution
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Var

module experimental.MapFusion (Op : Set) (sig : Op → List ℕ) where

open import experimental.AbstractBindingTree Op sig
open import experimental.Map Op sig
open import experimental.GSubst
open import experimental.Renaming 
open experimental.Renaming.WithOpSig Op sig

record QuoteShift {ℓ}(V : Set ℓ) {{S : Shiftable V}} {{_ : Renameable V}}
  : Set ℓ where
  field {{V-is-Quotable}} : Quotable V
  field quote-var→val : ∀ x → “ (var→val{ℓ}{V} x) ” ≡ ` x
        quote-shift : ∀ (v : V) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”
        quote-ren : ∀ (ρ : Var → Var) (v : V) → “ ren ρ v ” ≡ rename ρ “ v ”

open QuoteShift {{...}} public

instance
  Var-is-QuoteShift : QuoteShift Var
  Var-is-QuoteShift = record { quote-var→val = λ x → refl
                             ; quote-shift = λ v → refl
                             ; quote-ren = λ ρ v → refl }
  ABT-is-QuoteShift : QuoteShift ABT
  ABT-is-QuoteShift = record { quote-var→val = λ x → refl
                             ; quote-shift = λ v → refl
                             ; quote-ren = λ ρ v → refl }

map-rename-fusion : ∀{ℓ}{V₂ V₃ : Set ℓ}
  {{_ : Shiftable V₂}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₂}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
  {ρ₁ : Rename}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
   → (M : ABT)
   → σ₂ ○ ρ₁ ≈ σ₃
   → map σ₂ (rename ρ₁ M) ≡ map σ₃ M
map-rename-fusion {ℓ}{V₂}{V₃}{ρ₁ = ρ₁}{σ₂}{σ₃} M σ₂○ρ₁≈σ₃ =
  map-map-fusion-ext{lzero}{ℓ}{ℓ}{Var}{V₂}{V₃}{σ₁ = ρ₁}{σ₂}{σ₃}
            M σ₂○ρ₁≈σ₃ map-ext (λ {ρ₁}{σ₂} → map-perm {ρ₁}{σ₂})
  where
  map-ext : ∀{ρ₁ : Rename}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
          → σ₂ ○ ρ₁ ≈ σ₃ → ext σ₂ ○ ext ρ₁ ≈ ext σ₃
  map-ext {ρ₁} {σ₂} {σ₃} σ₂○ρ₁≈σ₃ zero =
      trans (quote-var→val{ℓ}{V₂} 0) (sym (quote-var→val{ℓ}{V₃} 0))
  map-ext {ρ₁} {σ₂} {σ₃} σ₂○ρ₁≈σ₃ (suc x)=
          trans (quote-shift{ℓ}{V₂} (σ₂ (ρ₁ x)))
                (sym (trans (quote-shift{ℓ}{V₃} _)
                            (cong (rename (↑ 1)) (sym (σ₂○ρ₁≈σ₃ x)))))
  map-perm : ∀{ρ₁ : Rename}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃} {f f⁻¹ : Var → Var}
      → (∀ x → f⁻¹ (f x) ≡ x)
      → (∀ y → f (f⁻¹ y) ≡ y)
      → σ₂ ○ ρ₁ ≈ σ₃
      → (ren f ∘ σ₂ ∘ f⁻¹) ○ (f ∘ ρ₁ ∘ f⁻¹) ≈ (ren f ∘ σ₃ ∘ f⁻¹)
  map-perm {ρ₁}{σ₂}{σ₃} {f}{f⁻¹} inv inv' σ₂○ρ₁≈σ₃ x
      rewrite inv (ρ₁ (f⁻¹ x)) | quote-ren f (σ₂ (ρ₁ (f⁻¹ x)))
      | quote-ren f (σ₃ (f⁻¹ x)) | σ₂○ρ₁≈σ₃ (f⁻¹ x) =
        refl

rename-map-fusion : ∀{ℓ}{V₁ V₃ : Set ℓ}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₁}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₃}}
  {σ₁ : GSubst V₁}{ρ₂ : Rename}{σ₃ : GSubst V₃}
   → (M : ABT)
   → ρ₂ ○ σ₁ ≈ σ₃
   → rename ρ₂ (map σ₁ M) ≡ map σ₃ M
rename-map-fusion {ℓ}{V₁}{V₃}{σ₁ = σ₁}{ρ₂}{σ₃} M ρ₂○σ₁≈σ₃ =
  map-map-fusion-ext{ℓ}{lzero}{ℓ}{V₁}{Var}{V₃}{σ₁ = σ₁}{ρ₂}{σ₃}
            M ρ₂○σ₁≈σ₃ map-ext map-perm
  where
  map-ext : ∀{σ₁ : GSubst V₁}{ρ₂ : Rename}{σ₃ : GSubst V₃}
          → ρ₂ ○ σ₁ ≈ σ₃ → ext ρ₂ ○ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂○σ₁≈σ₃ zero rewrite quote-var→val{ℓ}{V₁} 0
    | quote-var→val{ℓ}{V₃} 0 = refl
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂○σ₁≈σ₃ (suc x) rewrite quote-shift{ℓ}{V₁} (σ₁ x)
      | quote-shift{ℓ}{V₃} (σ₃ x) = begin
      rename (0 • ⟰ ρ₂) (map (↑ 1) “ σ₁ x ”)
          ≡⟨ compose-rename (↑ 1) (0 • ⟰ ρ₂) “ σ₁ x ” ⟩
      rename (↑ 1 ⨟ (0 • ⟰ ρ₂)) “ σ₁ x ”
         ≡⟨ cong (λ □ → rename □ “ σ₁ x ”) (ren-tail (⟰ ρ₂) 0) ⟩
      rename (⟰ ρ₂) “ σ₁ x ”
         ≡⟨ cong (λ □ → rename □ “ σ₁ x ”) (inc=⨟ᵣ↑ ρ₂) ⟩
      rename (ρ₂ ⨟ ↑ 1) “ σ₁ x ”
         ≡⟨ sym (compose-rename ρ₂ (↑ 1) “ σ₁ x ”) ⟩
      rename (↑ 1) (rename ρ₂ “ σ₁ x ”)
         ≡⟨ cong (rename (↑ 1)) (ρ₂○σ₁≈σ₃ x) ⟩
      map (↑ 1) “ σ₃ x ”
      ∎
  map-perm : ∀ {σ₁ : GSubst V₁} {ρ₂ : Rename} {σ₃ : GSubst V₃}
      {f f⁻¹ : Var → Var}
      → ((x : Var) → f⁻¹ (f x) ≡ x)
      → ((y : Var) → f (f⁻¹ y) ≡ y)
      → ρ₂ ○ σ₁ ≈ σ₃
      → (f ∘ ρ₂ ∘ f⁻¹) ○ (ren f ∘ σ₁ ∘ f⁻¹) ≈ (ren f ∘ σ₃ ∘ f⁻¹)
  map-perm {σ₁} {ρ₂} {σ₃} {f}{f⁻¹} inv inv' ρ₂○σ₁≈σ₃ x
      rewrite quote-ren f (σ₁ (f⁻¹ x)) | quote-ren f (σ₃ (f⁻¹ x))
      | compose-rename f (f ∘ ρ₂ ∘ f⁻¹) “ σ₁ (f⁻¹ x) ” = begin
      rename (f ∘ ρ₂ ∘ (f⁻¹ ∘ f)) “ σ₁ (f⁻¹ x) ”
        ≡⟨ cong (λ □ → map (f ∘ ρ₂ ∘ □) “ σ₁ (f⁻¹ x) ”) (extensionality inv)  ⟩
      rename (f ∘ ρ₂) “ σ₁ (f⁻¹ x) ”
        ≡⟨ sym (compose-rename ρ₂ f “ σ₁ (f⁻¹ x) ”) ⟩
      rename f (rename ρ₂ “ σ₁ (f⁻¹ x) ”)
        ≡⟨ cong (rename f) (ρ₂○σ₁≈σ₃ (f⁻¹ x)) ⟩
      rename f “ σ₃ (f⁻¹ x) ”
      ∎

map-map-fusion : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₂}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₁}} {{_ : Renameable V₂}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
  {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
   → (M : ABT)
   → σ₂ ○ σ₁ ≈ σ₃
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion {ℓ}{V₁}{V₂}{V₃} M σ₂○σ₁≈σ₃ =
  map-map-fusion-ext M σ₂○σ₁≈σ₃ mm-fuse-ext perm-env
  where
  G : ∀{σ₂ : GSubst V₂} → _○_≈_ {lzero}{ℓ}{ℓ}{Var}
                         (σ₂ , (var→val 0)) (↑ 1) (⟰ σ₂)
  G {σ₂} x = refl
  H : ∀{σ₂ : GSubst V₂} → ↑ 1 ○ σ₂ ≈ ⟰ σ₂
  H {σ₂} x rewrite quote-shift{ℓ}{V₂} (σ₂ x) = refl

  mm-fuse-ext : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
      → σ₂ ○ σ₁ ≈ σ₃ → ext σ₂ ○ ext σ₁ ≈ ext σ₃
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂○σ₁≈σ₃ zero =
      begin
          map (σ₂ , (var→val 0)) “ (var→val{ℓ}{V₁} 0) ”
              ≡⟨ cong (map (σ₂ , (var→val{ℓ}{V₂} 0))) (quote-var→val{ℓ}{V₁} 0) ⟩
          map (σ₂ , (var→val 0)) (` 0)       ≡⟨⟩
          “ (σ₂ , (var→val 0)) 0 ”
                                        ≡⟨⟩
          “ (var→val{ℓ}{V₂} 0) ”        ≡⟨ (quote-var→val{ℓ}{V₂} 0) ⟩
          ` 0                        ≡⟨ sym (quote-var→val{ℓ}{V₃} 0) ⟩
          “ (var→val{ℓ}{V₃} 0) ”        ∎
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂○σ₁≈σ₃ (suc x) = begin
      map (σ₂ , (var→val 0)) “ ⇑ (σ₁ x) ”
              ≡⟨ cong (map (σ₂ , (var→val 0))) (quote-shift{ℓ}{V₁} (σ₁ x)) ⟩
      map (σ₂ , (var→val 0)) (rename (↑ 1) “ σ₁ x ”)
                     ≡⟨ map-rename-fusion “ σ₁ x ” G ⟩
      map (⟰ σ₂) “ σ₁ x ”
                              ≡⟨ sym (rename-map-fusion “ σ₁ x ” H) ⟩
      rename (↑ 1) (map σ₂ “ σ₁ x ”) ≡⟨ cong (rename (↑ 1)) (σ₂○σ₁≈σ₃ x) ⟩
      rename (↑ 1) “ σ₃ x ” ≡⟨ sym (quote-shift{ℓ}{V₃} (σ₃ x)) ⟩
      “ ⇑ (σ₃ x) ” ∎

  perm-env : {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}{f f⁻¹ : Var → Var}
     → ((x : Var) → f⁻¹ (f x) ≡ x)
     → ((y : Var) → f (f⁻¹ y) ≡ y)
     → σ₂ ○ σ₁ ≈ σ₃
     → (ren f ∘ σ₂ ∘ f⁻¹) ○ ren f ∘ σ₁ ∘ f⁻¹ ≈ (ren f ∘ σ₃ ∘ f⁻¹)
  perm-env {σ₁}{σ₂}{σ₃}{f}{f⁻¹} inv inv' σ₂○σ≈σ₃ x = begin
      map (ren f ∘ σ₂ ∘ f⁻¹) “ ren f (σ₁ (f⁻¹ x)) ”
                   ≡⟨ cong (map (ren f ∘ σ₂ ∘ f⁻¹)) (quote-ren f (σ₁ (f⁻¹ x))) ⟩
      map (ren f ∘ σ₂ ∘ f⁻¹) (rename f “ σ₁ (f⁻¹ x) ”)
            ≡⟨ map-rename-fusion “ σ₁ (f⁻¹ x) ” (λ _ → refl) ⟩ 
      map (ren f ∘ σ₂ ∘ (f⁻¹ ∘ f)) “ σ₁ (f⁻¹ x) ”
       ≡⟨ cong (λ □ → map(ren f ∘ σ₂ ∘ □) “ σ₁ (f⁻¹ x) ”)(extensionality inv) ⟩ 
      map (ren f ∘ σ₂) “ σ₁ (f⁻¹ x) ”
               ≡⟨ sym (rename-map-fusion “ σ₁ (f⁻¹ x) ”
                                         (λ x₁ → sym (quote-ren f (σ₂ x₁))) ) ⟩ 
      rename f (map σ₂ “ σ₁ (f⁻¹ x) ”)
            ≡⟨ cong (rename f) (σ₂○σ≈σ₃ (f⁻¹ x)) ⟩
      rename f “ σ₃ (f⁻¹ x) ”
            ≡⟨ sym (quote-ren f (σ₃ (f⁻¹ x))) ⟩
      “ ren f (σ₃ (f⁻¹ x)) ”      ∎
