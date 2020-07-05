open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import experimental.Structures
open import experimental.GenericSubstitution
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

record QuoteShift {ℓ}(V : Set ℓ) {{S : Shiftable V}} : Set ℓ
  where
  field {{V-is-Quotable}} : Quotable V
  field quote-var→val : ∀ x → “ (var→val{ℓ}{V} x) ” ≡ ` x
        quote-shift : ∀ (v : V) → “ ⇑ v ” ≡ rename (↑ 1) “ v ”

open QuoteShift {{...}} public

instance
  ABT-is-QuoteShift : QuoteShift ABT
  ABT-is-QuoteShift = record { quote-var→val = λ x → refl
                             ; quote-shift = λ v → refl }

map-rename-fusion : ∀{ℓ}{V₂ V₃ : Set ℓ}
  {{_ : Shiftable V₂}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₂}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
  {σ₁ : Rename}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → map σ₂ (rename σ₁ M) ≡ map σ₃ M
map-rename-fusion {ℓ}{V₂}{V₃}{σ₁ = σ₁}{σ₂}{σ₃} M σ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{lzero}{ℓ}{ℓ}{Var}{V₂}{V₃}{σ₁ = σ₁}{σ₂}{σ₃}
            M σ₂∘σ₁≈σ₃ map-ext {!!}
  where
  map-ext : ∀{σ₁ : Rename}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
          → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ zero =
      trans (quote-var→val{ℓ}{V₂} 0) (sym (quote-var→val{ℓ}{V₃} 0))
  map-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ (suc x)=
          trans (quote-shift{ℓ}{V₂} (σ₂ (σ₁ x)))
                (sym (trans (quote-shift{ℓ}{V₃} _)
                            (cong (rename (↑ 1)) (sym (σ₂∘σ₁≈σ₃ x)))))

rename-map-fusion : ∀{ℓ}{V₁ V₃ : Set ℓ}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₁}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₃}}
  {σ₁ : GSubst V₁}{ρ₂ : Rename}{σ₃ : GSubst V₃}
   → (M : ABT)
   → ρ₂ ∘ σ₁ ≈ σ₃
   → rename ρ₂ (map σ₁ M) ≡ map σ₃ M
rename-map-fusion {ℓ}{V₁}{V₃}{σ₁ = σ₁}{ρ₂}{σ₃} M ρ₂∘σ₁≈σ₃ =
  map-map-fusion-ext{ℓ}{lzero}{ℓ}{V₁}{Var}{V₃}{σ₁ = σ₁}{ρ₂}{σ₃}
            M ρ₂∘σ₁≈σ₃ map-ext {!!}
  where
  map-ext : ∀{σ₁ : GSubst V₁}{ρ₂ : Rename}{σ₃ : GSubst V₃}
          → ρ₂ ∘ σ₁ ≈ σ₃ → ext ρ₂ ∘ ext σ₁ ≈ ext σ₃
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ zero rewrite quote-var→val{ℓ}{V₁} 0
    | quote-var→val{ℓ}{V₃} 0 = refl
  map-ext {σ₁} {ρ₂} {σ₃} ρ₂∘σ₁≈σ₃ (suc x) rewrite quote-shift{ℓ}{V₁} (σ₁ x)
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
         ≡⟨ cong (rename (↑ 1)) (ρ₂∘σ₁≈σ₃ x) ⟩
      map (↑ 1) “ σ₃ x ”
      ∎

map-map-fusion : ∀{ℓ}{V₁ V₂ V₃ : Set ℓ}
  {{_ : Shiftable V₁}} {{_ : Shiftable V₂}} {{_ : Shiftable V₃}}
  {{_ : Renameable V₁}} {{_ : Renameable V₂}} {{_ : Renameable V₃}}
  {{_ : QuoteShift V₁}}{{_ : QuoteShift V₂}}{{_ : QuoteShift V₃}}
  {σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
   → (M : ABT)
   → σ₂ ∘ σ₁ ≈ σ₃
   → map σ₂ (map σ₁ M) ≡ map σ₃ M
map-map-fusion {ℓ}{V₁}{V₂}{V₃} M σ₂∘σ₁≈σ₃ =
  map-map-fusion-ext M σ₂∘σ₁≈σ₃ mm-fuse-ext  {!!}
  where
  G : ∀{σ₂ : GSubst V₂} → _∘_≈_ {lzero}{ℓ}{ℓ}{Var}
                         (σ₂ , (var→val 0)) (↑ 1) (⟰ σ₂)
  G {σ₂} x = refl
  H : ∀{σ₂ : GSubst V₂} → ↑ 1 ∘ σ₂ ≈ ⟰ σ₂
  H {σ₂} x rewrite quote-shift{ℓ}{V₂} (σ₂ x) = refl

  mm-fuse-ext : ∀{σ₁ : GSubst V₁}{σ₂ : GSubst V₂}{σ₃ : GSubst V₃}
      → σ₂ ∘ σ₁ ≈ σ₃ → ext σ₂ ∘ ext σ₁ ≈ ext σ₃
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ zero =
      begin
          map (σ₂ , (var→val 0)) “ (var→val{ℓ}{V₁} 0) ”
              ≡⟨ cong (map (σ₂ , (var→val{ℓ}{V₂} 0))) (quote-var→val{ℓ}{V₁} 0) ⟩
          map (σ₂ , (var→val 0)) (` 0)       ≡⟨⟩
          “ (σ₂ , (var→val 0)) 0 ”
                                        ≡⟨⟩
          “ (var→val{ℓ}{V₂} 0) ”        ≡⟨ (quote-var→val{ℓ}{V₂} 0) ⟩
          ` 0                        ≡⟨ sym (quote-var→val{ℓ}{V₃} 0) ⟩
          “ (var→val{ℓ}{V₃} 0) ”        ∎
  mm-fuse-ext {σ₁}{σ₂}{σ₃} σ₂∘σ₁≈σ₃ (suc x) = begin
      map (σ₂ , (var→val 0)) “ ⇑ (σ₁ x) ”
              ≡⟨ cong (map (σ₂ , (var→val 0))) (quote-shift{ℓ}{V₁} (σ₁ x)) ⟩
      map (σ₂ , (var→val 0)) (rename (↑ 1) “ σ₁ x ”)
                     ≡⟨ map-rename-fusion “ σ₁ x ” G ⟩
      map (⟰ σ₂) “ σ₁ x ”
                              ≡⟨ sym (rename-map-fusion “ σ₁ x ” H) ⟩
      rename (↑ 1) (map σ₂ “ σ₁ x ”) ≡⟨ cong (rename (↑ 1)) (σ₂∘σ₁≈σ₃ x) ⟩
      rename (↑ 1) “ σ₃ x ” ≡⟨ sym (quote-shift{ℓ}{V₃} (σ₃ x)) ⟩
      “ ⇑ (σ₃ x) ” ∎
