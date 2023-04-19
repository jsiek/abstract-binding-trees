{-# OPTIONS --rewriting #-}
module rewriting.examples.CastSafeLogic2 where

open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2
open import rewriting.examples.CastDeterministic
open import rewriting.examples.CastLogRelLogic2

compatible-blame : ∀{Γ}{A}
     -------------
   → Γ ⊨ blame ⦂ A
compatible-blame {Γ}{A} γ = ℰ-blame

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ rewrite sub-var γ x =
     let ⊢𝒱γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ x)
         ⊢𝒱γx = lookup-𝓖 Γ γ ∋x in
     𝒱⇒ℰ ⊢𝒱γx

compatible-nat : ∀{Γ}{n : ℕ}
    --------------------------
   → Γ ⊨ ($ (Num n)) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-bool : ∀{Γ}{b : 𝔹}
    ---------------------------
   → Γ ⊨ ($ (Bool b)) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ = 𝒱⇒ℰ (substᵒ (≡ᵒ-sym 𝒱-base) (constᵒI refl))

compatible-lambda : ∀{Γ}{A}{B}{N}
   → (A ∷ Γ) ⊨ N ⦂ B
     -------------------
   → Γ ⊨ (ƛ N) ⦂ (A ⇒ B)
compatible-lambda {Γ}{A}{B}{N} ⊨N γ = ⊢ℰγλN
 where
 ⊢ℰγλN : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N))
 ⊢ℰγλN =
   𝒱⇒ℰ (𝒱-fun-intro (Λᵒ[ W ] →ᵒI ▷𝓔N[W]))
   where
   ▷𝓔N[W] : ∀{W} → ▷ᵒ 𝒱⟦ A ⟧ W ∷ 𝓖⟦ Γ ⟧ γ  ⊢ᵒ  ▷ᵒ ℰ⟦ B ⟧ ((⟪ ext γ ⟫ N) [ W ])
   ▷𝓔N[W] {W} =
     let ⊢𝒱W→ℰN[W] : 𝓖⟦ Γ ⟧ γ ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W) →ᵒ ▷ᵒ ℰ⟦ B ⟧ (⟪ W • γ ⟫ N))
         ⊢𝒱W→ℰN[W] = ▷→ (monoᵒ (→ᵒI (⊨N (W • γ)))) in
     appᵒ (Sᵒ ⊢𝒱W→ℰN[W]) Zᵒ

compatible-app : ∀{Γ}{A}{B}{L}{M}
   → Γ ⊨ L ⦂ (A ⇒ B)
   → Γ ⊨ M ⦂ A
     -------------------
   → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢ℰLM
 where
 ⊢ℰL : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)
 ⊢ℰL = ⊨L γ

 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ

 ⊢ℰLM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢ℰLM = ℰ-bind {F = □· (⟪ γ ⟫ M)} ⊢ℰL (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVM))
  where
  𝓟₁ = λ V → 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVM : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢ℰVM {V} = ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn →
       let v = 𝒱⇒Value (A ⇒ B) V 𝒱Vsn in
       let 𝓟₁⊢ℰM : 𝓟₁ V ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)
           𝓟₁⊢ℰM = Sᵒ (Sᵒ ⊢ℰM) in
       ℰ-bind {F = v ·□} 𝓟₁⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVW))
   where
   𝓟₂ = λ V W → 𝒱⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝒱⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢ℰVW : ∀{V W} → 𝓟₂ V W ⊢ᵒ ℰ⟦ B ⟧ (V · W)
   ⊢ℰVW {V}{W} =
     let ⊢𝒱V : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
         ⊢𝒱V = Sᵒ (Sᵒ Zᵒ) in
     let ⊢𝒱W : 𝓟₂ V W ⊢ᵒ 𝒱⟦ A ⟧ W
         ⊢𝒱W = Zᵒ in
     ⊢ᵒ-sucP ⊢𝒱W λ 𝒱Wsn →
     let w = 𝒱⇒Value A W 𝒱Wsn in
     𝒱-fun-elim ⊢𝒱V λ {N′ refl 𝒱W→ℰNW →
     let pres : 𝓟₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
         pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ {r →
                let ⊢▷ℰN′W = appᵒ 𝒱W→ℰNW (monoᵒ ⊢𝒱W) in
                let eq = deterministic r (β w) in
                ⊢ᵒ-weaken (subst (λ N → 𝓟₂ (ƛ N′) W ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ N) 
                                 (sym eq) ⊢▷ℰN′W)}) in
     substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (constᵒI (_ , (β w)) ,ᵒ pres)))
     }

compatible-inject : ∀{Γ}{G}{M}
  → Γ ⊨ M ⦂ gnd⇒ty G
    --------------------
  → Γ ⊨ M ⟨ G !⟩ ⦂ ★
compatible-inject {Γ}{G}{M} ⊨M γ = ℰMg!
 where
 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ gnd⇒ty G ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ
  
 ℰMg! : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ ★ ⟧ ((⟪ γ ⟫ M) ⟨ G !⟩)
 ℰMg! = ℰ-bind {F = □⟨ G !⟩} ⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVg!))
  where
  𝓟₁ = λ V → 𝒱⟦ gnd⇒ty G ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVg! : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ ★ ⟧ (V ⟨ G !⟩)
  ⊢ℰVg!{V} =
   ⊢ᵒ-sucP Zᵒ λ 𝒱Vsn →
   let v = 𝒱⇒Value (gnd⇒ty G) V 𝒱Vsn in
   𝒱⇒ℰ (𝒱-dyn-intro (constᵒI v) (monoᵒ Zᵒ))
   
red-inj-proj : ∀{G}{H}{W}
   → Value W
   → reducible ((W ⟨ G !⟩) ⟨ H ?⟩)
red-inj-proj {G} {H} {W} w
    with G ≡ᵍ H
... | yes refl = W , (collapse w  refl)
... | no neq = blame , (collide w neq refl)

compatible-project : ∀{Γ}{H}{M}
  → Γ ⊨ M ⦂ ★
    -----------------------------
  → Γ ⊨ M ⟨ H ?⟩ ⦂ gnd⇒ty H
compatible-project {Γ}{H}{M} ⊨M γ = ℰMh?
 where
 ⊢ℰM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ ★ ⟧ (⟪ γ ⟫ M)
 ⊢ℰM = ⊨M γ
  
 ℰMh? : 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ gnd⇒ty H ⟧ ((⟪ γ ⟫ M) ⟨ H ?⟩)
 ℰMh? = ℰ-bind {F = □⟨ H ?⟩} ⊢ℰM (Λᵒ[ V ] →ᵒI (→ᵒI ⊢ℰVh?))
  where
  𝓟₁ = λ V → 𝒱⟦ ★ ⟧ V ∷ (⟪ γ ⟫ M —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢ℰVh? : ∀{V} → 𝓟₁ V ⊢ᵒ ℰ⟦ gnd⇒ty H ⟧ (V ⟨ H ?⟩)
  ⊢ℰVh?{V} =
   let ⊢𝒱V : 𝓟₁ V ⊢ᵒ 𝒱⟦ ★ ⟧ V
       ⊢𝒱V = Zᵒ in
   𝒱-dyn-elim ⊢𝒱V λ { W G refl ⊢w×▷𝒱W →
   let ⊢w = proj₁ᵒ ⊢w×▷𝒱W in
   let ▷𝒱W = proj₂ᵒ ⊢w×▷𝒱W in
   ⊢ᵒ-sucP ⊢w λ{n} w →
   let pres : 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ preservation (gnd⇒ty H)((W ⟨ G !⟩) ⟨ H ?⟩)
       pres = Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ r → ⊢ᵒ-weaken (Goal r w ▷𝒱W)) in
   substᵒ (≡ᵒ-sym ℰ-stmt) (inj₂ᵒ (inj₂ᵒ (constᵒI (red-inj-proj w) ,ᵒ pres)))
   }
    where
    Goal : ∀{W}{G}{H}{N}
       → (W ⟨ G !⟩ ⟨ H ?⟩) —→ N
       → Value W
       → 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G ⟧ W
       → 𝓟₁ (W ⟨ G !⟩) ⊢ᵒ ▷ᵒ ℰ⟦ gnd⇒ty H ⟧ N
    Goal (ξξ □⟨ H ?⟩ refl refl r) w ▷𝒱W =
        ⊥-elim (value-irreducible (w 〈 _ 〉) r)
    Goal {W} (ξξ-blame □⟨ H ?⟩ ())
    Goal {W}{G}{G}{W} (collapse{H} w′ refl) w ▷𝒱W =
       ▷→▷ ▷𝒱W (→ᵒI (𝒱⇒ℰ Zᵒ))
    Goal {W} (collide x x₁ x₂) w ▷𝒱W = monoᵒ ℰ-blame

fundamental : ∀ {Γ A} → (M : Term)
  → Γ ⊢ M ⦂ A
    ----------
  → Γ ⊨ M ⦂ A
fundamental {Γ} {A} .(` _) (⊢` ∋x) =
    compatibility-var ∋x
fundamental {Γ} {.($ₜ ′ℕ)} .($ (Num _)) (⊢$ (Num n)) =
    compatible-nat
fundamental {Γ} {.($ₜ ′𝔹)} .($ (Bool _)) (⊢$ (Bool b)) =
    compatible-bool
fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) =
    compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) =
    compatible-lambda {N = N} (fundamental N ⊢N)
fundamental {Γ} {.★} (M ⟨ G !⟩) (⊢⟨!⟩ ⊢M) =
    compatible-inject {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} (M ⟨ H ?⟩) (⊢⟨?⟩ ⊢M H) =
    compatible-project {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} .blame ⊢blame = compatible-blame

sem-type-safety : ∀ {A} → (M N : Term)
  → (r : M —↠ N)
  → # (ℰ⟦ A ⟧ M) (suc (len r))
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
sem-type-safety {A} M .M (.M END) (inj₁ 𝒱M) =
    inj₁ (𝒱⇒Value A M 𝒱M)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₁ isBlame)) =
    inj₂ (inj₂ refl)
sem-type-safety {A} M .M (.M END) (inj₂ (inj₂ (red , _))) =
    inj₂ (inj₁ red)
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (inj₁ 𝒱M) =
  ⊥-elim (value-irreducible (𝒱⇒Value A M 𝒱M) M→M′)
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (inj₂ (inj₁ isBlame)) =
  ⊥-elim (blame-irreducible M→M′)
sem-type-safety {A} M N (_—→⟨_⟩_ .M {M′} M→M′ M′→N) (inj₂ (inj₂ (_ , presM))) =
    let ℰM′ : # (ℰ⟦ A ⟧ M′) (suc (len M′→N))
        ℰM′ = presM M′ (suc (suc (len M′→N))) ≤-refl M→M′ in
    sem-type-safety M′ N M′→N ℰM′

type-safety : ∀ {A} → (M N : Term)
  → [] ⊢ M ⦂ A
  → M —↠ N
    ---------------------------------------------
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
type-safety M N ⊢M M→N =
  let ℰM = ⊢ᵒ-elim ((fundamental M ⊢M) id) (suc (len M→N)) tt in
  sem-type-safety M N M→N ℰM 
