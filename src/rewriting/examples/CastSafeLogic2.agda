{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafeLogic2 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤ᵖ; tt to ttᵖ)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.StepIndexedLogic2
open import rewriting.examples.CastLogRelLogic2

{-# REWRITE sub-var #-}

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x γ =
     let ⊢𝓥γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ A ⟧ (γ x)
         ⊢𝓥γx = lookup-𝓖 Γ γ ∋x in
     let ⊢𝓔γx : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (γ x)
         ⊢𝓔γx = 𝓥⇒𝓔{A}{𝓖⟦ Γ ⟧ γ} ⊢𝓥γx in
     ⊢𝓔γx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} γ =
     let ⊢𝓥n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓥n = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔n : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′ℕ ⟧ ($ n)
         ⊢𝓔n = 𝓥⇒𝓔{$ₜ ′ℕ}{𝓖⟦ Γ ⟧ γ} ⊢𝓥n in
     ⊢𝓔n

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} γ =
     let ⊢𝓥b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓥⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓥b = ⊢ᵒ-intro λ { zero x → tt ; (suc k) x → refl} in
     let ⊢𝓔b : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ $ₜ ′𝔹 ⟧ ($ b)
         ⊢𝓔b = 𝓥⇒𝓔{$ₜ ′𝔹}{𝓖⟦ Γ ⟧ γ} ⊢𝓥b in
     ⊢𝓔b

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M γ = ⊢𝓔LM
 where
 ⊢𝓔L : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⇒ B ⟧ (⟪ γ ⟫ L)
 ⊢𝓔L = ⊨L γ

 ⊢𝓔M : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)
 ⊢𝓔M = ⊨M γ

 ⊢𝓔LM : 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M))
 ⊢𝓔LM = 𝓔-frame {F = □· (⟪ γ ⟫ M)} ⊢𝓔L
                 (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔VM))
  where
  𝓟₁ = λ V → 𝓥⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ ∷ 𝓖⟦ Γ ⟧ γ
  ⊢𝓔VM : ∀{V} → 𝓟₁ V ⊢ᵒ 𝓔⟦ B ⟧ (V · ⟪ γ ⟫ M)
  ⊢𝓔VM {V} = sucP⊢ᵒQ λ 𝓥Vsn →
       let v = 𝓥⇒Value (A ⇒ B) V 𝓥Vsn in
       let 𝓟₁⊢𝓔M : 𝓟₁ V ⊢ᵒ 𝓔⟦ A ⟧ (⟪ γ ⟫ M)
           𝓟₁⊢𝓔M = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢𝓔M) in
       𝓔-frame {F = v ·□} 𝓟₁⊢𝓔M
           (⊢ᵒ-∀-intro λ V → ⊢ᵒ-→-intro (⊢ᵒ-→-intro ⊢𝓔VW))
   where
   𝓟₂ = λ V W → 𝓥⟦ A ⟧ W ∷ (⟪ γ ⟫ M —↠ W)ᵒ ∷ 𝓥⟦ A ⇒ B ⟧ V ∷ (⟪ γ ⟫ L —↠ V)ᵒ
                 ∷ 𝓖⟦ Γ ⟧ γ
   ⊢𝓔VW : ∀{V W} → 𝓟₂ V W ⊢ᵒ 𝓔⟦ B ⟧ (V · W)
   ⊢𝓔VW {V}{W} =
     let ⊢𝓥V : 𝓟₂ V W ⊢ᵒ 𝓥⟦ A ⇒ B ⟧ V
         ⊢𝓥V = ⊢ᵒ-weaken (⊢ᵒ-weaken ⊢ᵒ-hyp) in
     let ⊢𝓥W : 𝓟₂ V W ⊢ᵒ 𝓥⟦ A ⟧ W
         ⊢𝓥W = ⊢ᵒ-hyp in
     ⊢ᵒ-sucP ⊢𝓥W λ 𝓥Wsn →
     let w = 𝓥⇒Value A W 𝓥Wsn in
     V-fun-elim ⊢𝓥V λ {N′ refl 𝓥W→𝓔NW →
     let prog : 𝓟₂ (ƛ N′) W ⊢ᵒ progress B (ƛ N′ · W)
         prog = (⊢ᵒ-inj₂ (⊢ᵒ-inj₁ (⊢ᵒ-Sᵒ-intro (_ , (β w))))) in
     let pres : 𝓟₂ (ƛ N′) W ⊢ᵒ preservation B (ƛ N′ · W)
         pres = ⊢ᵒ-∀-intro λ N → ⊢ᵒ-→-intro (Sᵒ⊢ᵒ λ {r →
               let ⊢▷𝓔N′W = ⊢ᵒ-→-elim 𝓥W→𝓔NW (⊢ᵒ-mono ⊢𝓥W) in
               let eq = deterministic r (β w) in
                subst (λ N → 𝓟₂ (ƛ N′) W ⊢ᵒ ▷ᵒ 𝓔⟦ B ⟧ N) (sym eq) ⊢▷𝓔N′W}) in
     𝓔-intro prog pres
     }


