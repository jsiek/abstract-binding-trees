{-# OPTIONS --without-K #-}
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Fin using (Fin; fromℕ<)
open import Data.List using (List; []; _∷_; length; _++_) renaming (map to lmap)
open import Data.List.Properties using (length-++; ++-assoc; ≡-dec)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Function using (_∘_)
open import GSubst
open import Level using (levelOfType)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import ScopedTuple using (Tuple)
open import ListAux
open import Sig
open import Structures
open import Var

module FoldFoldFusion (Op : Set) (sig : Op → List Sig) where

open import AbstractBindingTree Op sig
open import Fold Op sig
open Structures.WithOpSig Op sig

{-
  Example: 
     F is a compilation pass from language Lˢ to Lᵗ
     Fˢ is the denotational semantics Lˢ
     Fᵗ is the denotational semantics of Lᵗ

    Lˢ - Fˢ -> Cˢ
    |          |
    F          ~
    |          |
    V          |
    Lᵗ - Fᵗ -> Cᵗ

 -}

private
  variable
    ℓ : Level
    Vˢ Vᵗ Vᶠ Cˢ Cᵗ Cᶠ : Set ℓ

_⨟ᶠ_≈_ : {{_ : Shiftable Vˢ}} {{_ : Shiftable Vᵗ}} {{_ : Shiftable Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : Equiv Vᵗ Vˢ}}{{_ : Equiv Cᵗ Cˢ }}
   → GSubst Vᶠ → GSubst Vᵗ → GSubst Vˢ → Set (levelOfType Cˢ ⊔ levelOfType Cᵗ)
γ ⨟ᶠ τ ≈ σ = ∀ x → fold τ “ ret (γ x) ” ≈ ret (σ x)


_=ˢ_ : (a : Sig) → (b : Sig) → Dec (a ≡ b)
■ =ˢ ■ = yes refl
■ =ˢ ν b = no λ ()
■ =ˢ ∁ b = no λ ()
ν a =ˢ ■ = no λ ()
ν a =ˢ ν b
    with a =ˢ b
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
ν a =ˢ ∁ b = no λ ()
∁ a =ˢ ■ = no λ ()
∁ a =ˢ ν b = no λ ()
∁ a =ˢ ∁ b
    with a =ˢ b
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }

≡-rel : ∀ {xs ys : List Sig} .{ eq : xs ≡ ys } → xs ≡ ys
≡-rel {xs} {ys} {eq}
    with ≡-dec _=ˢ_ xs ys 
... | yes eq-rel = eq-rel
... | no neq = ⊥-elimi (neq eq)


Binder : ∀{ℓ} → Set → Set ℓ → Set ℓ
Binder V C = (op : Op)
         → (i j : ℕ)
         → .{i< : i < length (sig op)}
         → .{j< : j < sig→ℕ (nth (sig op) i {i<})}
         → Tuple (sig op) (Bind V C)
         → V

ind-hyp : {{_ : Shiftable Vˢ}} {{_ : Shiftable Vᵗ}} {{_ : Shiftable Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : Equiv Vᵗ Vˢ}}{{_ : Equiv Cᵗ Cˢ }}
   (k : ℕ) (op : Op) (b : Sig)(arg : Arg b)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ
   → (Vˢ → Vᵗ)
   → .{ k< : k < length (sig op) }
   → .{ b≤ : (sig→ℕ b) ≤ sig→ℕ (nth (sig op) k {k<}) }
   → (γ : GSubst Vᶠ) (τ : GSubst Vᵗ) (σ : GSubst Vˢ)
   → Set (levelOfType Cˢ ⊔ levelOfType Cᵗ)
ind-hyp k op b (ast M) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    γ ⨟ᶠ τ ≈ σ →
    fold τ “ fold γ M ” ≈ fold σ M
ind-hyp k op (ν b) (bind arg) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {≤-trans (≤-step ≤-refl) b≤}
       (γ , bindᶠ op k (sig→ℕ b) {k<} {b≤} rsᶠ)
       (τ , s→t (bindˢ op k (sig→ℕ b) {k<}{b≤} rsˢ))
       (σ , bindˢ op k (sig→ℕ b) {k<} {b≤} rsˢ)
ind-hyp k op (∁ b) (clear arg) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} id id id

ind-hyps : {{_ : Shiftable Vˢ}} {{_ : Shiftable Vᵗ}} {{_ : Shiftable Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : Equiv Vᵗ Vˢ}}{{_ : Equiv Cᵗ Cˢ }}
   (pbs : List Sig)(op : Op) (bs : List Sig) (args : Args bs)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ → (Vˢ → Vᵗ)
   → .{ sig=pbs+bs : sig op ≡ pbs ++ bs }
   → (γ : GSubst Vᶠ) (τ : GSubst Vᵗ) (σ : GSubst Vˢ)
   → Set (levelOfType Cˢ ⊔ levelOfType Cᵗ)
ind-hyps pbs op [] nil rsᶠ rsˢ bindˢ bindᶠ s→t {sig=} γ τ σ = ⊤
ind-hyps pbs op (b ∷ bs) (cons arg args) rsᶠ rsˢ bindˢ bindᶠ s→t {sig=} γ τ σ =
   ind-hyp (length pbs) op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {pbs<} {b≤} γ τ σ
   × ind-hyps(pbs ++ (b ∷ [])) op bs args rsᶠ rsˢ bindˢ bindᶠ s→t {sig=′} γ τ σ 
    where
    pbs< : length pbs < length (sig op)
    pbs< rewrite ≡-rel {eq = sig=} | length-++ pbs {b ∷ bs}
        | +-suc (length pbs) (length bs) = s≤s (m≤m+n _ _)
    sig=′ : sig op ≡ (pbs ++ b ∷ []) ++ bs
    sig=′ rewrite ≡-rel {eq = sig=} | ++-assoc pbs (b ∷ []) bs = refl
    b≤ : (sig→ℕ b) ≤ sig→ℕ (nth (sig op) (length pbs) {pbs<})
    b≤ rewrite sym (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                       {length-++-< pbs bs b}{pbs<} (sym (≡-rel {eq = sig=})))
       | nth-++ pbs bs b = ≤-refl

fold-fold-fusion : {{_ : Shiftable Vˢ}}{{_ : Shiftable Vᵗ}} {{_ : Shiftable Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : Equiv Cᵗ Cˢ}}
   {{_ : Similar Vᵗ Vˢ Cᵗ Cˢ}}
   {γ : GSubst Vᶠ}{σ : GSubst Vˢ}{τ : GSubst Vᵗ}
   (M : ABT)
   → γ ⨟ᶠ τ ≈ σ
   → (bindˢ : Binder Vˢ Cˢ) → (bindᶠ : Binder Vᶠ Cᶠ)
   → (s→t : Vˢ → Vᵗ)
   → (op≈ : ∀{op : Op}{args : Args (sig op)}
          {γ : GSubst Vᶠ}{σ : GSubst Vˢ}{τ : GSubst Vᵗ}
          → γ ⨟ᶠ τ ≈ σ
          → ind-hyps [] op (sig op) args (fold-args γ args)
                   (fold-args σ args) bindˢ bindᶠ s→t {refl} γ τ σ
          → fold τ “ fold-op op (fold-args γ args) ”
             ≈ fold-op op (fold-args σ args))
   → fold τ “ fold γ M ” ≈ fold σ M
fold-fold-fusion (` x) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} = γ⨟τ≈σ x
fold-fold-fusion {Vˢ = Vˢ}{Vᵗ = Vᵗ}{Vᶠ = Vᶠ}{Cˢ = Cˢ}{Cᵗ = Cᵗ}{Cᶠ = Cᶠ}{γ}{σ}{τ}
  (op ⦅ args ⦆) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} =
  let rsᶠ = fold-args γ args in
  let rsˢ = fold-args σ args in
  op≈ γ⨟τ≈σ (fuse-args{γ}{σ}{τ} [] op (sig op) args rsᶠ rsˢ {refl})
  where
  fuse-arg : ∀{γ : GSubst Vᶠ}{σ : GSubst Vˢ}{τ : GSubst Vᵗ}
     (k : ℕ) op (b : Sig) (arg : Arg b) 
     (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
     (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
     { k< : k < length (sig op) }
     { b≤ : sig→ℕ b ≤ sig→ℕ (nth (sig op) k {k<}) }
     → ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ
  fuse-arg {γ}{σ}{τ} k op b (ast M) rsᶠ rsˢ γ⨟τ≈σ =
      fold-fold-fusion M γ⨟τ≈σ bindˢ bindᶠ s→t op≈
  fuse-arg {γ}{σ}{τ} k op (ν b) (bind arg) rsᶠ rsˢ {k<} {b≤} =
      fuse-arg {γ , bindᶠ op k (sig→ℕ b) {k<} {b≤} rsᶠ}
               {σ , bindˢ op k (sig→ℕ b) {k<} {b≤} rsˢ}
               {τ , s→t (bindˢ op k (sig→ℕ b) {k<} {b≤} rsˢ)}
               k op b arg rsᶠ rsˢ {k<} {b≤′}
      where
      b≤′ : sig→ℕ b ≤ sig→ℕ (nth (sig op) k)
      b≤′ = ≤-trans (≤-step ≤-refl) b≤
  fuse-arg {γ}{σ}{τ} k op (∁ b) (clear arg) rsᶠ rsˢ {k<} {b≤} =
      fuse-arg {id}{id}{id} k op b arg rsᶠ rsˢ {k<}{b≤}
  fuse-args : ∀{γ : GSubst Vᶠ}{σ : GSubst Vˢ}{τ : GSubst Vᵗ}
     (pbs : List Sig) op (bs : List Sig) (args : Args bs) 
     (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
     (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
     { sig= : sig op ≡ pbs ++ bs }
     → ind-hyps pbs op bs args rsᶠ rsˢ bindˢ bindᶠ s→t {sig=} γ τ σ
  fuse-args {γ}{σ}{τ} pbs op [] nil rsᶠ rsˢ {sig=} = tt
  fuse-args {γ}{σ}{τ} pbs op (b ∷ bs) (cons arg args) rsᶠ rsˢ {sig=} =
      ⟨ (fuse-arg (length pbs) op b arg rsᶠ rsˢ {pbs<sig}{b≤}) ,
        (fuse-args (pbs ++ (b ∷ [])) op bs args rsᶠ rsˢ {sig=′}) ⟩
    where
    pbs<sig : length pbs < length (sig op)
    pbs<sig rewrite sig= | length-++ pbs {b ∷ bs}
        | +-suc (length pbs) (length bs) = s≤s (m≤m+n _ _)
    sig=′ : sig op ≡ (pbs ++ b ∷ []) ++ bs
    sig=′ rewrite sig= | ++-assoc pbs (b ∷ []) bs = refl
    b≤ : sig→ℕ b ≤ sig→ℕ (nth (sig op) (length pbs) {pbs<sig})
    b≤ rewrite sym (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                                {length-++-< pbs bs b}{pbs<sig} (sym sig=))
       | (nth-++ pbs bs b) = ≤-refl
