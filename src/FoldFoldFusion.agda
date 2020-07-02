open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.Fin using (Fin; fromℕ<)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List.Properties using (length-++; ++-assoc; ≡-dec)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties
    using (+-suc; ≤-trans; ≤-step; ≤-refl; ≤-reflexive; m≤m+n; ≤-pred)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Environment
open import Function using (_∘_)
{-open import GenericSubstitution-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import ScopedTuple using (Tuple)
{-import Substitution-}
open import Var

module FoldFoldFusion (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
{-
open import Map Op sig using (map)
-}
import Map
open import Fold Op sig
open import MapFusion Op sig using (QuoteShift)
open import FoldMapFusion Op sig
    using (FoldShift; fold-shift; fold-rename-fusion)
open import GenericSubstitution using (↑; GSubst-is-Env)

import Renaming
open Renaming.WithOpSig Op sig using (rename; ABT-is-Shiftable)

open Shiftable {{...}}
open Env {{...}}
open Quotable {{...}}
open Foldable {{...}}
open RelFold {{...}}
open Similar {{...}}
open QuoteShift {{...}}
open FoldShift {{...}}

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

_⨟_≈_ : ∀{ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ }}
   → Eᶠ → Eᵗ → Eˢ → Set (ℓˢ ⊔ ℓᵗ)
γ ⨟ τ ≈ σ = ∀ x → fold τ “ ret (⟅ γ ⟆ x) ” ≈ ret (⟅ σ ⟆ x)

nth : (xs : List ℕ) → (i : ℕ) → .{i< : i < length xs} → ℕ
nth (x ∷ xs) zero {i<} = x
nth (x ∷ xs) (suc i) {i<} = nth xs i {≤-pred i<}

nth-cong : ∀ (xs ys : List ℕ) (i : ℕ)
  {p : i < length xs }{q : i < length ys }
  → xs ≡ ys
  → nth xs i {p} ≡ nth ys i {q}
nth-cong xs ys i {p}{q} refl = refl

length-++-< : (xs ys : List ℕ) (y : ℕ)
   → length xs < length (xs ++ y ∷ ys)
length-++-< xs ys y rewrite length-++ xs {y ∷ ys}
    | +-suc (length xs) (length ys) = s≤s (m≤m+n _ _)   

nth-++ : ∀ (xs ys : List ℕ) (y : ℕ)
   → nth (xs ++ (y ∷ ys)) (length xs) {length-++-< xs ys y} ≡ y
nth-++ [] ys y = refl
nth-++ (x ∷ xs) ys y = nth-++ xs ys y

≡-rel : ∀ {xs ys : List ℕ} .{ eq : xs ≡ ys } → xs ≡ ys
≡-rel {xs} {ys} {eq}
    with ≡-dec _≟_ xs ys 
... | yes eq-rel = eq-rel
... | no neq = ⊥-elimi (neq eq)


Binder : ∀{ℓ} → Set ℓ → Set ℓ → Set ℓ
Binder V C = (op : Op)
         → (i j : ℕ)
         → .{i< : i < length (sig op)}
         → .{j< : j < nth (sig op) i {i<}}
         → Tuple (sig op) (Bind V C)
         → V

{-- start of experiment 

ind-hyp : ∀{ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ }}
   (k : ℕ) op (b : ℕ)(arg : Arg b)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ
   → (Vˢ → Vᵗ)
   → .{ k< : k < length (sig op) }
   → .{ b≤ : b ≤ nth (sig op) k {k<} }
   → (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
   → Set (ℓˢ ⊔ ℓᵗ)
ind-hyp k op zero (ast M) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    fold τ “ fold γ M ” ≈ fold σ M
ind-hyp k op (suc b) (bind arg) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {≤-trans (≤-step ≤-refl) b≤}
       (γ , bindᶠ op k b {k<} {b≤} rsᶠ)
       (τ , s→t (bindˢ op k b {k<}{b≤} rsˢ))
       (σ , bindˢ op k b {k<} {b≤} rsˢ)

ind-hyps : ∀{ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ }}
   (pbs : List ℕ)(op : Op) (bs : List ℕ) (args : Args bs)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ → (Vˢ → Vᵗ)
   → .{ sig=pbs+bs : sig op ≡ pbs ++ bs }
   → (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
   → Set (ℓˢ ⊔ ℓᵗ)
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
    b≤ : b ≤ nth (sig op) (length pbs) {pbs<}
    b≤ = ≤-trans (≤-reflexive (sym (nth-++ pbs bs b)))
                 (≤-reflexive (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                       {length-++-< pbs bs b}{pbs<} (sym (≡-rel {eq = sig=})))) 

fold-fold-fusion : ∀ {ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}
   {Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
{-
   {{_ : Shiftable Cᵗ}}
-}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
{-
{{_ : Quotable Cᶠ}}
-}
   {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ}}
   {{_ : Similar Vᵗ Vˢ Cᵗ Cˢ}}
   {{_ : FoldShift Vᶠ Cᶠ}} {{_ : FoldShift Vˢ Cˢ}} {{_ : FoldShift Vᵗ Cᵗ}}
   {{_ : QuoteShift Cᶠ}}
   {γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
   (M : ABT)
   → γ ⨟ τ ≈ σ
   → (bindˢ : Binder Vˢ Cˢ) → (bindᶠ : Binder Vᶠ Cᶠ)
   → (s→t : Vˢ → Vᵗ)
   → (op≈ : ∀{op : Op}{args : Args (sig op)}{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
          → γ ⨟ τ ≈ σ
          → ind-hyps [] op (sig op) args (fold-args γ args)
                   (fold-args σ args) bindˢ bindᶠ s→t {refl} γ τ σ
          → fold τ “ fold-op op (fold-args γ args) ”
             ≈ fold-op op (fold-args σ args))
   → fold τ “ fold γ M ” ≈ fold σ M
fold-fold-fusion (` x) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} = γ⨟τ≈σ x
fold-fold-fusion {ℓˢ}{ℓᵗ}{ℓᶠ}{Vˢ}{Cˢ}{Eˢ}{Vᵗ}{Cᵗ}{Eᵗ}{Vᶠ}{Cᶠ}{Eᶠ}{γ}{σ}{τ}
  (op ⦅ args ⦆) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} =
  let rsᶠ = fold-args γ args in
  let rsˢ = fold-args σ args in
  op≈ γ⨟τ≈σ (fuse-args{γ}{σ}{τ} [] op (sig op) args rsᶠ rsˢ {refl} γ⨟τ≈σ)
  where
  fuse-arg : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
     (k : ℕ) op (b : ℕ) (arg : Arg b) 
     (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
     (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
     { k< : k < length (sig op) }
     { b≤ : b ≤ nth (sig op) k {k<} }
     → γ ⨟ τ ≈ σ
     → ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ
  fuse-arg {γ}{σ}{τ} k op zero (ast M) rsᶠ rsˢ γ⨟τ≈σ =
      fold-fold-fusion M γ⨟τ≈σ bindˢ bindᶠ s→t op≈
  fuse-arg {γ}{σ}{τ} k op (suc b) (bind arg) rsᶠ rsˢ {k<} {b≤} γ⨟τ≈σ =
      fuse-arg {γ , bindᶠ op k b {k<} {b≤} rsᶠ}
               {σ , bindˢ op k b {k<} {b≤} rsˢ}
               {τ , s→t (bindˢ op k b {k<} {b≤} rsˢ)}
               k op b arg rsᶠ rsˢ {k<} {b≤′} ext-env
    where
    b≤′ : b ≤ nth (sig op) k
    b≤′ = ≤-trans (≤-step ≤-refl) b≤
    ext-env : (γ , bindᶠ op k b {k<}{b≤} rsᶠ)
              ⨟ (τ , (s→t (bindˢ op k b {k<}{b≤} rsˢ)))
              ≈ (σ , bindˢ op k b {k<}{b≤} rsˢ)
    ext-env zero rewrite lookup-0 γ (bindᶠ op k b {k<}{b≤} rsᶠ)
        | lookup-0 σ (bindˢ op k b {k<}{b≤} rsˢ) = G
        where
        G : fold (τ , s→t (bindˢ op k b {k<}{b≤} rsˢ))
                 “ ret (bindᶠ op k b {k<}{b≤} rsᶠ) ”
            ≈ ret (bindˢ op k b {k<}{b≤} rsˢ)
        G = {!!}
    ext-env (suc x) rewrite lookup-suc γ (bindᶠ op k b {k<}{b≤} rsᶠ) x
        | lookup-suc σ (bindˢ op k b {k<}{b≤} rsˢ) x = {!!}
        where
        J : fold τ “ ret (⟅ γ ⟆ x) ” ≈ ret (⟅ σ ⟆ x)
        J = γ⨟τ≈σ x
        
        H : fold (τ , (s→t (bindˢ op k b {k<}{b≤} rsˢ)))
                 “ ret (⇑ (⟅ γ ⟆ x)) ”
            ≈ ret (⇑ (⟅ σ ⟆ x))
        H = let eqR = begin
                      ret (⇑ (⟅ σ ⟆ x))     ≡⟨ sym (shift-ret (⟅ σ ⟆ x)) ⟩
                      ⇑ (ret (⟅ σ ⟆ x))     ∎
            in
            let eqL = begin
                      fold (τ , (s→t (bindˢ op k b {k<}{b≤} rsˢ)))
                            “ ret (⇑ (⟅ γ ⟆ x)) ”
                      ≡⟨ cong (λ □ → fold (τ , (s→t _)) “ □ ”)
                              (sym (shift-ret (⟅ γ ⟆ x))) ⟩
                      fold (τ , (s→t (bindˢ op k b {k<}{b≤} rsˢ)))
                            “ ⇑ (ret (⟅ γ ⟆ x)) ”
                      ≡⟨ cong (λ □ →  fold (τ , (s→t _)) □) (quote-shift (ret (⟅ γ ⟆ x))) ⟩
                      fold (τ , (s→t (bindˢ op k b {k<}{b≤} rsˢ)))
                           (rename (↑ 1) “ ret (⟅ γ ⟆ x) ”)
                      ≡⟨ fold-rename-fusion “ ret (⟅ γ ⟆ x) ” {!!} {!!} {!!} ⟩
                      fold (⟰ τ) “ ret (⟅ γ ⟆ x) ”
                      ≡⟨ fold-shift τ (⟰ τ) “ ret (⟅ γ ⟆ x) ” {!!} ⟩
                      ⇑ (fold τ “ ret (⟅ γ ⟆ x) ”)
                      ∎
            in
            {!!}
    
  fuse-args : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
     (pbs : List ℕ) op (bs : List ℕ) (args : Args bs) 
     (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
     (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
     { sig= : sig op ≡ pbs ++ bs }
     → γ ⨟ τ ≈ σ
     → ind-hyps pbs op bs args rsᶠ rsˢ bindˢ bindᶠ s→t {sig=} γ τ σ
  fuse-args {γ}{σ}{τ} pbs op [] nil rsᶠ rsˢ {sig=} γ⨟τ≈σ = tt
  fuse-args {γ}{σ}{τ} pbs op (b ∷ bs) (cons arg args) rsᶠ rsˢ {sig=} γ⨟τ≈σ =
      ⟨ (fuse-arg (length pbs) op b arg rsᶠ rsˢ {pbs<sig}{b≤} γ⨟τ≈σ) ,
        (fuse-args (pbs ++ (b ∷ [])) op bs args rsᶠ rsˢ {sig=′} γ⨟τ≈σ) ⟩
    where
    pbs<sig : length pbs < length (sig op)
    pbs<sig rewrite sig= | length-++ pbs {b ∷ bs}
        | +-suc (length pbs) (length bs) = s≤s (m≤m+n _ _)
    sig=′ : sig op ≡ (pbs ++ b ∷ []) ++ bs
    sig=′ rewrite sig= | ++-assoc pbs (b ∷ []) bs = refl
    b≤ : b ≤ nth (sig op) (length pbs) {pbs<sig}
    b≤ = ≤-trans (≤-reflexive (sym (nth-++ pbs bs b)))
                 (≤-reflexive (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                                {length-++-< pbs bs b}{pbs<sig} (sym sig=))) 

 end of experiment --}

ind-hyp : ∀{ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ }}
   (k : ℕ) op (b : ℕ)(arg : Arg b)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ
   → (Vˢ → Vᵗ)
   → .{ k< : k < length (sig op) }
   → .{ b≤ : b ≤ nth (sig op) k {k<} }
   → (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
   → Set (ℓˢ ⊔ ℓᵗ)
ind-hyp k op zero (ast M) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    γ ⨟ τ ≈ σ →
    fold τ “ fold γ M ” ≈ fold σ M
ind-hyp k op (suc b) (bind arg) rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {≤-trans (≤-step ≤-refl) b≤}
       (γ , bindᶠ op k b {k<} {b≤} rsᶠ)
       (τ , s→t (bindˢ op k b {k<}{b≤} rsˢ))
       (σ , bindˢ op k b {k<} {b≤} rsˢ)

ind-hyps : ∀{ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}{Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ }}
   (pbs : List ℕ)(op : Op) (bs : List ℕ) (args : Args bs)
   (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
   (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
   → Binder Vˢ Cˢ → Binder Vᶠ Cᶠ → (Vˢ → Vᵗ)
   → .{ sig=pbs+bs : sig op ≡ pbs ++ bs }
   → (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
   → Set (ℓˢ ⊔ ℓᵗ)
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
    b≤ : b ≤ nth (sig op) (length pbs) {pbs<}
    b≤ = ≤-trans (≤-reflexive (sym (nth-++ pbs bs b)))
                 (≤-reflexive (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                       {length-++-< pbs bs b}{pbs<} (sym (≡-rel {eq = sig=})))) 

fold-fold-fusion : ∀ {ℓˢ ℓᵗ ℓᶠ}{Vˢ Cˢ Eˢ : Set ℓˢ}{Vᵗ Cᵗ Eᵗ : Set ℓᵗ}
   {Vᶠ Cᶠ Eᶠ : Set ℓᶠ}
   {{_ : Env Eˢ Vˢ}} {{_ : Env Eᵗ Vᵗ}} {{_ : Env Eᶠ Vᶠ}}
   {{_ : Foldable Vˢ Cˢ}} {{_ : Foldable Vᵗ Cᵗ}} {{_ : Foldable Vᶠ Cᶠ}} 
   {{_ : Quotable Cᶠ}} {{_ : RelFold Vᵗ Vˢ Cᵗ Cˢ}}
   {{_ : Similar Vᵗ Vˢ Cᵗ Cˢ}}
   {γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
   (M : ABT)
   → γ ⨟ τ ≈ σ
   → (bindˢ : Binder Vˢ Cˢ) → (bindᶠ : Binder Vᶠ Cᶠ)
   → (s→t : Vˢ → Vᵗ)
   → (op≈ : ∀{op : Op}{args : Args (sig op)}{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
          → γ ⨟ τ ≈ σ
          → ind-hyps [] op (sig op) args (fold-args γ args)
                   (fold-args σ args) bindˢ bindᶠ s→t {refl} γ τ σ
          → fold τ “ fold-op op (fold-args γ args) ”
             ≈ fold-op op (fold-args σ args))
   → fold τ “ fold γ M ” ≈ fold σ M
fold-fold-fusion (` x) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} = γ⨟τ≈σ x
fold-fold-fusion {ℓˢ}{ℓᵗ}{ℓᶠ}{Vˢ}{Cˢ}{Eˢ}{Vᵗ}{Cᵗ}{Eᵗ}{Vᶠ}{Cᶠ}{Eᶠ}{γ}{σ}{τ}
  (op ⦅ args ⦆) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ {- fuse-ext -} =
  let rsᶠ = fold-args γ args in
  let rsˢ = fold-args σ args in
  op≈ γ⨟τ≈σ (fuse-args{γ}{σ}{τ} [] op (sig op) args rsᶠ rsˢ {refl})
  where
  fuse-arg : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
     (k : ℕ) op (b : ℕ) (arg : Arg b) 
     (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
     (rsˢ : Tuple (sig op) (Bind Vˢ Cˢ))
     { k< : k < length (sig op) }
     { b≤ : b ≤ nth (sig op) k {k<} }
     → ind-hyp k op b arg rsᶠ rsˢ bindˢ bindᶠ s→t {k<} {b≤} γ τ σ
  fuse-arg {γ}{σ}{τ} k op zero (ast M) rsᶠ rsˢ γ⨟τ≈σ =
      fold-fold-fusion M γ⨟τ≈σ bindˢ bindᶠ s→t op≈
  fuse-arg {γ}{σ}{τ} k op (suc b) (bind arg) rsᶠ rsˢ {k<} {b≤} =
      fuse-arg {γ , bindᶠ op k b {k<} {b≤} rsᶠ}
               {σ , bindˢ op k b {k<} {b≤} rsˢ}
               {τ , s→t (bindˢ op k b {k<} {b≤} rsˢ)}
               k op b arg rsᶠ rsˢ {k<} {b≤′}
    where
    b≤′ : b ≤ nth (sig op) k
    b≤′ = ≤-trans (≤-step ≤-refl) b≤
  fuse-args : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}
     (pbs : List ℕ) op (bs : List ℕ) (args : Args bs) 
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
    b≤ : b ≤ nth (sig op) (length pbs) {pbs<sig}
    b≤ = ≤-trans (≤-reflexive (sym (nth-++ pbs bs b)))
                 (≤-reflexive (nth-cong (pbs ++ b ∷ bs) (sig op) (length pbs)
                                {length-++-< pbs bs b}{pbs<sig} (sym sig=))) 
