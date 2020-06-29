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
open import ScopedTuple
{-import Substitution-}
open import Var

module FoldFoldFusion (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Fold Op sig
open import Map Op sig using ()

open Shiftable {{...}}
open Env {{...}}
open Quotable {{...}}
open Foldable {{...}}
open RelFold {{...}}
open Similar {{...}}

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
    γ ⨟ τ ≈ σ → fold τ “ fold γ M ” ≈ fold σ M
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
          → ind-hyps [] op (sig op) args (fold-args γ args)
                   (fold-args σ args) bindˢ bindᶠ s→t {refl} γ τ σ
          → fold τ “ fold-op op (fold-args γ args) ”
             ≈ fold-op op (fold-args σ args))
   → fold τ “ fold γ M ” ≈ fold σ M
fold-fold-fusion (` x) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ = γ⨟τ≈σ x
fold-fold-fusion {ℓˢ}{ℓᵗ}{ℓᶠ}{Vˢ}{Cˢ}{Eˢ}{Vᵗ}{Cᵗ}{Eᵗ}{Vᶠ}{Cᶠ}{Eᶠ}{γ}{σ}{τ}
  (op ⦅ args ⦆) γ⨟τ≈σ bindˢ bindᶠ s→t op≈ =
  let rsᶠ = fold-args γ args in
  let rsˢ = fold-args σ args in
  op≈ (fuse-args{γ}{σ}{τ} [] op (sig op) args rsᶠ rsˢ {refl})
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



{-
module ReifyArg {Vᶠ}{Cᶠ}
  (Vᶠ-is-Shiftable : Shiftable Vᶠ)
  (Cᶠ-is-Quotable : Quotable Cᶠ) where
  open Shiftable {{...}} ; open Quotable {{...}}
  instance _ : Shiftable Vᶠ ; _ = Vᶠ-is-Shiftable
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  
  reify-arg : {b : ℕ} → Bind Vᶠ Cᶠ b → Arg b
  reify-arg {zero} c = ast “ c ”
  reify-arg {suc b} f = bind (reify-arg {b} (f (var→val 0)))

  reify-args : {bs : List ℕ} → Tuple bs (Bind Vᶠ Cᶠ) → Args bs
  reify-args {[]} tt = nil
  reify-args {b ∷ bs} ⟨ r , rs ⟩ = cons (reify-arg r) (reify-args rs)


record FuseFoldFoldAux
  {Vᶠ Cᶠ Eᶠ : Set}
  {V Eˢ Eᵗ : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Eᶠ Vᶠ Cᶠ)
  (Fˢ : FoldEnv Eˢ V C) (Fᵗ : FoldEnv Eᵗ V C)
  (Cᶠ-is-Quotable : Quotable Cᶠ)
  : Set (lsuc ℓ)
  where
  open FoldEnv {{...}} ; open Quotable {{...}}
  instance _ : FoldEnv Eᶠ Vᶠ Cᶠ ; _ = F
           _ : FoldEnv Eˢ V C ; _ = Fˢ
           _ : FoldEnv Eᵗ V C ; _ = Fᵗ
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  open FoldEnv F using () renaming (ret to retᶠ)
  open FoldEnv Fˢ using () renaming (ret to retˢ; fold-op to fold-opˢ;
      lookup-0 to lookup-0ˢ; lookup-suc to lookup-sucˢ)
  open FoldEnv Fᵗ using () renaming (ret to retᵗ; fold-op to fold-opᵗ;
      lookup-0 to lookup-0ᵗ; lookup-suc to lookup-sucᵗ;
      lookup-shift to lookup-shiftᵗ; shift to shiftᵗ)
  open Substitution.ABTOps Op sig using (rename)
  
  field retᵗ-retˢ : ∀ (v : V) → retᵗ v ≡ retˢ v
        ret-var→val : ∀ x → “ ret (var→val x) ” ≡ ` x
        shiftᶜ : C → C
        shift-retˢ : ∀ (v : V) → shiftᶜ (retˢ v) ≡ retˢ (shift v)
        shift-retᵗ : ∀ (v : V) → shiftᶜ (retᵗ v) ≡ retᵗ (shiftᵗ v)
        ret-shift : ∀ (vᶠ : Vᶠ) → “ ret (shift vᶠ) ” ≡ rename (↑ 1) “ ret vᶠ ”
  field argᶠ : (op : Op) → ℕ → Tuple (sig op) (Bind Vᶠ Cᶠ) → Vᶠ
        argˢ : (op : Op) → ℕ → Tuple (sig op) (Bind V C) → V
  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-congᵗ : ∀ op rs rs' → zip _⩳_ rs rs'
                 → fold-opᵗ op rs ≡ fold-opᵗ op rs'
        
  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shiftᵗ v') (λ c c' → c ≡ shiftᶜ c')
           renaming (_⩳_ to _⩳ᵗ_)

  field op-shiftᵗ : ∀ op {rs↑ rs} → zip _⩳ᵗ_ rs↑ rs
                 → fold-opᵗ op rs↑ ≡ shiftᶜ (fold-opᵗ op rs)

  _⨟_≈_ : Eᶠ → Eᵗ → Eˢ → Set ℓ
  γ ⨟ τ ≈ σ = ∀ x → fold τ “ ret (lookup γ x) ” ≡ retˢ (lookup σ x)

  {- need to tell argᶠ which argument place its working on -}

  {- would be nice to remove γ ⨟ τ ≈ σ premise from ind-hyp -}

  ind-hyp : ∀ k op (b : ℕ)(arg : Arg b)
       (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
       (rsˢ : Tuple (sig op) (Bind V C))
       (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ) → Set ℓ
  ind-hyp k op zero (ast M) rsᶠ rsˢ γ τ σ =
      γ ⨟ τ ≈ σ → fold τ “ fold γ M ” ≡ fold σ M
  ind-hyp k op (suc b) (bind arg) rsᶠ rsˢ γ τ σ =
      ind-hyp k op b arg rsᶠ rsˢ (γ , argᶠ op k rsᶠ) (τ , argˢ op k rsˢ)
              (σ , argˢ op k rsˢ)
       
  ind-hyps : ∀ k op (bs : List ℕ)(args : Args bs) 
       (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
       (rsˢ : Tuple (sig op) (Bind V C))
       (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ) → Set ℓ
  ind-hyps k op [] args rsᶠ rsˢ γ τ σ = ⊤
  ind-hyps k op (b ∷ bs) (cons arg args) rsᶠ rsˢ γ τ σ =
    ind-hyp k op b arg rsᶠ rsˢ γ τ σ × ind-hyps (suc k) op bs args rsᶠ rsˢ γ τ σ

  open import FoldMapFusion Op sig

  FS : FoldShift Fᵗ
  FS = record { shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ ; op-shift = op-shiftᵗ}
  open FoldShift FS using (fold-shift)  

  RPF : FuseFoldEnvRename Fᵗ
  RPF = record { op-eq = op-congᵗ ; shiftᶜ = shiftᶜ ; shift-ret = shift-retᵗ }
  open FuseFoldEnvRename RPF using (rename-fold)

  {- need to update this and use it! -}
  ext-pres : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}{v : V}
     → γ ⨟ τ ≈ σ  →  (γ , var→val 0) ⨟ τ , v ≈ (σ , v)
  ext-pres {γ} {σ} {τ} {v} γ⨟τ≈σ zero rewrite lookup-0 γ (var→val 0)
      | lookup-0ˢ σ v | ret-var→val 0 | lookup-0ᵗ τ v = retᵗ-retˢ v
  ext-pres {γ} {σ} {τ} {v} γ⨟τ≈σ (suc x) rewrite lookup-suc γ (var→val 0) x
      | lookup-sucˢ σ v x = begin
      fold (τ , v) “ ret (shift (lookup γ x)) ”
         ≡⟨ cong (fold (τ , v)) (ret-shift (lookup γ x)) ⟩
      fold (τ , v) (rename (↑ 1) “ ret (lookup γ x) ”)
         ≡⟨ rename-fold “ ret (lookup γ x) ” G ⟩
      fold (shift-env τ) “ ret (lookup γ x) ”
         ≡⟨ fold-shift τ (shift-env τ) “ ret (lookup γ x) ” (lookup-shiftᵗ τ) ⟩
      shiftᶜ (fold τ “ ret (lookup γ x) ”)
         ≡⟨ cong shiftᶜ (γ⨟τ≈σ x) ⟩
      shiftᶜ (retˢ (lookup σ x))
         ≡⟨ shift-retˢ (lookup σ x) ⟩
      retˢ (shift (lookup σ x))
      ∎
      where
      G : (FuseFoldEnvRename.MEPFE RPF FuseFoldEnvMapEnv.⨟ ↑ 1
            ≈ (τ , v)) (shift-env τ)
      G zero rewrite lookup-shiftᵗ τ 0 | lookup-sucᵗ τ v 0 = refl
      G (suc x) rewrite lookup-shiftᵗ τ (suc x)
          | lookup-sucᵗ τ v (suc x) = cong retᵗ refl



record FuseFoldEnvFoldEnv {Vᶠ Cᶠ Eᶠ : Set}
  {V Eˢ Eᵗ : Set}{ℓ : Level}{C : Set ℓ}
  (F : FoldEnv Eᶠ Vᶠ Cᶠ)
  (Fˢ : FoldEnv Eˢ V C) (Fᵗ : FoldEnv Eᵗ V C)
  (Cᶠ-is-Quotable : Quotable Cᶠ)
  : Set (lsuc ℓ)
  where
  open FoldEnv {{...}} ; open Quotable {{...}}
  instance _ : FoldEnv Eᶠ Vᶠ Cᶠ ; _ = F
           _ : FoldEnv Eˢ V C ; _ = Fˢ
           _ : FoldEnv Eᵗ V C ; _ = Fᵗ
           _ : Quotable Cᶠ ; _ = Cᶠ-is-Quotable
  open FoldEnv F using () renaming (ret to retᶠ)
  open FoldEnv Fˢ using () renaming (ret to retˢ; fold-op to fold-opˢ;
      lookup-0 to lookup-0ˢ; lookup-suc to lookup-sucˢ)
  open FoldEnv Fᵗ using () renaming (ret to retᵗ; fold-op to fold-opᵗ;
      lookup-0 to lookup-0ᵗ; lookup-suc to lookup-sucᵗ;
      lookup-shift to lookup-shiftᵗ)
  open Shiftable (FoldEnv.V-is-Shiftable Fᵗ) using() renaming (shift to shiftᵗ)
  open Substitution.ABTOps Op sig using (rename)

  field retᵗ-retˢ : ∀ (v : V) → retᵗ v ≡ retˢ v
        ret-var→val : ∀ x → “ ret (var→val x) ” ≡ ` x
        shiftᶜ : C → C
        shift-retˢ : ∀ (v : V) → shiftᶜ (retˢ v) ≡ retˢ (shift v)
        shift-retᵗ : ∀ (v : V) → shiftᶜ (retᵗ v) ≡ retᵗ (shiftᵗ v)
        ret-shift : ∀ (vᶠ : Vᶠ) → “ ret (shift vᶠ) ” ≡ rename (↑ 1) “ ret vᶠ ”
  field argᶠ : (op : Op) → ℕ → Tuple (sig op) (Bind Vᶠ Cᶠ) → Vᶠ
        argˢ : (op : Op) → ℕ → Tuple (sig op) (Bind V C) → V


  open RelBind {ℓ}{V}{C}{V}{C} _≡_ _≡_
  field op-congᵗ : ∀ op rs rs' → zip _⩳_ rs rs'
                 → fold-opᵗ op rs ≡ fold-opᵗ op rs'
  open RelBind {ℓ}{V}{C}{V}{C}
           (λ v v' → v ≡ shiftᵗ v') (λ c c' → c ≡ shiftᶜ c')
           renaming (_⩳_ to _⩳ᵗ_)

  field op-shiftᵗ : ∀ op {rs↑ rs} → zip _⩳ᵗ_ rs↑ rs
                 → fold-opᵗ op rs↑ ≡ shiftᶜ (fold-opᵗ op rs)
  
  open ReifyArg {Vᶠ}{Cᶠ} V-is-Shiftable Cᶠ-is-Quotable
  FFFAux : FuseFoldFoldAux F Fˢ Fᵗ Cᶠ-is-Quotable
  FFFAux = record
             { retᵗ-retˢ = retᵗ-retˢ
             ; ret-var→val = ret-var→val
             ; shiftᶜ = shiftᶜ
             ; shift-retˢ = shift-retˢ
             ; shift-retᵗ = shift-retᵗ
             ; ret-shift = ret-shift
             ; argᶠ = argᶠ
             ; argˢ = argˢ
             ; op-congᵗ = op-congᵗ
             ; op-shiftᵗ = op-shiftᵗ
             }
  open FuseFoldFoldAux FFFAux hiding (argᶠ; argˢ)
  
{-
        op-cong : ∀ op rs rsˢ (τ : Eᵗ)
                → zip _⩳_ (fold-args τ (reify-args rs)) rsˢ
                → fold τ “ fold-op op rs ” ≡ fold-opˢ op rsˢ
-}
{-
        Need to ditch reify-args to get the right induction hypothesis
        to the client, but how? 
        Need environments extended in the right way depending on each
        fold and op!
-}
{-      This one uses reify a la Safe Universes.
        op-cong : ∀ op (args : Args (sig op)) (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
                → zip _⩳_ (fold-args τ (reify-args (fold-args γ args)))
                          (fold-args σ args)
                → fold τ “ fold γ (op ⦅ args ⦆) ” ≡ fold σ (op ⦅ args ⦆)
-}
  field op-cong : ∀ op (args : Args (sig op)) (γ : Eᶠ) (τ : Eᵗ) (σ : Eˢ)
                → γ ⨟ τ ≈ σ
                → ind-hyps 0 op (sig op) args (fold-args γ args)
                             (fold-args σ args) γ τ σ
                → fold τ “ fold γ (op ⦅ args ⦆) ” ≡ fold σ (op ⦅ args ⦆)


       
  fusion : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ} (M : ABT)
    → γ ⨟ τ ≈ σ
    → fold τ “ fold γ M ” ≡ fold σ M

{-
  fuse-arg : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}{b : ℕ} (arg : Arg b)
    → γ ⨟ τ ≈ σ
    → fold-arg τ (reify-arg (fold-arg γ arg)) ⩳ fold-arg σ arg
  fuse-args : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}{bs : List ℕ} (args : Args bs)
    → γ ⨟ τ ≈ σ
    → zip _⩳_ (fold-args τ (reify-args (fold-args γ args)))
              (fold-args σ args)
  fusion {γ}{σ}{τ} (` x) γ⨟τ≈σ = γ⨟τ≈σ x
  fusion {γ}{σ}{τ} (op ⦅ args ⦆) γ⨟τ≈σ =
     let pa = fuse-args args γ⨟τ≈σ in
     op-cong op args γ τ σ pa
  fuse-arg {γ} {σ} {τ} (ast M) γ⨟τ≈σ = fusion M γ⨟τ≈σ
  fuse-arg {γ} {σ} {τ} (bind arg) γ⨟τ≈σ refl = fuse-arg arg (ext-pres γ⨟τ≈σ)
  fuse-args {γ} {σ} {τ} nil γ⨟τ≈σ = tt
  fuse-args {γ} {σ} {τ}{b ∷ bs} (cons arg args) γ⨟τ≈σ =
      ⟨ fuse-arg {b = b} arg γ⨟τ≈σ , fuse-args {bs = bs} args γ⨟τ≈σ ⟩
-}

  fuse-arg : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}{b : ℕ}
      (k : ℕ) {- which argument -}
      (arg : Arg b) op
      (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
      (rsˢ : Tuple (sig op) (Bind V C))
    → ind-hyp k op b arg  rsᶠ rsˢ γ τ σ
  fuse-args : ∀{γ : Eᶠ}{σ : Eˢ}{τ : Eᵗ}{bs : List ℕ}
      (k : ℕ)
      (args : Args bs) op
      (rsᶠ : Tuple (sig op) (Bind Vᶠ Cᶠ))
      (rsˢ : Tuple (sig op) (Bind V C))
    → ind-hyps k op bs args rsᶠ rsˢ γ τ σ
    
  fusion {γ}{σ}{τ} (` x) γ⨟τ≈σ = γ⨟τ≈σ x
  fusion {γ}{σ}{τ} (op ⦅ args ⦆) γ⨟τ≈σ =
     let IHs = fuse-args 0 args op (fold-args γ args) (fold-args σ args) in
     op-cong op args γ τ σ γ⨟τ≈σ IHs
  fuse-arg {γ} {σ} {τ}{zero} k (ast M) op rsᶠ rsˢ γ⨟τ≈σ = fusion M γ⨟τ≈σ
  fuse-arg {γ} {σ} {τ}{suc b} k (bind arg) op rsᶠ rsˢ =
      fuse-arg {γ , argᶠ op k rsᶠ}{σ , argˢ op k rsˢ}{τ , argˢ op k rsˢ}
                        k arg op rsᶠ rsˢ 
  fuse-args {γ} {σ} {τ} k nil op rsᶠ rsˢ = tt
  fuse-args {γ} {σ} {τ}{b ∷ bs} k (cons arg args) op rsᶠ rsˢ =
      ⟨ fuse-arg {b = b} k arg op rsᶠ rsˢ ,
        fuse-args {bs = bs} (suc k) args op rsᶠ rsˢ ⟩


-}
