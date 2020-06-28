open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc; toℕ; inject≤; fromℕ<)
open import Data.List using (List; []; _∷_; length; lookup; _++_)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
    using (+-suc; +-comm; ≤-step; ≤-refl; ≤-trans; m≤m+n; <⇒≤)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Environment
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var
open import ScopedTuple
    using (Tuple; map; _✖_; zip; zip-refl; map-pres-zip; map-compose-zip;
           map-compose; zip-map→rel; Lift-Eq-Tuple; Lift-Rel-Tuple; zip→rel)
open import GenericSubstitution
open import Agda.Primitive using (Level; lzero; lsuc)

module experimental.Fold (Op : Set) (sig : Op → List ℕ) where

open import AbstractBindingTree Op sig
open import Map Op sig

Bind : {ℓᶜ : Level} → Set → Set ℓᶜ → ℕ → Set ℓᶜ
Bind V C zero = C
Bind V C (suc b) = V → Bind V C b

{-------------------------------------------------------------------------------
 Folding over an abstract binding tree
 ------------------------------------------------------------------------------}
record Foldable {ℓᶜ : Level}(V : Set)(C : Set ℓᶜ) : Set (lsuc ℓᶜ) where
  field ret : V → C
        fold-op : (op : Op) → Tuple (sig op) (λ _ → C) → C
        binder : (op : Op) → (i : Fin (length (sig op)))
           → (j : Fin (lookup (sig op) i)) → Tuple (sig op) (Bind V C) → V

open Env {{...}}
open Foldable {{...}}

arg-binder : ∀{ℓ}{V : Set}{C : Set ℓ} {{_ : Foldable V C}}{n : ℕ}
   → (op : Op) → (i : Fin (length (sig op))) → (b : Fin n)
   → (Bind V C (toℕ b)) → Tuple (sig op) (Bind V C)
   → { n≤ : n ≤ lookup (sig op) i}
   → C
arg-binder op i zero r rs′ {n≤} = r
arg-binder {n = suc n} op i (suc b) f rs′ {n≤} =
    let n≤′ = ≤-trans (≤-step ≤-refl) n≤ in
    let x = (f (binder op i (inject≤ b n≤′) rs′)) in
    arg-binder op i b x rs′ {n≤′}


args-binder : ∀{bs}{ℓ}{V : Set}{C : Set ℓ} {{_ : Foldable V C}}{bs′}
   → (op : Op) → (i : Fin (length bs′))
   → Tuple bs (Bind V C)
   → Tuple (sig op) (Bind V C)
   → { bs′++bs≡sig : bs′ ++ bs ≡ sig op }
   → Tuple bs (λ _ → C)
args-binder {[]} op i tt rs′ {i+bs≡sig} = tt
args-binder {b ∷ bs} {bs′ = bs′} op i ⟨ r , rs ⟩ rs′ {bs′++bs≡sig} =
    ⟨ arg-binder {n = lookup (sig op) (fromℕ< {length bs′}{length (sig op)}
          len[bs′]<len[sig])} op (inject≤ i (<⇒≤ len[bs′]<len[sig]))
              {!!} {!!} rs′ {{!!}} ,
      args-binder {bs} {bs′ = bs′ ++ (b ∷ [])} op suc[i] rs rs′
                  {trans (++-assoc bs′ (b ∷ []) bs) bs′++bs≡sig} ⟩
    where
    suc[i] : Fin (length (bs′ ++ b ∷ []))
    suc[i] rewrite length-++ bs′ {b ∷ []} | +-comm (length bs′) 1 = suc i
    len[bs′]<len[sig] : length bs′ < length (sig op)
    len[bs′]<len[sig] rewrite sym (bs′++bs≡sig) | length-++ bs′ {b ∷ bs}
        | +-suc (length bs′) (length bs) = s≤s (m≤m+n (length bs′) (length bs))
    Fin[b] : Fin (lookup (sig op) (fromℕ< len[bs′]<len[sig]))
    Fin[b] = fromℕ< {b}{lookup (sig op) (fromℕ< len[bs′]<len[sig])} {!!}

{-
    G : i ≤ length (sig op)
    G rewrite sym i+bs≡sig = m≤m+n i (suc (length bs))
    H : suc ((toℕ i) + length bs) ≡ length (sig op)
    H rewrite +-suc (toℕ i) (length bs) = i+bs≡sig
-}

{-

fold : ∀{ℓ E V}{C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → ABT → C
fold-arg : ∀{ℓ E V}{C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → {b : ℕ} → Arg b → Bind V C b
fold-args : ∀{ℓ E V}{C : Set ℓ}
   {{_ : Shiftable V}} {{_ : Env E V}} {{_ : Foldable V C}}
   → E → {bs : List ℕ} → Args bs → Tuple bs (Bind V C)

fold σ (` x) = ret (⟅ σ ⟆ x)
fold σ (op ⦅ args ⦆) =
   let rs = fold-args σ {sig op} args in
   fold-op op (args-binder {sig op} 0 op rs rs {refl})
fold-arg σ {zero} (ast M) = fold σ M
fold-arg σ {suc b} (bind arg) v = fold-arg (σ , v) arg
fold-args σ {[]} nil = tt
fold-args σ {b ∷ bs} (cons arg args) = ⟨ fold-arg σ arg , fold-args σ args ⟩

-}
