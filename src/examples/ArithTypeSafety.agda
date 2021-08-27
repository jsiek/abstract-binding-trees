open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
    using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Product
    using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import examples.Arith hiding (eval-op; eval; evaluate)
open import Fold Op sig
open import FoldPreserve Op sig
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sig
open import Level using (Level; Lift; lift; lower)
open import Var
import Agda.Builtin.Unit

module examples.ArithTypeSafety where

data Type : Set where
  t-nat : Type
  t-bool : Type

𝑃 : (op : Op) → Vec Type (length (sig op))
   → BTypes Type (sig op) → Type → Set
𝑃 (op-num x) []̌ Bss Tᵣ = Tᵣ ≡ t-nat
𝑃 op-mult (T₁ ∷̌ T₂ ∷̌ []̌) Bss Tᵣ = T₁ ≡ t-nat × T₂ ≡ t-nat × Tᵣ ≡ t-nat
𝑃 op-let (T₁ ∷̌ T₂ ∷̌ []̌) ⟨ tt , ⟨ ⟨ T₃ , tt ⟩ , tt ⟩ ⟩ Tᵣ =
    T₂ ≡ Tᵣ × T₁ ≡ T₃
𝑃 (op-bool x) []̌ Bss Tᵣ = Tᵣ ≡ t-bool
𝑃 op-if (Tᶜ ∷̌ Tᵗ ∷̌ Tₑ ∷̌ []̌) Bss Tᵣ = Tᶜ ≡ t-bool × Tᵗ ≡ Tₑ × Tₑ ≡ Tᵣ
𝑃 op-error []̌ tt Tᵣ = ⊤

𝐴 : List Type → Maybe Val → Type → Set
𝐴 Γ mv T = ⊤

𝑉 : List Type → Var → Type → Type → Set
𝑉 Γ x A B = A ≡ B

open import ABTPredicate Op sig 𝑉 𝑃

data ⊢_⦂_ : Val → Type → Set where
  ⊢-nat :  ∀{n} → ⊢ (v-num n) ⦂ t-nat
  ⊢-bool :  ∀{b} → ⊢ (v-bool b) ⦂ t-bool

data _⊢v_⦂_ : List Type → Maybe Val → Type → Set where
  ⊢v-none : ∀{Γ A} → Γ ⊢v nothing ⦂ A
  ⊢v-just :  ∀{Γ v A} → ⊢ v ⦂ A → Γ ⊢v just v ⦂ A

_⊢c_⦂_ : List Type → Maybe Val → Type → Set
Γ ⊢c mv ⦂ A = Γ ⊢v mv ⦂ A

{---------         Type Safety via fold-preserves                     ---------}

shift-⊢v : ∀{v A B Δ} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
shift-⊢v {nothing} ⊢vσx = ⊢v-none
shift-⊢v {just x₁} (⊢v-just ⊢v⦂) = ⊢v-just ⊢v⦂

compress-⊢v : ∀{v A B Δ} → (B ∷ Δ) ⊢v v ⦂ A → Δ ⊢v v ⦂ A
compress-⊢v {.nothing} ⊢v-none = ⊢v-none
compress-⊢v {.(just _)} (⊢v-just x) = ⊢v-just x

open import Structures
open WithOpSig Op sig
open import ScopedTuple using (Tuple; _✖_; zip)

eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
        → Maybe Val
eval-op (op-num n) tt = just (v-num n)
eval-op op-error tt = nothing
eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
   v₁ ← x ; v₂ ← y 
   num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
eval-op op-let ⟨ mv , ⟨ f , tt ⟩ ⟩ = f mv
   {- skipping check on mv, simpler -}
eval-op (op-bool b) tt = just (v-bool b)
eval-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
   vᶜ ← cnd
   bool? vᶜ (λ b → if b then thn else els)

instance
  MVal-is-Foldable : Foldable (Maybe Val) (Maybe Val)
  MVal-is-Foldable = record { ret = λ x → x ; fold-op = eval-op }

eval : (Var → Maybe Val) → AST → Maybe Val
eval = fold

evaluate : AST → Maybe Val
evaluate M = eval (λ x → nothing) M

instance
  _ : FoldPreservable (Maybe Val) (Maybe Val) (Type)
  _ = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; 𝐴 = 𝐴 ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢c_⦂_
             ; ret-pres = λ x → x ; shift-⊢v = shift-⊢v
             ; 𝑉-⊢v = λ { refl ⊢v⦂ → ⊢v⦂ } ; prev-𝑉 = λ x → x }

lift-lower-id : ∀{ℓ ℓ′ : Level}{A : Set ℓ}{x : Lift ℓ′ A}
    → lift (lower x) ≡ x
lift-lower-id = refl

op-pres : ∀ {op}{Rs}{Δ}{A : Type}{As : Vec Type (length (sig op))}{Bs}
          → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
          → 𝑃 op As Bs A → Δ ⊢c (eval-op op Rs) ⦂ A
op-pres {op-num n} nil-r refl = ⊢v-just ⊢-nat
op-pres {op-mult} (cons-r (ast-r Px) (cons-r (ast-r Py) nil-r))
        ⟨ refl , ⟨ refl , refl ⟩ ⟩
    with Px | Py
... | ⊢v-none | _ = ⊢v-none
... | ⊢v-just ⊢v⦂ | ⊢v-none = ⊢v-none
... | ⊢v-just ⊢-nat | ⊢v-just ⊢-nat = ⊢v-just ⊢-nat
op-pres {op-let} {A = Tᵣ}{As = T₁ ∷̌ T₂ ∷̌ []̆}
        (cons-r (ast-r{c = c} Prhs)
                (cons-r (bind-r{b}{Δ = Δ}{f = f} Pbody) nil-r))
        ⟨ refl , refl ⟩ =
    compress-⊢v {B = T₁} (⊢ᵣ→⊢c G)
    where G : ■ ∣ T₁ ∷ Δ ∣ lift Agda.Builtin.Unit.tt ⊢ᵣ f c ⦂ Tᵣ
          G = Pbody (shift-⊢v Prhs) tt
op-pres {op-bool b} nil-r refl = ⊢v-just ⊢-bool
op-pres {op-if} (cons-r (ast-r Pc) (cons-r (ast-r Pthn)
                                   (cons-r (ast-r Pels) nil-r)))
                ⟨ refl , ⟨ refl , refl ⟩ ⟩
    with Pc
... | ⊢v-none = ⊢v-none
... | ⊢v-just (⊢-bool{b})
    with b
... | true = Pthn
... | false = Pels
op-pres {op-error} nil-r tt = ⊢v-none

type-safety : ∀ M
   → [] ⊢ M ⦂ t-nat
   → [] ⊢c evaluate M ⦂ t-nat
type-safety M ⊢M = fold-preserves ⊢M (λ ()) op-pres
