open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Environment
import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var
open import Agda.Primitive

module examples.Arith where

data Op : Set where
  op-num : ℕ → Op
  op-mult : Op
  op-let : Op
  op-bool : 𝔹 → Op
  op-if : Op

sig : Op → List ℕ
sig (op-num n) = []
sig op-mult = 0 ∷ 0 ∷ []
sig op-let = 0 ∷ 1 ∷ []
sig (op-bool b) = []
sig op-if = 0 ∷ 0 ∷ 0 ∷ []

open import ScopedTuple
open import Syntax using (Shiftable; ↑; id)
open Syntax.OpSig Op sig using (rename)

open import AbstractBindingTree Op sig renaming (ABT to AST)
pattern $ n  = op-num n ⦅ nil ⦆
pattern # b  = op-bool b ⦅ nil ⦆
infixl 7  _⊗_
pattern _⊗_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
pattern cond_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆

open import Data.Maybe using (Maybe; nothing; just)

data Val : Set where
  v-num : ℕ → Val
  v-bool : 𝔹 → Val

instance
  MVal-is-Shiftable : Shiftable (Maybe Val)
  MVal-is-Shiftable = record { var→val = λ x → nothing ; shift = λ r → r
                      ; var→val-suc-shift = refl }
open Shiftable MVal-is-Shiftable public

_>>=_ : ∀{V : Set} → (Maybe V) → (V → Maybe V) → Maybe V
x >>= f
    with x
... | nothing = nothing
... | just n = f n

num? : ∀{V : Set} → Val → (ℕ → Maybe V) → Maybe V
num? mv f
    with mv
... | v-num n = f n
... | _ = nothing

bool? : ∀{V : Set} → Val → (𝔹 → Maybe V) → Maybe V
bool? mv f
    with mv
... | v-bool b = f b
... | _ = nothing

open import Fold Op sig public

eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
        → Maybe Val
eval-op (op-num n) tt = just (v-num n)
eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
   v₁ ← x ; v₂ ← y 
   num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
eval-op op-let ⟨ x , ⟨ f , tt ⟩ ⟩ = do n ← x; f (just n)
eval-op (op-bool b) tt = just (v-bool b)
eval-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
   vᶜ ← cnd
   bool? vᶜ (λ b → if b then thn else els)

EvalFold : Fold (Maybe Val) (Maybe Val) 
EvalFold = record { V-is-Shiftable = MVal-is-Shiftable
              ; is-Foldable = record { ret = λ x → x ; fold-op = eval-op } }
open Fold EvalFold using (fold; fold-op) public

eval : AST → Maybe Val
eval = fold (↑ 0)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

_ : eval ($ 2 ⊗ $ 21) ≡ just (v-num 42)
_ = refl

_ : eval (` 0) ≡ nothing
_ = refl

_ : eval (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just (v-num 42)
_ = refl

_ : eval (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ nothing
_ = refl

open import Preserve Op sig

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

data ⊢_⦂_ : Val → Type → Set where
  ⊢-nat :  ∀{n} → ⊢ (v-num n) ⦂ t-nat
  ⊢-bool :  ∀{b} → ⊢ (v-bool b) ⦂ t-bool

data _⊢v_⦂_ : List Type → Maybe Val → Type → Set where
  ⊢v-none : ∀{Γ A} → Γ ⊢v nothing ⦂ A
  ⊢v-just :  ∀{Γ v A} → ⊢ v ⦂ A → Γ ⊢v just v ⦂ A

_⊢c_⦂_ : List Type → Maybe Val → Type → Set
Γ ⊢c mv ⦂ A = Γ ⊢v mv ⦂ A

{--- Type Safety via preserve-fold ---}

shift-⊢v : ∀{v A B Δ} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v shift v ⦂ A
shift-⊢v {nothing} ⊢vσx = ⊢v-none
shift-⊢v {just x₁} (⊢v-just ⊢v⦂) = ⊢v-just ⊢v⦂

open FoldPred 𝑃 (λ Γ mv T → ⊤) _⊢v_⦂_ _⊢v_⦂_ 

compress-⊢v : ∀{v A B Δ} → (B ∷ Δ) ⊢v v ⦂ A → Δ ⊢v v ⦂ A
compress-⊢v {.nothing} ⊢v-none = ⊢v-none
compress-⊢v {.(just _)} (⊢v-just x) = ⊢v-just x

op-pres : ∀ {op}{Rs}{Δ}{A : Type}{As : Vec Type (length (sig op))}{Bs}
          → sig op ∣ Δ ∣ Bs ⊢ᵣ₊ Rs ⦂ As
          → 𝑃 op As Bs A → Δ ⊢c (fold-op op Rs) ⦂ A
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
        ⟨ refl , refl ⟩
    with c
... | nothing = ⊢v-none
... | just v =
       let wtres : (T₁ ∷ Δ) ⊢c f (just v) ⦂ T₂
           wtres = ⊢ᵣ→⊢c (Pbody {just v} (shift-⊢v Prhs) tt) in
       compress-⊢v wtres
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

𝐴 : List Type → Maybe Val → Type → Set
𝐴 = λ Γ mv T → ⊤

module TypeSafetyViaPreserveFold where

  EvalPres : FoldPreserveABTPred EvalFold
  EvalPres = record { 𝑉 = λ Γ x A → ⊤ ; 𝑃 = 𝑃 ; 𝐴 = 𝐴
             ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢v_⦂_
             ; shift-⊢v = shift-⊢v ; ret-pres = λ x → x ; op-pres = op-pres }
  open FoldPreserveABTPred EvalPres using (_⊢_⦂_; preserve-fold)

  type-safety : ∀ M
     → [] ⊢ M ⦂ t-nat
     → [] ⊢c eval M ⦂ t-nat
  type-safety M ⊢M = preserve-fold ⊢M (λ x → ⊢v-none)

module TypeSafetyViaPreserveFoldEnv where

  Eval2 : FoldEnv (Var → Maybe Val) (Maybe Val) (Maybe Val) 
  Eval2 = record { is-Foldable = record {ret = λ x → x; fold-op = eval-op}
                 ; is-Env = Fun-is-Env }
  open FoldEnv Eval2 renaming (fold to fold₂)

  eval2 : AST → Maybe Val
  eval2 = fold₂ (λ x → nothing)

  FEPE : FunEnvPredExt _⊢v_⦂_ 𝐴 MVal-is-Shiftable
  FEPE = record { shift-⊢v = shift-⊢v }
  open FunEnvPredExt FEPE 

  EvalPres : FoldEnvPreserveABTPred Eval2
  EvalPres = record { 𝑉 = λ Γ x A → ⊤ ; 𝑃 = 𝑃 ; 𝐴 = 𝐴
             ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢v_⦂_
             ; ext-pres = ext-pres ; ret-pres = λ x → x ; op-pres = op-pres }
  open FoldEnvPreserveABTPred EvalPres using (_⊢_⦂_; preserve-fold) 

  type-safety : ∀ M
     → [] ⊢ M ⦂ t-nat
     → [] ⊢c eval2 M ⦂ t-nat
  type-safety M ⊢M = preserve-fold ⊢M (λ ())


{- Partial Evaluator -}

data Res : Set where
  val : Val → Res
  exp : AST → Res

val? : Res → (Val → Maybe Res) → (AST → Maybe Res) → Maybe Res
val? mv f g
    with mv
... | val v = f v
... | exp M = g M

val→term : Val → AST
val→term (v-num n) = $ n
val→term (v-bool b) = # b

res→term : Res → AST
res→term (val v) = val→term v
res→term (exp M) = M

shift-res : Res → Maybe Res
shift-res (val v) = just (val v)
shift-res (exp M) = just (exp (rename (↑ 1) M))

shift-mres : Maybe Res → Maybe Res
shift-mres nothing = nothing
shift-mres (just r) = shift-res r

pe-op : (op : Op) → Tuple (sig op) (Bind (Maybe Res) (Maybe Res)) → (Maybe Res)
pe-op (op-num n) tt = just (val (v-num n))
pe-op (op-bool b) tt = just (val (v-bool b))
pe-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
   r₁ ← x  ; r₂ ← y 
   val? r₁ (λ v₁ → val? r₂ (λ v₂ → num? v₁ (λ n → num? v₂ (λ m →
                               just (val (v-num (n * m))))))
                           (λ M₂ → just (exp ((val→term v₁) ⊗ M₂))))
           (λ M₁ → just (exp (M₁ ⊗ res→term r₂)))
pe-op op-let ⟨ x , ⟨ f , tt ⟩ ⟩ = do r ← x ; f (just r)
pe-op op-if ⟨ cnd , ⟨ thn , ⟨ els , tt ⟩ ⟩ ⟩ = do
   rᶜ ← cnd ; rᵗ ← thn ; rᵉ ← els
   (val? rᶜ (λ vᶜ → bool? vᶜ (λ b → if b then thn else els))
            (λ Mᶜ → just (exp (cond Mᶜ then res→term rᵗ else res→term rᵉ))))

instance
  MRes-is-Shiftable : Shiftable (Maybe Res)
  MRes-is-Shiftable = record { var→val = λ x → just (exp (` x))
                      ; shift = shift-mres ; var→val-suc-shift = refl }

PEFold : Fold (Maybe Res) (Maybe Res) 
PEFold = record { V-is-Shiftable = MRes-is-Shiftable
              ; is-Foldable = record { ret = λ x → x ; fold-op = pe-op } }
open Fold PEFold renaming (fold to partial-eval) public

_ : partial-eval id ($ 2 ⊗ $ 21) ≡ just (val (v-num 42))
_ = refl

_ : partial-eval id (` 0) ≡ just (exp (` 0))
_ = refl

{- the result should really be (` 0 ⊗ $ 21) -}
_ : partial-eval id (bind $ 21 ｛ ` 1 ⊗ ` 0 ｝) ≡ just (exp (` 1 ⊗ $ 21))
_ = refl

