open import Agda.Primitive
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
    using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Environment
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Var


module examples.Arith where

data Op : Set where
  op-num : ℕ → Op
  op-mult : Op
  op-let : Op
  op-bool : 𝔹 → Op
  op-if : Op
  op-error : Op

sig : Op → List ℕ
sig (op-num n) = []
sig op-mult = 0 ∷ 0 ∷ []
sig op-let = 0 ∷ 1 ∷ []
sig (op-bool b) = []
sig op-if = 0 ∷ 0 ∷ 0 ∷ []
sig op-error = []

open import ScopedTuple using (Tuple; zip)
open import Syntax using (↑; _•_; id; Rename)
open Syntax.OpSig Op sig using (rename; rename-id)
open import Fold Op sig 
open import Map Op sig
open import FoldPreserve Op sig
open import FoldFoldFusion Op sig
  renaming (_⨟_≈_ to _⨟′_≈_)

open import AbstractBindingTree Op sig renaming (ABT to AST)
pattern $ n  = op-num n ⦅ nil ⦆
pattern # b  = op-bool b ⦅ nil ⦆
infixl 7  _⊗_
pattern _⊗_ L M = op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern bind_｛_｝ L M = op-let ⦅ cons (ast L) (cons (bind (ast M)) nil) ⦆
pattern cond_then_else_ L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern error = op-error ⦅ nil ⦆

data Val : Set where
  v-num : ℕ → Val
  v-bool : 𝔹 → Val

instance
  MVal-is-Shiftable : Shiftable (Maybe Val)
  MVal-is-Shiftable = record { var→val = λ x → nothing ; ⇑ = λ r → r
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


eval-op : (op : Op) → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
        → Maybe Val
eval-op (op-num n) tt = just (v-num n)
eval-op op-error tt = nothing
eval-op op-mult ⟨ x , ⟨ y , tt ⟩ ⟩ = do
   v₁ ← x ; v₂ ← y 
   num? v₁ (λ n → num? v₂ (λ m → just (v-num (n * m))))
eval-op op-let ⟨ mv , ⟨ f , tt ⟩ ⟩ = f mv {- skipping check on mv, simpler -}
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

_ : evaluate ($ 2 ⊗ $ 21) ≡ just (v-num 42)
_ = refl

_ : evaluate (` 0) ≡ nothing
_ = refl

_ : evaluate (bind $ 21 ｛ $ 2 ⊗ ` 0 ｝) ≡ just (v-num 42)
_ = refl

_ : evaluate (bind ` 0 ｛ $ 2 ⊗ $ 21 ｝) ≡ just (v-num 42)
_ = refl {- call-by-name behavior wrt. errors because skipped check -}

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

𝑉 : List Type → Var → Type → Set
𝑉 Γ x A = ⊤

open import ABTPredicate Op sig 𝑉 𝑃

data ⊢_⦂_ : Val → Type → Set where
  ⊢-nat :  ∀{n} → ⊢ (v-num n) ⦂ t-nat
  ⊢-bool :  ∀{b} → ⊢ (v-bool b) ⦂ t-bool

data _⊢v_⦂_ : List Type → Maybe Val → Type → Set where
  ⊢v-none : ∀{Γ A} → Γ ⊢v nothing ⦂ A
  ⊢v-just :  ∀{Γ v A} → ⊢ v ⦂ A → Γ ⊢v just v ⦂ A

_⊢c_⦂_ : List Type → Maybe Val → Type → Set
Γ ⊢c mv ⦂ A = Γ ⊢v mv ⦂ A

{--- Type Safety via preserve-fold ---}

shift-⊢v : ∀{v A B Δ} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
shift-⊢v {nothing} ⊢vσx = ⊢v-none
shift-⊢v {just x₁} (⊢v-just ⊢v⦂) = ⊢v-just ⊢v⦂

compress-⊢v : ∀{v A B Δ} → (B ∷ Δ) ⊢v v ⦂ A → Δ ⊢v v ⦂ A
compress-⊢v {.nothing} ⊢v-none = ⊢v-none
compress-⊢v {.(just _)} (⊢v-just x) = ⊢v-just x

instance
  _ : FoldPreservable (Maybe Val) (Maybe Val) (Type) (Var → Maybe Val)
  _ = record { 𝑉 = 𝑉 ; 𝑃 = 𝑃 ; 𝐴 = 𝐴 ; _⊢v_⦂_ = _⊢v_⦂_ ; _⊢c_⦂_ = _⊢c_⦂_
             ; ret-pres = λ x → x ; shift-⊢v = shift-⊢v }

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
    let wtres : (T₁ ∷ Δ) ⊢c f c ⦂ T₂
        wtres = ⊢ᵣ→⊢c (Pbody {c} (shift-⊢v Prhs) tt) in
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
op-pres {op-error} nil-r tt = ⊢v-none

type-safety : ∀ M
   → [] ⊢ M ⦂ t-nat
   → [] ⊢c evaluate M ⦂ t-nat
type-safety M ⊢M = fold-preserves ⊢M (λ x → ⊢v-none) op-pres

{- Partial Evaluator -}

data Res : Set where
  val : Val → Res
  exp : AST → Res

val→term : Val → AST
val→term (v-num n) = $ n
val→term (v-bool b) = # b

res→ast : Res → AST
res→ast (val v) = val→term v
res→ast (exp M) = M

⇑ᵣ : Res → Res
⇑ᵣ (val v) = val v
⇑ᵣ (exp M) = exp (rename (↑ 1) M)

⇓ : Res → Res
⇓ (val v) = val v
⇓ (exp M) = exp (map (λ x → x ∸ 1) M)

to-num : (r : Res) → Maybe (Σ[ n ∈ ℕ ] r ≡ val (v-num n))
to-num (val (v-num n)) = just ⟨ n , refl ⟩
to-num (val (v-bool b)) = nothing
to-num (exp e) = nothing

if-num? : Res → (ℕ → Res) → (AST → Res) → Res
if-num? r f g
    with to-num r
... | nothing = g (res→ast r)
... | just ⟨ n , refl ⟩ = f n

to-bool : (r : Res) → Maybe (Σ[ b ∈ 𝔹 ] r ≡ val (v-bool b))
to-bool (val (v-num n)) = nothing
to-bool (val (v-bool b)) = just ⟨ b , refl ⟩
to-bool (exp e) = nothing

if-bool? : Res → (𝔹 → Res) → (AST → Res) → Res
if-bool? r f g
    with to-bool r
... | nothing = g (res→ast r)
... | just ⟨ b , refl ⟩ = f b

pe-op : (op : Op) → Tuple (sig op) (Bind Res Res) → Res
pe-op (op-num n) tt = val (v-num n)
pe-op (op-bool b) tt = val (v-bool b)
pe-op op-mult ⟨ mr₁ , ⟨ mr₂ , tt ⟩ ⟩ = do
   if-num? mr₁ (λ n₁ → if-num? mr₂ (λ n₂ →  val (v-num (n₁ * n₂)))
                                 (λ N₂ → exp ($ n₁ ⊗ N₂)))
              (λ N₁ → exp (N₁ ⊗ res→ast mr₂))
pe-op op-let ⟨ mr , ⟨ f , tt ⟩ ⟩ = ⇓ (f (⇑ᵣ mr))
pe-op op-if ⟨ mrᶜ , ⟨ mrᵗ , ⟨ mrᵉ , tt ⟩ ⟩ ⟩ = do
   if-bool? mrᶜ (λ b → if b then mrᵗ else mrᵉ)
                (λ Mᶜ → exp (cond Mᶜ then res→ast mrᵗ else res→ast mrᵉ))
pe-op op-error tt = exp error

instance
  Res-is-Shiftable : Shiftable Res
  Res-is-Shiftable = record { var→val = λ x → exp (` x) ; ⇑ = ⇑ᵣ
                            ; var→val-suc-shift = refl }

instance
  PE-is-Foldable : Foldable Res Res
  PE-is-Foldable = record { ret = λ r → r ; fold-op = pe-op }

pe : (Var → Res) → AST → Res
pe = fold

pe-arg : (Var → Res) → {b : ℕ} → Arg b → Bind Res Res b
pe-arg = fold-arg

pe-args : (Var → Res) → {bs : List ℕ} → Args bs → Tuple bs (Bind Res Res)
pe-args = fold-args

init-env : Var → Res
init-env x = exp (` x)

_ : pe init-env ($ 2 ⊗ $ 21) ≡ val (v-num 42)
_ = refl

_ : pe init-env (` 0) ≡ exp (` 0)
_ = refl

_ : pe init-env (bind $ 21 ｛ ` 1 ⊗ ` 0 ｝) ≡ exp (` 0 ⊗ $ 21)
_ = refl

_ : pe init-env (bind ` 1 ｛ ` 1 ⊗ ` 0 ｝) ≡ exp (` 0 ⊗ ` 1)
_ = refl

instance
  _ : RelFold (Maybe Val) (Maybe Val) (Maybe Val) (Maybe Val) 
  _ = record { _∼_ = _≡_ ; _≈_ = _≡_ }

eval-op-cong : ∀{op : Op}{rs : Tuple(sig op)(Bind(Maybe Val)(Maybe Val))}{rs'}
   → zip _⩳_ rs rs'
   → eval-op  op rs ≡ eval-op op rs'
eval-op-cong {op-num x} {rs} {rs'} z = refl
eval-op-cong {op-mult} {⟨ .nothing , ⟨ .nothing , snd ⟩ ⟩}
    {⟨ nothing , ⟨ nothing , tt ⟩ ⟩} ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
eval-op-cong {op-mult} {⟨ .nothing , ⟨ .(just x) , tt ⟩ ⟩}
    {⟨ nothing , ⟨ just x , tt ⟩ ⟩} ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
eval-op-cong {op-mult} {⟨ .(just x) , ⟨ .nothing , tt ⟩ ⟩}
    {⟨ just x , ⟨ nothing , tt ⟩ ⟩} ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
eval-op-cong {op-mult} {⟨ .(just x) , ⟨ .(just x₁) , tt ⟩ ⟩}
    {⟨ just x , ⟨ just x₁ , tt ⟩ ⟩} ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
eval-op-cong {op-let} {⟨ mv , ⟨ fst₃ , tt ⟩ ⟩}
    {⟨ .mv , ⟨ fst₅ , tt ⟩ ⟩} ⟨ refl , ⟨ fst₁ , tt ⟩ ⟩ = fst₁ refl
eval-op-cong {op-bool x} {rs}{ rs'} z = refl
eval-op-cong {op-if} {⟨ fst₃ , ⟨ fst₅ , ⟨ fst₆ , tt ⟩ ⟩ ⟩}
    {⟨ .fst₃ , ⟨ .fst₅ , ⟨ .fst₆ , tt ⟩ ⟩ ⟩}
    ⟨ refl , ⟨ refl , ⟨ refl , tt ⟩ ⟩ ⟩ = refl
eval-op-cong {op-error} {rs}{rs'} z = refl

instance
  _ : Similar (Maybe Val) (Maybe Val) (Maybe Val) (Maybe Val) 
  _ = record { ret≈ = λ x → x ; shift∼ = λ { refl → refl }
             ; op⩳ = eval-op-cong }
  _ : Quotable Res
  _ = record { “_” = res→ast }

bogus21 : ∀{i} → suc (suc i) ≤ 1 → ⊥
bogus21 {i} (s≤s ())

bogus32 : ∀{i} → suc (suc (suc i)) ≤ 2 → ⊥
bogus32 {i} (s≤s (s≤s ()))

bogus43 : ∀{i} → suc (suc (suc (suc i))) ≤ 3 → ⊥
bogus43 {i} (s≤s (s≤s (s≤s ())))

bind-eval : (op : Op) → (i j : ℕ)
    .{i< : i < length (sig op)}
    .{j< : j < nth (sig op) i {i<}}
    → Tuple (sig op) (Bind (Maybe Val) (Maybe Val)) → (Maybe Val)
bind-eval op-mult (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)
bind-eval op-if (suc (suc (suc i))) j {i<} {j<} rs = ⊥-elimi (bogus43 i<)
bind-eval op-let (suc zero) zero {i<}{j<} ⟨ r , ⟨ f , tt ⟩ ⟩ = r
bind-eval op-let (suc zero) (suc j) {i<} {j<} rs = ⊥-elimi (bogus21 j<)
bind-eval op-let (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)

bind-pe : (op : Op) → (i j : ℕ)
    .{i< : i < length (sig op)}
    .{j< : j < nth (sig op) i {i<}}
    → Tuple (sig op) (Bind Res Res) → Res
bind-pe op-mult (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)
bind-pe op-if (suc (suc (suc i))) j {i<} {j<} rs = ⊥-elimi (bogus43 i<)
bind-pe op-let (suc zero) zero {i<}{j<} ⟨ r , ⟨ f , tt ⟩ ⟩ = ⇑ᵣ r
bind-pe op-let (suc zero) (suc j) {i<} {j<} rs = ⊥-elimi (bogus21 j<)
bind-pe op-let (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)

pe-correct : ∀{τ σ : Var → Maybe Val}{γ : Var → Res} (M : AST)
   → (∀ x → eval τ (res→ast (γ x)) ≡ σ x)
   → eval τ (res→ast (pe γ M)) ≡ eval σ M
pe-correct M τ∘γ=σ =
   fold-fold-fusion{Vˢ = Maybe Val}{Vᵗ = Maybe Val}{Vᶠ = Res}
       M τ∘γ=σ bind-eval bind-pe (λ mv → mv) op≈
   where
   op≈ : ∀ {op} {args : Args (sig op)} {τ σ : Var → Maybe Val}{γ : Var → Res}
      → γ ⨟′ τ ≈ σ
      → ind-hyps [] op (sig op) args (fold-args γ args)
          (fold-args σ args) bind-eval bind-pe (λ mv → mv) {refl} γ τ σ
      → fold τ (res→ast (pe-op op (fold-args γ args)))
         ≡  eval-op op (fold-args σ args)
   op≈ {op-num n} {nil} {τ} {σ} {γ} γ⨟τ≈σ tt = refl
   op≈ {op-mult} {cons (ast L) (cons (ast M) nil)} {τ} {σ} {γ} γ⨟τ≈σ
        ⟨ IH-L , ⟨ IH-M , tt ⟩ ⟩ = {!!}
        where
        IH-L′ : fold τ (res→ast (fold γ L)) ≡ fold σ L
        IH-L′ = IH-L γ⨟τ≈σ
        IH-M′ : fold τ (res→ast (fold γ M)) ≡ fold σ M
        IH-M′ = IH-M γ⨟τ≈σ
        
   op≈ {op-let} {cons (ast M) (cons (bind (ast N)) nil)} {τ} {σ} {γ} γ⨟τ≈σ
       ⟨ IH-M , ⟨ IH-N , tt ⟩ ⟩ =
       {!!}
       where
       fuse-ext : (x : ℕ)
                → fold (fun-extend τ (fold σ M))
                    (res→ast (fun-extend γ (⇑ᵣ (fold γ M)) x))
                  ≡ fun-extend σ (fold σ M) x
       fuse-ext = {!!}
       IH-M′ : fold τ (res→ast (fold γ M)) ≡ fold σ M
       IH-M′ = IH-M γ⨟τ≈σ
       IH-N′ : fold (fun-extend τ (fold σ M))
                  (res→ast (fold (fun-extend γ (⇑ᵣ (fold γ M))) N))
                ≡ fold (fun-extend σ (fold σ M)) N
       IH-N′ = IH-N fuse-ext 
       
   op≈ {op-bool b} {nil} {τ} {σ} {γ} γ⨟τ≈σ tt = refl
   op≈ {op-if} {args} {τ} {σ} {γ} γ⨟τ≈σ IHs  = {!!}
   op≈ {op-error} {nil} {τ} {σ} {γ} γ⨟τ≈σ tt = refl

{-


EvalFoldEnv : FoldEnv (Var → Maybe Val) (Maybe Val) (Maybe Val)
EvalFoldEnv = record { is-Foldable = record {ret = λ x → x; fold-op = eval-op}
                     ; is-Env = Fun-is-Env }
open FoldEnv EvalFoldEnv using () renaming (fold to eval; fold-arg to eval-arg;
    fold-args to eval-args)
open Map Rename-is-Map
open GenericSubst Var-is-Shiftable

Res-is-Quotable : Quotable Res
Res-is-Quotable  = record { “_” = res→ast }

res-shift-ren : ∀ vᶠ → res→ast (⇑ vᶠ) ≡ rename (↑ 1) (res→ast vᶠ)
res-shift-ren (val (v-num n)) = refl
res-shift-ren (val (v-bool b)) = refl
res-shift-ren (exp M) = refl

res-down-ren : ∀ v → res→ast (⇓ v) ≡ ren (λ x → x ∸ 1) (res→ast v)
res-down-ren (val (v-num n)) = refl
res-down-ren (val (v-bool b)) = refl
res-down-ren (exp M) = refl

eval-val→term : ∀ (v : Val) τ → eval τ (val→term v) ≡ just v
eval-val→term (v-num n) τ = refl
eval-val→term (v-bool b) τ = refl

_○_≈_ : (σ₂ : Var → Var)(σ₁ : Rename)(σ₃ : Rename) → Set
σ₂ ○ σ₁ ≈ σ₃ = ∀ x → ren σ₂ (` (⦉ σ₁ ⦊  x)) ≡ ` (⦉ σ₃ ⦊  x)

compose-ext : ∀{σ₁}{σ₂}{σ₃}
            → σ₂ ○ σ₁ ≈ σ₃ → fun-ext σ₂ 0 ○ (0 • inc σ₁) ≈ (0 • inc σ₃)
compose-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ zero = refl
compose-ext {σ₁} {σ₂} {σ₃} σ₂∘σ₁≈σ₃ (suc x)
    rewrite g-inc-shift σ₁ x | g-inc-shift σ₃ x =
    cong `_ (cong suc (var-injective (σ₂∘σ₁≈σ₃ x)))


postulate
  eval-shift : ∀ γ M mv
     → eval (fun-ext γ mv) (rename (↑ 1) M) ≡ eval γ M

  eval-down : ∀ γ M mv
     {- 0 ∉ FV M -}
     → eval γ (ren (λ x → x ∸ 1) M) ≡  eval (fun-ext γ mv) M

module PECorrectDirect where

  pe-correct : ∀{γ}{τ}{σ} (M : AST)
     → (∀ x → eval γ (res→ast (τ x)) ≡ σ x)
     → eval γ (res→ast (pe τ M)) ≡ eval σ M
  pe-correct {γ}{τ}{σ} (` x) lk-eq = lk-eq x
  pe-correct {γ}{τ}{σ} (op-num n ⦅ nil ⦆) lk-eq = refl
  pe-correct {γ}{τ}{σ} (op-bool b ⦅ nil ⦆) lk-eq = refl
  pe-correct {γ}{τ}{σ} (op-error ⦅ nil ⦆) lk-eq = refl
  pe-correct {γ}{τ}{σ} (op-let ⦅ cons(ast M)(cons(bind(ast N))nil) ⦆) lk-eq 
      with pe-correct {γ} {τ} {σ} M lk-eq
  ... | IH-M =
      let IH-N :   eval (fun-ext γ (eval σ M))
                        (res→ast (pe (fun-ext τ (⇑ (pe τ M))) N))
                 ≡ eval (fun-ext σ (eval σ M)) N
          IH-N = pe-correct {fun-ext γ (eval σ M)} {fun-ext τ (⇑ (pe τ M))}
                       {fun-ext σ (eval σ M)} N G in
      begin
      eval γ (res→ast (⇓ (pe (fun-ext τ (⇑ (pe τ M))) N)))
         ≡⟨ cong(eval γ)(res-down-ren (pe (fun-ext τ (⇑ (pe τ M))) N)) ⟩
      eval γ (ren(λ x → x ∸ 1)(res→ast (pe (fun-ext τ (⇑ (pe τ M))) N)))
         ≡⟨ eval-down γ(res→ast(pe(fun-ext τ(⇑(pe τ M))) N))(eval σ M) ⟩
      eval (fun-ext γ (eval σ M))
           (res→ast (pe (fun-ext τ (⇑ (pe τ M))) N))           ≡⟨ IH-N ⟩
      eval (fun-ext σ (eval σ M)) N      ∎
      where
      G : (x : Var) → eval (fun-ext γ (eval σ M))
                           (res→ast (fun-ext τ (⇑ (pe τ M)) x))
                      ≡ fun-ext σ (eval σ M) x
      G zero = begin
          eval (fun-ext γ (eval σ M)) (res→ast (⇑ (pe τ M)))
                   ≡⟨ cong (λ □ → eval (fun-ext γ (eval σ M)) □)
                           (res-shift-ren (pe τ M)) ⟩
          eval (fun-ext γ (eval σ M)) (rename (↑ 1) (res→ast (pe τ M)))
                     ≡⟨ eval-shift γ (res→ast (pe τ M)) (eval σ M) ⟩
          eval γ (res→ast (pe τ M))
                     ≡⟨ IH-M ⟩
          eval σ M         ∎
      G (suc x) = begin
          eval (fun-ext γ (eval σ M)) (res→ast (⇑ (τ x)))
                   ≡⟨ cong (eval(fun-ext γ (eval σ M))) (res-shift-ren (τ x))  ⟩
          eval (fun-ext γ (eval σ M)) (rename (↑ 1) (res→ast (τ x)))
                  ≡⟨ eval-shift γ (res→ast (τ x)) (eval σ M) ⟩
          eval γ (res→ast (τ x)) ≡⟨ lk-eq x ⟩
          σ x     ∎
  pe-correct {γ}{τ}{σ}(op-if ⦅ cons(ast L)(cons(ast M)(cons(ast N)nil)) ⦆) lk-eq
      with pe-correct {γ} {τ} {σ} L lk-eq | pe-correct {γ} {τ} {σ} M lk-eq
         | pe-correct {γ} {τ} {σ} N lk-eq
  ... | IH-L | IH-M | IH-N
      with to-bool (pe τ L)
  ... | nothing rewrite IH-L | IH-M | IH-N = refl
  ... | just ⟨ b , eq ⟩ rewrite eq | sym IH-L
      with b
  ... | true rewrite sym IH-M = refl
  ... | false rewrite sym IH-N = refl
  pe-correct {γ}{τ}{σ} (op-mult ⦅ cons (ast L) (cons (ast M) nil)  ⦆) lk-eq
      with pe-correct {γ} {τ} {σ} L lk-eq | pe-correct {γ} {τ} {σ} M lk-eq
  ... | IH-L | IH-M
      with to-num (pe τ L) | to-num (pe τ M)
  ... | nothing | _ rewrite IH-L | IH-M = refl
  ... | just ⟨ n₁ , eq₁ ⟩ | nothing rewrite eq₁ | sym IH-L | IH-M = refl
  ... | just ⟨ n₁ , eq₁ ⟩ | just ⟨ n₂ , eq₂ ⟩
      rewrite eq₁ | eq₂ | sym IH-L | sym IH-M = refl

module PECorrectViaFoldFoldFusion where

  open RelBind {lzero}{Maybe Val}{Maybe Val}{Maybe Val}{Maybe Val} _≡_ _≡_
    using (_⩳_)

  eval-op-cong : ∀(op : Op) (rs : Tuple(sig op)(Bind(Maybe Val)(Maybe Val))) rs'
     → zip _⩳_ rs rs'
     → eval-op  op rs ≡ eval-op op rs'
  eval-op-cong (op-num x) rs rs' z = refl
  eval-op-cong op-mult ⟨ .nothing , ⟨ .nothing , snd ⟩ ⟩
      ⟨ nothing , ⟨ nothing , tt ⟩ ⟩ ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
  eval-op-cong op-mult ⟨ .nothing , ⟨ .(just x) , tt ⟩ ⟩
      ⟨ nothing , ⟨ just x , tt ⟩ ⟩ ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
  eval-op-cong op-mult ⟨ .(just x) , ⟨ .nothing , tt ⟩ ⟩
      ⟨ just x , ⟨ nothing , tt ⟩ ⟩ ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
  eval-op-cong op-mult ⟨ .(just x) , ⟨ .(just x₁) , tt ⟩ ⟩
      ⟨ just x , ⟨ just x₁ , tt ⟩ ⟩ ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
  eval-op-cong op-let ⟨ mv , ⟨ fst₃ , tt ⟩ ⟩
      ⟨ .mv , ⟨ fst₅ , tt ⟩ ⟩ ⟨ refl , ⟨ fst₁ , tt ⟩ ⟩ = fst₁ refl
  eval-op-cong (op-bool x) rs rs' z = refl
  eval-op-cong op-if ⟨ fst₃ , ⟨ fst₅ , ⟨ fst₆ , tt ⟩ ⟩ ⟩
      ⟨ .fst₃ , ⟨ .fst₅ , ⟨ .fst₆ , tt ⟩ ⟩ ⟩
      ⟨ refl , ⟨ refl , ⟨ refl , tt ⟩ ⟩ ⟩ = refl
  eval-op-cong op-error rs rs' z = refl

  open import FoldFoldFusion Op sig

{-
  open ReifyArg {Res}{Res} Res-is-Shiftable Res-is-Quotable
    using (reify-args)
-}

  FME : FuseMapEnvMapEnv Rename-is-MapEnv Ren-is-MapEnv Rename-is-MapEnv
  FME = record { compose-ext = compose-ext }
  open FuseMapEnvMapEnv FME renaming (fusion to ren-rename)

  up-down : ∀ r → ⇓ (⇑ r) ≡ r
  up-down (val v) = refl
  up-down (exp M) = cong exp (trans (ren-rename M (λ x → refl)) rename-id)

  res→ast-⇑-rename : ∀ r
     → res→ast (⇑ r) ≡ rename (↑ 1) (res→ast r)
  res→ast-⇑-rename (val (v-num n)) = refl
  res→ast-⇑-rename (val (v-bool b)) = refl
  res→ast-⇑-rename (exp M) = refl

  open import FoldMapFusion Op sig

  RenPresEval : FuseFoldEnvRename EvalFoldEnv
  RenPresEval = record { op-eq = eval-op-cong ; shiftᶜ = λ mv → mv
                       ; shift-ret = λ v → refl }
  open FuseFoldEnvRename RenPresEval using (rename-fold {-; _⨟_≈_-})

  arg-pe : (op : Op) → ℕ → Tuple (sig op) (Bind Res Res) → Res
  arg-pe (op-num n) k rs = exp (` 0) {- how to make this case impossible? -}
  arg-pe op-mult k rs = exp (` 0)
  arg-pe op-let (suc zero) ⟨ r , ⟨ f , tt ⟩ ⟩ = ⇑ r
  arg-pe op-let _ ⟨ r , ⟨ f , tt ⟩ ⟩ = exp (` 0)
  arg-pe (op-bool b) k rs = exp (` 0)
  arg-pe op-if k rs = exp (` 0)
  arg-pe op-error k rs = exp (` 0)

  arg-eval : (op : Op) → ℕ → Tuple (sig op) (Bind (Maybe Val) (Maybe Val))
      → (Maybe Val)
  arg-eval (op-num x) k rs = nothing
  arg-eval op-mult k rs = nothing
  arg-eval op-let (suc zero) ⟨ mv , ⟨ f , tt ⟩ ⟩ = mv
  arg-eval op-let _ ⟨ mv , ⟨ f , tt ⟩ ⟩ = nothing
  arg-eval (op-bool x) k rs = nothing
  arg-eval op-if k rs = nothing
  arg-eval op-error k rs = nothing

  FFFAux : FuseFoldFoldAux PEFold EvalFoldEnv EvalFoldEnv Res-is-Quotable
  FFFAux = record
             { retᵗ-retˢ = λ v → refl
             ; ret-var→val = λ x → refl
             ; shiftᶜ = λ mv → mv
             ; shift-retˢ = λ v → refl
             ; shift-retᵗ = λ v → refl
             ; ret-shift = res-shift-ren
             ; argᶠ = arg-pe
             ; argˢ = arg-eval
             ; op-congᵗ = eval-op-cong
             ; op-shiftᵗ = {!!}
             }
  open FuseFoldFoldAux FFFAux

  {- The following should be pushed inside FoldFoldFusion -}
  fuse-ext : ∀ γ τ σ M
     → γ ⨟ τ ≈ σ
     → eval τ (res→ast (pe γ M)) ≡ eval σ M
     → (fun-ext γ (⇑ (pe γ M))) ⨟ (fun-ext τ (eval σ M)) ≈ (fun-ext σ (eval σ M))
  fuse-ext γ τ σ M γ⨟τ≈σ IH-M zero = begin
          eval (fun-ext τ (eval σ M)) (res→ast (⇑ (pe γ M)))
                   ≡⟨ cong (λ □ → eval (fun-ext τ (eval σ M)) □)
                           (res-shift-ren (pe γ M)) ⟩
          eval (fun-ext τ (eval σ M)) (rename (↑ 1) (res→ast (pe γ M)))
                     ≡⟨ eval-shift τ (res→ast (pe γ M)) (eval σ M) ⟩
          eval τ (res→ast (pe γ M))
                     ≡⟨ IH-M ⟩
          eval σ M         ∎
  fuse-ext γ τ σ M γ⨟τ≈σ IH-M (suc x) = begin
          eval (fun-ext τ (eval σ M)) (res→ast (⇑ (γ x)))
                   ≡⟨ cong (eval(fun-ext τ (eval σ M))) (res-shift-ren (γ x))  ⟩
          eval (fun-ext τ (eval σ M)) (rename (↑ 1) (res→ast (γ x)))
                  ≡⟨ eval-shift τ (res→ast (γ x)) (eval σ M) ⟩
          eval τ (res→ast (γ x)) ≡⟨ γ⨟τ≈σ x ⟩
          σ x     ∎

  op-cong : (op : Op) (args : Args (sig op)) (γ : Var → Res)
            (τ σ : Var → Maybe Val)
     → γ ⨟ τ ≈ σ
     → ind-hyps 0 op (sig op) args (pe-args γ args) (eval-args σ args) γ τ σ
     → eval τ (res→ast (pe γ (op ⦅ args ⦆)))
       ≡ eval σ (op ⦅ args ⦆)
  op-cong (op-num x) args γ τ σ γ⨟τ≈σ IHs = refl
  op-cong op-mult args γ τ σ γ⨟τ≈σ IHs = {!!}
  op-cong op-let (cons (ast M) (cons (bind (ast N)) nil)) γ τ σ γ⨟τ≈σ
          ⟨ IH-M , ⟨ IH-N , tt ⟩ ⟩ =
      let IH-M′ : eval τ (res→ast (pe γ M)) ≡ eval σ M
          IH-M′ = IH-M γ⨟τ≈σ in
      let IH-N′ :  eval (fun-ext τ (eval σ M))
                        (res→ast (pe (fun-ext γ (⇑ (pe γ M))) N))
                 ≡ eval (fun-ext σ (eval σ M)) N
          IH-N′ = IH-N (fuse-ext γ τ σ M γ⨟τ≈σ IH-M′) in
      begin
      eval τ (res→ast (⇓ (pe (fun-ext γ (⇑ (pe γ M))) N)))
         ≡⟨ cong(eval τ)(res-down-ren (pe (fun-ext γ (⇑ (pe γ M))) N)) ⟩
      eval τ (ren(λ x → x ∸ 1)(res→ast (pe (fun-ext γ (⇑ (pe γ M))) N)))
         ≡⟨ eval-down τ(res→ast(pe(fun-ext γ(⇑(pe γ M))) N))(eval σ M) ⟩
      eval (fun-ext τ (eval σ M))
           (res→ast (pe (fun-ext γ (⇑ (pe γ M))) N))          ≡⟨ IH-N′ ⟩
      eval (fun-ext σ (eval σ M)) N      ∎
  op-cong (op-bool x) args γ τ σ γ⨟τ≈σ IHs = refl
  op-cong op-if args γ τ σ γ⨟τ≈σ IHs = {!!}
  op-cong op-error args γ τ σ γ⨟τ≈σ IHs = refl

  PE-Preserve : FuseFoldEnvFoldEnv PEFold EvalFoldEnv EvalFoldEnv
                                       Res-is-Quotable
  PE-Preserve = record
                  { retᵗ-retˢ = λ v → refl
                  ; ret-var→val = λ x → refl
                  ; shiftᶜ = λ mv → mv
                  ; shift-retˢ = λ v → refl
                  ; shift-retᵗ = λ v → refl
                  ; ret-shift = res-shift-ren
                  ; op-congᵗ = eval-op-cong
                  ; argᶠ = arg-pe
                  ; argˢ = arg-eval
                  ; op-cong = op-cong
                  ; op-shiftᵗ = λ op x → {!!}
                  }


-}
