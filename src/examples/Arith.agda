open import Agda.Primitive
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elimi)
open import Data.List using (List; []; _∷_; length) renaming (map to lmap)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat
    using (ℕ; zero; suc; _+_; _*_; _⊔_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import GenericSubstitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Syntax
  using (Sig; sig→ℕ; ν; ■; ↑; _•_; _,_; ext; id; Rename; Shiftable; Equiv;
         Relatable)
open import Var
open import ListAux

module examples.Arith where

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

data Op : Set where
  op-num : ℕ → Op
  op-mult : Op
  op-let : Op
  op-bool : 𝔹 → Op
  op-if : Op
  op-error : Op

sig : Op → List Sig
sig (op-num n) = []
sig op-mult = ■ ∷ ■ ∷ []
sig op-let = ■ ∷ ν ■ ∷ []
sig (op-bool b) = []
sig op-if = ■ ∷ ■ ∷ ■ ∷ []
sig op-error = []

open import ScopedTuple using (Tuple; _✖_; zip)
open Syntax.OpSig Op sig using (rename; rename-id; FV-rename; FV-↑1-0)
open import Fold Op sig 
open import Map Op sig
open import FoldPreserve Op sig
open import FoldFoldFusion Op sig
  renaming (_⨟ᶠ_≈_ to _⨟′_≈_)
open import MapFusion Op sig using (QuoteShift; ABT-is-QuoteShift)
open import FoldMapFusion Op sig
  using (fold-rename-fusion; fold-map-fusion-ext-FV; FoldShift; _⊢_⨟_≈_;
  _⊢ₐ_⨟_≈_; _⊢₊_⨟_≈_)
  renaming (_⨟_⩰_ to _′⨟_≈_)

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


eval-op : (op : Op) → Tuple (lmap sig→ℕ (sig op)) (Bind (Maybe Val) (Maybe Val))
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

{---------         Type Safety via fold-preserves                     ---------}

shift-⊢v : ∀{v A B Δ} → Δ ⊢v v ⦂ A → (B ∷ Δ) ⊢v ⇑ v ⦂ A
shift-⊢v {nothing} ⊢vσx = ⊢v-none
shift-⊢v {just x₁} (⊢v-just ⊢v⦂) = ⊢v-just ⊢v⦂

compress-⊢v : ∀{v A B Δ} → (B ∷ Δ) ⊢v v ⦂ A → Δ ⊢v v ⦂ A
compress-⊢v {.nothing} ⊢v-none = ⊢v-none
compress-⊢v {.(just _)} (⊢v-just x) = ⊢v-just x

instance
  _ : FoldPreservable (Maybe Val) (Maybe Val) (Type)
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

{---------                  Partial Evaluator                         ---------}

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

FV-res : Res → Var → Set
FV-res (val v) x = ⊥
FV-res (exp M) x = FV M x

FV-res-⇑ᵣ-0 : ∀ r → FV-res (⇑ᵣ r) 0 → ⊥
FV-res-⇑ᵣ-0 (exp M) 0∈⇑r = FV-↑1-0 M 0∈⇑r

⟱ : Var → Var
⟱ x = x ∸ 1

⇓ : Res → Res
⇓ (val v) = val v
⇓ (exp M) = exp (map ⟱ M)

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

pe-op : (op : Op) → Tuple (lmap sig→ℕ (sig op)) (Bind Res Res) → Res
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

pe-arg : (Var → Res) → {b : Sig} → Arg b → Bind Res Res (sig→ℕ b)
pe-arg = fold-arg

pe-args : (Var → Res) → {bs : List Sig} → Args bs
   → Tuple (lmap sig→ℕ bs) (Bind Res Res)
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

{---------            Correctness of Partial Evaluator                ---------}

instance
  ≡-is-Equiv : ∀{ℓ}{V : Set ℓ} → Equiv V V 
  ≡-is-Equiv = record { _≈_ = _≡_ }

_≡ᵇ_  : ∀ {ℓ : Level}{V : Set ℓ} → (Bind V V) ✖ (Bind V V)
_≡ᵇ_ {ℓ}{V} = _⩳_{V₁ = V}{V}{V}{V}

≡ᵇ→≡ : ∀ {V : Set}{b}{r r' : Bind V V b}
   → _≡ᵇ_{V = V} r  r' → r ≡ r'
≡ᵇ→≡ {V}{zero} {r} {r'} refl = refl
≡ᵇ→≡ {V}{suc b} {r} {r'} r≡ᵇr' = extensionality λ x → ≡ᵇ→≡{V} (r≡ᵇr' refl)

zip-≡ᵇ→≡ : ∀{V : Set}{bs : List ℕ} {rs rs' : Tuple bs (Bind V V)}
   → zip (_≡ᵇ_{V = V}) rs rs' → rs ≡ rs'
zip-≡ᵇ→≡ {V}{[]} {tt} {tt} tt = refl
zip-≡ᵇ→≡ {V}{b ∷ bs} {⟨ r , rs ⟩} {⟨ r' , rs' ⟩} ⟨ r=r' , z-rs-rs' ⟩ =
    cong₂ ⟨_,_⟩ (≡ᵇ→≡{V} r=r') (zip-≡ᵇ→≡{V} z-rs-rs')

eval-op-cong : ∀{op : Op}
   {rs rs' : Tuple (lmap sig→ℕ (sig op)) (Bind(Maybe Val)(Maybe Val))}
   → zip (_≡ᵇ_{V = Maybe Val}) rs rs' → eval-op  op rs ≡ eval-op op rs'
eval-op-cong z rewrite zip-≡ᵇ→≡ z = refl

instance
  _ : Relatable (Maybe Val) (Maybe Val)
  _ = record { var→val≈ = λ x → refl ; shift≈ = λ { refl → refl } }
  
  _ : Similar (Maybe Val) (Maybe Val) (Maybe Val) (Maybe Val) 
  _ = record { ret≈ = λ x → x ; op⩳ = eval-op-cong }
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
    .{j< : j < sig→ℕ (nth (sig op) i {i<})}
    → Tuple (lmap sig→ℕ (sig op)) (Bind (Maybe Val) (Maybe Val)) → (Maybe Val)
bind-eval op-mult (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)
bind-eval op-if (suc (suc (suc i))) j {i<} {j<} rs = ⊥-elimi (bogus43 i<)
bind-eval op-let (suc zero) zero {i<}{j<} ⟨ r , ⟨ f , tt ⟩ ⟩ = r
bind-eval op-let (suc zero) (suc j) {i<} {j<} rs = ⊥-elimi (bogus21 j<)
bind-eval op-let (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)

bind-pe : (op : Op) → (i j : ℕ)
    .{i< : i < length (sig op)}
    .{j< : j < sig→ℕ (nth (sig op) i {i<})}
    → Tuple (lmap sig→ℕ (sig op)) (Bind Res Res) → Res
bind-pe op-mult (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)
bind-pe op-if (suc (suc (suc i))) j {i<} {j<} rs = ⊥-elimi (bogus43 i<)
bind-pe op-let (suc zero) zero {i<}{j<} ⟨ r , ⟨ f , tt ⟩ ⟩ = ⇑ᵣ r
bind-pe op-let (suc zero) (suc j) {i<} {j<} rs = ⊥-elimi (bogus21 j<)
bind-pe op-let (suc (suc i)) j {i<} {j<} rs = ⊥-elimi (bogus32 i<)

res-shift-ren : ∀ vᶠ → res→ast (⇑ᵣ vᶠ) ≡ rename (↑ 1) (res→ast vᶠ)
res-shift-ren (val (v-num n)) = refl
res-shift-ren (val (v-bool b)) = refl
res-shift-ren (exp M) = refl

res-down-ren : ∀ v → res→ast (⇓ v) ≡ map ⟱ (res→ast v)
res-down-ren (val (v-num n)) = refl
res-down-ren (val (v-bool b)) = refl
res-down-ren (exp M) = refl

eval-shift : ∀ (τ : Var → Maybe Val) M (mv : Maybe Val)
   → eval (τ , mv) (rename (↑ 1) M) ≡ eval τ M
eval-shift τ M mv = fold-rename-fusion M G eval-op-cong (λ v → refl)
  where
  G : _′⨟_≈_{Vᵐ = Var} (↑ 1) (τ , mv) τ
  G zero = refl
  G (suc x) = refl

instance
  _ : FoldShift (Maybe Val) (Maybe Val)
  _ = record { shift-ret = λ v → refl ; op-shift = eval-op-cong }

  _ : QuoteShift Var
  _ = record { quote-var→val = λ x → refl ; quote-shift = λ v → refl }

eval-down : ∀ (γ : Var → Maybe Val) (M : AST) (mv : Maybe Val)
  → (FV M 0 → ⊥)
  → eval γ (map ⟱ M) ≡  eval (γ , mv) M
eval-down γ M mv 0∉M =
  fold-map-fusion-ext-FV {σ = ⟱}{δ = γ}{γ = γ , mv} M G
      (λ{b}{arg} → env-ext{b}{arg}) eval-op-cong 
  where
  G : M ⊢ ⟱ ⨟ γ ≈ (γ , mv)
  G zero 0∈M = ⊥-elim (0∉M 0∈M)
  G (suc x) sx∈M = refl

  env-ext : {b : Sig} {arg : Arg b} {σ : Var → Var}
    {δ : Var → Maybe Val} {γ' : Var → Maybe Val} {v : Maybe Val}
    → (bind arg) ⊢ₐ σ ⨟ δ ≈ γ'
    → arg ⊢ₐ ext σ ⨟ (δ , v) ≈ (γ' , v)
  env-ext σ⨟δ≈γ zero x∈arg = refl
  env-ext σ⨟δ≈γ (suc x) x∈arg = σ⨟δ≈γ x x∈arg


FV-res→ast : ∀ r → FV (res→ast r) ≡ FV-res r
FV-res→ast (val (v-num n)) = refl
FV-res→ast (val (v-bool b)) = refl
FV-res→ast (exp M) = refl

FV-⟱ : ∀ M x → FV (map ⟱ M) x → Σ[ y ∈ ℕ ] y ∸ 1 ≡ x × FV M y
FV-⟱ M x fv = FV-rename ⟱ M x fv

FV-res-⇓ : ∀ r x → FV-res (⇓ r) x → Σ[ y ∈ ℕ ] y ∸ 1 ≡ x × FV-res r y
FV-res-⇓ (val v) x ()
FV-res-⇓ (exp M) x fvr = FV-⟱ M x fvr

FV-⟰ : ∀ M y → FV (rename (↑ 1) M) y → Σ[ z ∈ ℕ ] y ≡ suc z × FV M z
FV-⟰ M y y∈↑M
    with FV-rename (↑ 1) M y y∈↑M
... | ⟨ z , ⟨ refl , fv ⟩ ⟩ = ⟨ z , ⟨ refl , fv ⟩ ⟩

FV-res-⇑ : ∀ r y → FV-res (⇑ᵣ r) y → FV-res r (y ∸ 1)
FV-res-⇑ (exp M) y y∋⇑r
    with FV-⟰ M y y∋⇑r
... | ⟨ z , ⟨ refl , fv ⟩ ⟩ = fv

FV-res-⇑-2 : ∀ r y → FV-res (⇑ᵣ r) y → Σ[ z ∈ ℕ ] y ≡ suc z × FV-res r z
FV-res-⇑-2 (exp M) y y∋⇑r = FV-⟰ M y y∋⇑r

FV-env : (Var → Res) → Var → Set
FV-env γ x = Σ[ y ∈ Var ] FV-res (γ y) x

FV-pe : ∀ γ M x → FV-res (pe γ M) x → FV-env γ x
FV-pe γ (` y) x fvr = ⟨ y , fvr ⟩
FV-pe γ (op-num n ⦅ nil ⦆) x ()
FV-pe γ (op-bool b ⦅ nil ⦆) x ()
FV-pe γ (op-error ⦅ nil ⦆) x ()
FV-pe γ (op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆) x fvr
    with to-num (pe γ L) | to-num (pe γ M)
... | nothing | _
    with fvr
... | inj₁ fvrL rewrite FV-res→ast (pe γ L) = FV-pe γ L x fvrL
... | inj₂ fvr′
    with fvr′
... | inj₁ fvrM rewrite FV-res→ast (pe γ M) = FV-pe γ M x fvrM
... | inj₂ ()
FV-pe γ (op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆) x fvr
    | just ⟨ n₁ , eq₁ ⟩ | nothing rewrite eq₁
    with fvr
... | inj₁ ()
... | inj₂ fvr′
    with fvr′
... | inj₁ fvrM rewrite FV-res→ast (pe γ M) = FV-pe γ M x fvrM
... | inj₂ ()
FV-pe γ (op-mult ⦅ cons (ast L) (cons (ast M) nil) ⦆) x fvr
    | just ⟨ n₁ , eq₁ ⟩ | just ⟨ n₂ , eq₂ ⟩ rewrite eq₁ | eq₂
    with fvr
... | ()
FV-pe γ (op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆) x fvr
    with to-bool (pe γ L)
... | nothing
    with fvr
... | inj₁ fvrL rewrite FV-res→ast (pe γ L) = FV-pe γ L x fvrL
... | inj₂ fvr′
    with fvr′
... | inj₁ fvrM rewrite FV-res→ast (pe γ M) = FV-pe γ M x fvrM
... | inj₂ fvr′′
    with fvr′′
... | inj₁ fvrN rewrite FV-res→ast (pe γ N) = FV-pe γ N x fvrN
... | inj₂ ()    
FV-pe γ (op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆) x fvr
    | just ⟨ b , eq ⟩ rewrite eq 
    with b
... | true = FV-pe γ M x fvr
... | false = FV-pe γ N x fvr
FV-pe γ (op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆) x fvr
    with FV-res-⇓ (pe (γ , (⇑ᵣ (pe γ M))) N) x fvr
... | ⟨ y , ⟨ y-1=x , y∈pe[N] ⟩ ⟩ rewrite sym y-1=x
    with FV-pe (γ , (⇑ᵣ (pe γ M))) N y y∈pe[N]
... | ⟨ 0 , y∈peM ⟩ = FV-pe γ M (y ∸ 1) (FV-res-⇑ (pe γ M) y y∈peM)
... | ⟨ suc z , y∈γz ⟩ =
      let y-1∈γz = FV-res-⇑ (γ z) y y∈γz in
      ⟨ z , y-1∈γz ⟩

FV-0-pe : ∀ γ r M → FV (res→ast (pe (γ , (⇑ᵣ r)) M)) 0 → ⊥
FV-0-pe γ r M 0∈peM
    rewrite FV-res→ast (pe (γ , (⇑ᵣ r)) M)
    with FV-pe (γ , ⇑ᵣ r) M 0 0∈peM
... | ⟨ 0 , 0∈γ⇑r ⟩
    with FV-res-⇑-2 r 0 0∈γ⇑r
... | ⟨ z , ⟨ () , fv ⟩ ⟩
FV-0-pe γ r M 0∈peM
    | ⟨ suc y , 0∈γ⇑r ⟩ 
    with FV-res-⇑-2 (γ y) 0 0∈γ⇑r
... | ⟨ z , ⟨ () , fv ⟩ ⟩

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
        ⟨ IH-L , ⟨ IH-M , tt ⟩ ⟩
       with to-num (pe γ L) | to-num (pe γ M)
   ... | nothing | _ rewrite IH-L γ⨟τ≈σ | IH-M γ⨟τ≈σ = refl
   ... | just ⟨ n₁ , eq₁ ⟩ | nothing
       rewrite eq₁ | sym (IH-L γ⨟τ≈σ) | IH-M γ⨟τ≈σ = refl
   ... | just ⟨ n₁ , eq₁ ⟩ | just ⟨ n₂ , eq₂ ⟩
       rewrite eq₁ | eq₂ | sym (IH-L γ⨟τ≈σ) | sym (IH-M γ⨟τ≈σ) = refl
   op≈ {op-let} {cons (ast M) (cons (bind (ast N)) nil)} {τ} {σ} {γ} γ⨟τ≈σ
       ⟨ IH-M , ⟨ IH-N , tt ⟩ ⟩ = begin
       eval τ (res→ast (⇓ (pe (γ , (⇑ᵣ (pe γ M))) N)))
            ≡⟨ cong (eval τ) (res-down-ren (pe (γ , (⇑ᵣ (pe γ M))) N)) ⟩
       eval τ (map ⟱ (res→ast (pe (γ , (⇑ᵣ (pe γ M))) N)))
            ≡⟨ eval-down τ (res→ast (pe (γ , (⇑ᵣ (pe γ M))) N))
                         _ (FV-0-pe γ (pe γ M) N) ⟩
       eval (τ , eval σ M) (res→ast (pe (γ , (⇑ᵣ (pe γ M))) N))
            ≡⟨ IH-N fuse-ext ⟩
       eval (σ , eval σ M) N     ∎
       where
       fuse-ext : (x : ℕ) → eval (τ , eval σ M) (res→ast ((γ , ⇑ᵣ (pe γ M)) x))
                            ≡ (σ , eval σ M) x
       fuse-ext zero = begin
           eval (τ , eval σ M) (res→ast (⇑ᵣ (pe γ M)))
                ≡⟨ cong (λ □ → eval (τ , eval σ M) □) (res-shift-ren (pe γ M)) ⟩
           eval (τ , eval σ M) (rename (↑ 1) (res→ast (pe γ M)))
                                          ≡⟨ eval-shift τ (res→ast (pe γ M)) _ ⟩
           eval τ (res→ast (pe γ M))                             ≡⟨ IH-M γ⨟τ≈σ ⟩
           eval σ M        ∎
       fuse-ext (suc x) = begin
           eval (τ , eval σ M) (res→ast (⇑ᵣ (γ x)))
                   ≡⟨ cong (λ □ → eval (τ , eval σ M) □) (res-shift-ren (γ x)) ⟩
           eval (τ , eval σ M) (rename (↑ 1) (res→ast (γ x)))
                                           ≡⟨ eval-shift τ ((res→ast (γ x))) _ ⟩
           eval τ (res→ast (γ x))          ≡⟨ γ⨟τ≈σ x ⟩
           σ x                             ∎
   op≈ {op-bool b} {nil} {τ} {σ} {γ} γ⨟τ≈σ tt = refl
   op≈ {op-if} {cons (ast L) (cons (ast M) (cons (ast N) nil))} {τ}{σ}{γ} γ⨟τ≈σ
       ⟨ IH-L , ⟨ IH-M , ⟨ IH-N , tt ⟩ ⟩ ⟩
       with to-bool (pe γ L)
   ... | nothing rewrite IH-L γ⨟τ≈σ | IH-M γ⨟τ≈σ | IH-N γ⨟τ≈σ = refl
   ... | just ⟨ b , eq ⟩ rewrite eq | sym (IH-L γ⨟τ≈σ)
       with b
   ... | true rewrite sym (IH-M γ⨟τ≈σ) = refl
   ... | false rewrite sym (IH-N γ⨟τ≈σ) = refl
   op≈ {op-error} {nil} {τ} {σ} {γ} γ⨟τ≈σ tt = refl
