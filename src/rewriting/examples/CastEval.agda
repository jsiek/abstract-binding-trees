{-# OPTIONS --rewriting #-}
module rewriting.examples.CastEval where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to topᵖ; tt to ttᵖ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast

_⊢_ : List Type → Type → Set
Γ ⊢ A = Σ[ M ∈ Term ] Γ ⊢ M ⦂ A

data _⊢v_ : List Type → Type → Set where
  val : ∀{Γ A} → (V : Term) → (Γ ⊢ V ⦂ A) → Value V → Γ ⊢v A

data _⊢t_ : List Type → Type → Set where
  tval : ∀{Γ A} → (Γ ⊢v A) → Γ ⊢t A
  tblame : ∀{Γ A} → Γ ⊢t A

data _⊢r_ : List Type → Type → Set where
  rterm : ∀{Γ A} → (Γ ⊢t A) → Γ ⊢r A
  rtimeout : ∀{Γ A} → Γ ⊢r A

⊢v⇒⊢A : ∀{Γ A} → Γ ⊢v A → Γ ⊢ A
⊢v⇒⊢A (val V ⊢V v) = (V , ⊢V)

⊢v⇒trm : ∀{Γ A} → Γ ⊢v A → Term
⊢v⇒trm (val V ⊢V v) = V

Value-⊢v⇒trm : ∀{Γ A}
     (V : Γ ⊢v A)
   → Value (⊢v⇒trm V)
Value-⊢v⇒trm (val V ⊢V v) = v

⊢v⇒wt : ∀{Γ A} → (d : Γ ⊢v A) → Γ ⊢ (⊢v⇒trm d) ⦂ A
⊢v⇒wt (val V ⊢V v) = ⊢V

trm : ∀{Γ A} → Γ ⊢t A → Term
trm (tval ⊢v) = ⊢v⇒trm ⊢v
trm tblame = blame

letB : ∀{Γ A B} → Γ ⊢r A → (Γ ⊢v A → Γ ⊢r B) → Γ ⊢r B
letB (rterm (tval ⊢V)) f = f ⊢V
letB (rterm (tblame)) f = rterm tblame
letB rtimeout f = rtimeout

letB-syntax = letB
infix 1 letB-syntax
syntax letB-syntax M (λ x → N) = letᵇ x := M ; N

postulate wt-subst : ∀{Γ}{A}{B}{N}{W} → Γ ⊢ W ⦂ A → A ∷ Γ ⊢ N ⦂ B → Γ ⊢ N [ W ] ⦂ B

_⊙_ : ∀{Γ A B} → Γ ⊢v (A ⇒ B) → Γ ⊢v A → Γ ⊢ B
(val (ƛ N) (⊢ƛ ⊢N) (ƛ̬ N)) ⊙ (val W ⊢W w) = (N [ W ]) , wt-subst ⊢W ⊢N

inject : ∀{Γ G} → Γ ⊢v gnd⇒ty G → Γ ⊢v ★
inject {Γ} {G} (val V ⊢V v) = val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)

project : ∀{Γ H} → Γ ⊢v ★ → Γ ⊢r gnd⇒ty H
project {Γ} {H} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉))
    with G ≡ᵍ H
... | yes refl = rterm (tval (val V ⊢V v))
... | no neq = rterm tblame

eval : ∀{A} → [] ⊢ A → ℕ → [] ⊢r A
eval ⊢M zero = rtimeout
eval (_ , ⊢` ()) (suc k)
eval (_ , ⊢$ c) (suc k) = rterm (tval (val ($ c) (⊢$ c) ($̬ c)))
eval (_ , ⊢ƛ ⊢N) (suc k) = rterm (tval (val (ƛ _) (⊢ƛ ⊢N) (ƛ̬ _)))
eval ((L · M) , (⊢· ⊢L ⊢M)) (suc k) =
    letᵇ ⊢V := eval (L , ⊢L) k ; letᵇ ⊢W := eval (M , ⊢M) k ; eval (⊢V ⊙ ⊢W) k
eval ((M ⟨ G !⟩) , (⊢⟨!⟩ ⊢M)) (suc k) =
    letᵇ ⊢V := eval (M , ⊢M) k ; rterm (tval (inject ⊢V))
eval ((M ⟨ H ?⟩) , ⊢⟨?⟩ ⊢M _) (suc k) =
    letᵇ ⊢V := eval (M , ⊢M) k ;
    letᵇ ⊢W := project{H = H} ⊢V ; eval (⊢v⇒⊢A ⊢W) k
eval (blame , ⊢blame) (suc k) = rterm tblame

infixr 6 _⇓ᵗ_
_⇓ᵗ_ : Term → Term → Set
M ⇓ᵗ V = ∃[ k ] ∃[ A ] Σ[ ⊢M ∈ [] ⊢ M ⦂ A ] ∃[ ⊢V ] ∃[ v ]
   eval (M , ⊢M) k ≡ rterm (tval (val V ⊢V v))

_⇓ᵇ : Term → Set
M ⇓ᵇ = ∃[ k ] ∃[ A ] Σ[ ⊢M ∈ [] ⊢ M ⦂ A ] eval (M , ⊢M) k ≡ rterm tblame

_⇑ : Term → Set
M ⇑ = ∀{k}{A}{⊢M : [] ⊢ M ⦂ A} → eval (M , ⊢M) k ≡ rtimeout

letB-term-inv : ∀{Γ A B}{M : Γ ⊢r A}{f : Γ ⊢v A → Γ ⊢r B}{⊢t}
   → letB M f ≡ rterm ⊢t
   → (∃[ ⊢M ] (M ≡ rterm (tval ⊢M)) × (f ⊢M ≡ rterm ⊢t))
     ⊎ (M ≡ rterm tblame × ⊢t ≡ tblame)
letB-term-inv {M = rterm (tval (val V ⊢V v))} {f} {⊢t} eq =
    inj₁ (val V ⊢V v , refl , eq)
letB-term-inv {M = rterm tblame} {f} {⊢t} refl = inj₂ (refl , refl)

eval-mono : ∀{k}{A}{M : [] ⊢ A}{⊢t} → (eval M k ≡ rterm ⊢t) → ∀{k′} → k ≤ k′
   → eval M k′ ≡ rterm ⊢t
eval-mono {suc k}{A}{(_ , ⊢` ())} 
eval-mono {suc k} {.($ₜ typeof c)} {_ , ⊢$ c} refl {suc k′} (s≤s k≤k′) = refl
eval-mono {suc k}{A}{(_ , ⊢ƛ ⊢N)} refl {suc k′} (s≤s k≤k′) = refl
eval-mono {suc k}{A}{(L · M , ⊢· ⊢L ⊢M)} eq {suc k′} (s≤s k≤k′)
    with letB-term-inv{M = eval (L , ⊢L) k} eq 
... | inj₂ (eq3 , refl) rewrite eval-mono eq3 k≤k′ = refl
... | inj₁ (⊢V , eq2 , eq1)
    with letB-term-inv{M = eval (M , ⊢M) k} eq1
... | inj₂ (eq4 , refl) rewrite eval-mono eq2 k≤k′ | eval-mono eq4 k≤k′ = refl
... | inj₁ (xx , eqM , eq5) rewrite eval-mono eq2 k≤k′ | eval-mono eqM k≤k′
       | eval-mono eq5 k≤k′ = refl
eval-mono {suc k}{A}{((M ⟨ G !⟩) , ⊢⟨!⟩ ⊢M)} eq {suc k′} (s≤s k≤k′)
    with letB-term-inv{M = eval (M , ⊢M) k} eq 
... | inj₂ (eqM , refl) rewrite eval-mono eqM k≤k′ = refl
... | inj₁ (⊢V , eqM , eqInj) rewrite eval-mono eqM k≤k′ = eqInj
eval-mono {suc k}{A}{((M ⟨ H ?⟩) , ⊢⟨?⟩ ⊢M _)} eq {suc k′} (s≤s k≤k′)
    with letB-term-inv{M = eval (M , ⊢M) k} eq 
... | inj₂ (eqM , refl) rewrite eval-mono eqM k≤k′ = refl
... | inj₁ (⊢V , eqM , eqLet) rewrite eval-mono eqM k≤k′
    with letB-term-inv{M = project ⊢V} eqLet
... | inj₂ (eqProj , refl) rewrite eqProj = refl
... | inj₁ (⊢W , eqProj , eqW) rewrite eqProj = eval-mono eqW k≤k′
eval-mono {suc k}{A}{(_ , ⊢blame)} refl {suc k′} (s≤s k≤k′) = refl

Value-tval : ∀{Γ}{A} (V : Γ ⊢v A)
   → Value (trm (tval V))
Value-tval (val V ⊢V v) = v

eval-app-inv : ∀{A}{B}{V : [] ⊢v (A ⇒ B)}{W : [] ⊢v A}{k}{⊢t}
   → eval (V ⊙ W) k ≡ rterm ⊢t
   → ∃[ N ] ∃[ ⊢N ] V ≡ val (ƛ N) (⊢ƛ ⊢N) (ƛ̬ N)
       × eval (N [ ⊢v⇒trm W ] , wt-subst (⊢v⇒wt W) ⊢N) k ≡ rterm ⊢t
eval-app-inv {A}{B}{val (ƛ N) (⊢ƛ ⊢N) (ƛ̬ N)}{val W ⊢W w}{k}{⊢t} evalV·W =
  N , (⊢N , (refl , evalV·W))

project-blame-inv : ∀{Γ}{V}{G}{H}{⊢V}{v}
   → project{Γ}{H} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ rterm tblame
   → G ≢ H
project-blame-inv{G = G}{H} eqProj
    with G ≡ᵍ H
... | no neq = λ G=H → neq G=H
... | yes refl
    with eqProj
... | ()

project-value-inv : ∀{Γ}{V}{G}{H}{⊢V}{v}{W}
   → project{Γ}{H} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ rterm (tval W)
   → G ≡ H
project-value-inv{G = G}{H} eqProj
    with G ≡ᵍ H
... | yes refl = refl
... | no neq
    with eqProj
... | ()

project-value-inv2 : ∀{Γ}{V}{G}{⊢V}{v}{W}
   → project{Γ}{G} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ rterm (tval W)
   → W ≡ (val V ⊢V v)
project-value-inv2{G = G}{W = val W ⊢W w} eqProj 
    with G ≡ᵍ G
... | no neq
    with eqProj
... | ()
project-value-inv2{G = G}{W = val W ⊢W w} eqProj  | yes refl
    with eqProj
... | refl = refl    

eval-sound : ∀{A} → (M : [] ⊢ A) → ∀{k}{⊢t} → eval M k ≡ rterm ⊢t
   → proj₁ M —↠ trm ⊢t
eval-sound (M , ⊢M) {0}{⊢t} ()
eval-sound (($ c) , ⊢$ c) {suc k}{tval (val ($ c′) _ _)} refl = _ END
eval-sound ((L · M) , ⊢· ⊢L ⊢M) {suc k}{⊢t} eq
    with letB-term-inv{M = eval (L , ⊢L) k} eq
... | inj₂ (eqL , refl) = app-blame-L (eval-sound (L , ⊢L) {k} eqL)
... | inj₁ (V , eqL , eqLet) rewrite eqL
    with letB-term-inv{M = eval (M , ⊢M) k} eqLet
... | inj₂ (eqM , refl) rewrite eqM =
      let IHL = eval-sound (L , ⊢L) {k} eqL in
      let IHM = eval-sound (M , ⊢M) {k} eqM in
      app-blame-R IHL (Value-tval V) IHM
... | inj₁ (W , eqM , eqLet2) rewrite eqM
    with eval-app-inv{V = V}{W}{k} eq
... | N , ⊢N , refl , evalN[W] =     
      let IHL = eval-sound (L , ⊢L) {k} eqL in
      let IHM = eval-sound (M , ⊢M) {k} eqM in
      let IHNW = eval-sound (N [ ⊢v⇒trm W ] , wt-subst (⊢v⇒wt W) ⊢N) {k}
                     evalN[W] in
      app-beta IHL IHM (Value-⊢v⇒trm W) IHNW
eval-sound ((ƛ N) , ⊢ƛ ⊢M) {suc k}{⊢t} refl = _ END
eval-sound ((M ⟨ G !⟩) , ⊢⟨!⟩ ⊢M) {suc k}{⊢t} eq
    with letB-term-inv{M = eval (M , ⊢M) k} eq
... | inj₂ (eqM , refl) = inj-blame (eval-sound (M , ⊢M) {k} eqM)
... | inj₁ ((val V ⊢V v) , eqM , refl) =
    let IHM = eval-sound (M , ⊢M) {k} eqM in
    reduce-inject IHM
eval-sound ((M ⟨ H ?⟩) , ⊢⟨?⟩ ⊢M H) {suc k}{⊢t} eq
    with letB-term-inv{M = eval (M , ⊢M) k} eq
... | inj₂ (eqM , refl) = proj-blame (eval-sound (M , ⊢M) {k} eqM)
... | inj₁ ((val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) , eqM , eq)
    with letB-term-inv{M = project (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉))} eq
... | inj₂ (eqProj , refl) =
      let IHM = eval-sound (M , ⊢M) {k} eqM in
      let G≢H = project-blame-inv eqProj in
      project-collide IHM v G≢H
... | inj₁ (W , eqProj , eqW)
    with eval-sound (⊢v⇒⊢A W) {k = k} eqW
... | IHW 
    with project-value-inv eqProj
... | refl rewrite project-value-inv2 eqProj | value—↠ v IHW =
     project-collapse (eval-sound (M , ⊢M) {k} eqM) v refl
eval-sound (.blame , ⊢blame) {suc k}{⊢t} refl = _ END


{- todo: eval-complete -}
