{-# OPTIONS --rewriting #-}
module rewriting.examples.CastEval where

open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe
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

data Halt : Set where
  `_ : Term → Halt
  hblame : Halt

data Result : Set where
  halt : Halt → Result
  timeout : Result

trm : Halt → Term
trm (` M) = M
trm hblame = blame

letM : ∀{T U : Set} → Maybe T → (T → Maybe U) → Maybe U
letM (just t) f = f t
letM nothing f = nothing

letM-syntax = letM
infix 1 letM-syntax
syntax letM-syntax M (λ x → N) = letᵐ x := M ; N

letB : Maybe Result → (Term → Maybe Result) → Maybe Result
letB R f = letM R g
  where
  g : Result → Maybe Result
  g (halt (` V)) = f V
  g (halt hblame) = just (halt hblame)
  g timeout = just timeout
  
letB-syntax = letB
infix 1 letB-syntax
syntax letB-syntax M (λ x → N) = letᵇ x := M ; N

return : Term → Maybe Result
return V = just (halt (` V))

blame! :  Maybe Result
blame! = just (halt hblame)

_⊙_ : Term → Term → Maybe Term
(ƛ N) ⊙ W = just (N [ W ])
L ⊙ M = nothing

project : Ground → Term → Maybe Result
project H (V ⟨ G !⟩)
    with G ≡ᵍ H
... | yes refl = return V
... | no neq = blame!
project H M = nothing

eval : Term → ℕ → Maybe Result
eval M zero = just timeout
eval (` x) (suc k) = nothing
eval ($ c) (suc k) = return ($ c)
eval (ƛ N) (suc k) = return (ƛ N)
eval (L · M) (suc k) =
    letᵇ V := eval L k ; letᵇ W := eval M k ;
    letᵐ N := (V ⊙ W) ; eval N k
eval (M ⟨ G !⟩) (suc k) =
    letᵇ V := eval M k ; return (V ⟨ G !⟩)
eval (M ⟨ H ?⟩) (suc k) =
    letᵇ V := eval M k ; project H V
eval blame (suc k) = blame!

infixr 6 _⇓_
_⇓_ : Term → Term → Set
M ⇓ V = ∃[ k ] eval M  k ≡ return V

_⇓ᵇ : Term → Set
M ⇓ᵇ = ∃[ k ] eval M k ≡ blame!

_⇑ : Term → Set
M ⇑ = ∀ k → eval M k ≡ just timeout

letM-just-inv : ∀{T U : Set} (M : Maybe T){f : T → Maybe U}{t : U}
   → letM M f ≡ just t
   → (∃[ m ] (M ≡ just m) × (f m ≡ just t))
letM-just-inv (just m) {f} {t} letJust rewrite letJust = m , refl , letJust

letB-halt-inv : ∀ (M : Maybe Result){f : Term → Maybe Result}{t : Halt}
   → letB M f ≡ just (halt t)
   → (∃[ v ] (M ≡ return v) × (f v ≡ just (halt t)))
     ⊎ (M ≡ blame! × t ≡ hblame)
letB-halt-inv (just (halt (` V))) {f} {t} eq =
    inj₁ (V , refl , eq)
letB-halt-inv (just (halt hblame)) {f} {t} refl = inj₂ (refl , refl)

eval-mono : ∀{M}{k}{t} → (eval M k ≡ just (halt t)) → ∀{k′} → k ≤ k′
   → eval M k′ ≡ just (halt t)
eval-mono {` x} {suc k} {t} () {suc k′} (s≤s k≤k′)
eval-mono {$ c} {suc k} {t} refl {suc k′} (s≤s k≤k′) = refl
eval-mono {ƛ N} {suc k} {t} refl {suc k′} (s≤s k≤k′) = refl
eval-mono {L · M} {suc k} {t} eqM {suc k′} (s≤s k≤k′)
    with letB-halt-inv (eval L k) eqM
... | inj₂ (eqL , refl) rewrite eval-mono eqL k≤k′ = refl
... | inj₁ (V , eqL , eqLet1)
    with letB-halt-inv (eval M k) eqLet1
... | inj₂ (eqM , refl) rewrite eval-mono eqL k≤k′ | eval-mono eqM k≤k′ = refl
... | inj₁ (W , eqM , eqLet2) rewrite eval-mono eqL k≤k′ | eval-mono eqM k≤k′
    with letM-just-inv (V ⊙ W) eqLet2
... | m , eqVW , eqN rewrite eqVW =    
      eval-mono eqN k≤k′
eval-mono {M ⟨ G !⟩} {suc k} {t} eqM {suc k′} (s≤s k≤k′)
    with letB-halt-inv (eval M k) eqM
... | inj₂ (eqM , refl) rewrite eval-mono eqM k≤k′ = refl
... | inj₁ (V , eqM , eqInj) rewrite eval-mono eqM k≤k′ = eqInj
eval-mono {M ⟨ H ?⟩} {suc k} {t} eqM {suc k′} (s≤s k≤k′)
    with letB-halt-inv (eval M k) eqM 
... | inj₂ (eqM , refl) rewrite eval-mono eqM k≤k′ = refl
... | inj₁ (V , eqM , eqLet) rewrite eval-mono eqM k≤k′ = eqLet
eval-mono {blame} {suc k} {t} eqM {suc k′} (s≤s k≤k′) = eqM

project-value : ∀ V H W → Value V → project H V ≡ just (halt (` W)) → Value W
project-value .(_ ⟨ G !⟩) H W (v 〈 G 〉) eq
    with G ≡ᵍ H | eq
... | yes refl | refl = v
... | no neq | ()

eval-to-value : ∀ M V k → eval M k ≡ return V → Value V
eval-to-value (M) V zero ()
eval-to-value (` x) V (suc k) ()
eval-to-value ($ c) V (suc k) refl = $̬ c
eval-to-value (ƛ N) V (suc k) refl = ƛ̬ N
eval-to-value (L · M) V (suc k) evalMk=V
    with letB-halt-inv (eval L k) evalMk=V
... | inj₂ (eqL , ())
... | inj₁ (V′ , eqL , eqLet)
    with letM-just-inv (eval M k) eqLet
... | halt (` W) , eqM , eqLet2
    with letM-just-inv (V′ ⊙ W) eqLet2
... | N , VW=N , eqN = eval-to-value N V k eqN
eval-to-value (M ⟨ G !⟩) V (suc k) evalMk=V
    with letB-halt-inv (eval M k) evalMk=V
... | inj₂ (eqM , ())
... | inj₁ (V′ , eqM , refl) rewrite eqM =
    let v′ = eval-to-value M V′ k eqM in
    v′ 〈 G 〉
eval-to-value (M ⟨ H ?⟩) V (suc k) evalMk=V
    with letB-halt-inv (eval M k) evalMk=V
... | inj₂ (eqM , ())
... | inj₁ (V′ , eqM , eqProj) =
    project-value V′ H V (eval-to-value M V′ k eqM) eqProj 
eval-to-value blame V (suc k) ()

eval-value : ∀ V → Value V → ∃[ k ] eval V k ≡ return V
eval-value .(ƛ N) (ƛ̬ N) = 1 , refl
eval-value .($ c) ($̬ c) = 1 , refl
eval-value (V ⟨ G !⟩) (v 〈 G 〉)
    with eval-value V v
... | k , evV = (suc k) , Goal v evV
    where
    Goal : ∀{V}
       → Value V
       → eval V k ≡ just (halt (` V))
       → (letᵇ V′ := eval V k ; return (V′ ⟨ G !⟩))
             ≡ return (V ⟨ G !⟩)
    Goal {V} v evV rewrite evV = refl

⇓-value : ∀ V → Value V → V ⇓ V
⇓-value V v = eval-value V v

⇓-determ : ∀{M}{V}{V′}
  → M ⇓ V
  → M ⇓ V′
    ------
  → V ≡ V′ 
⇓-determ {M}{V}{V′} (k , evalMk=V) (k′ , evalMk′=V′)
    with k ≤? k′
... | yes k≤k′ =
      let evalMk′=V = eval-mono evalMk=V k≤k′ in
      Goal (trans (sym evalMk′=V) evalMk′=V′)
      where
      Goal : just (halt (` V)) ≡ just (halt (` V′)) → V ≡ V′
      Goal refl = refl
... | no nlt =
      let k′≤k = ≰⇒≥ nlt in
      let evalMk=V′ = eval-mono evalMk′=V′ k′≤k in
      Goal (trans (sym evalMk=V) evalMk=V′)
      where
      Goal : just (halt (` V)) ≡ just (halt (` V′)) → V ≡ V′
      Goal refl = refl

⇓-value-eq : ∀{V W} → Value V → V ⇓ W → W ≡ V
⇓-value-eq {V}{W} v V⇓W = ⇓-determ V⇓W (⇓-value V v)

eval-blame-not-value : ∀ M k → eval M k ≡ blame! → Value M → ⊥
eval-blame-not-value .(ƛ N) zero () (ƛ̬ N)
eval-blame-not-value .(ƛ N) (suc k) () (ƛ̬ N)
eval-blame-not-value .($ c) zero () ($̬ c)
eval-blame-not-value .($ c) (suc k) () ($̬ c)
eval-blame-not-value (V ⟨ G !⟩) (suc (suc k)) eq (v 〈 G 〉)
    with letB-halt-inv (eval V (suc k)) eq
... | inj₁ (v′ , eqV , ())
... | inj₂ (eqM , eqB) = eval-blame-not-value V (suc k) eqM v

⇓ᵇ-not-value : ∀{M} → M ⇓ᵇ → Value M → ⊥
⇓ᵇ-not-value {M} (k , evM=b) v = eval-blame-not-value M k evM=b v

values-dont-diverge : ∀{V} → Value V → V ⇑ → ⊥
values-dont-diverge {V} v V⇑
    with eval-value V v
... | k , eq
    with trans (sym (V⇑ k)) eq
... | ()    

⇓ᵇ-blame : blame ⇓ᵇ
⇓ᵇ-blame = 1 , refl

blame-eval-not-value : ∀{V} → blame ⇓ V → ⊥
blame-eval-not-value {V} (zero , ())
blame-eval-not-value {V} (suc k , ())

blame-doesnt-diverge : blame ⇑ → ⊥
blame-doesnt-diverge b⇑
    with b⇑ 1
... | ()   



-- Termue-` : ∀{Γ}{A} (V : Γ ⊢v A)
--    → Termue (trm (` V))
-- Termue-` (val V ⊢V v) = v

-- eval-app-inv : ∀{A}{B}{V : [] ⊢v (A ⇒ B)}{W : [] ⊢v A}{k}{⊢t}
--    → eval (V ⊙ W) k ≡ halt ⊢t
--    → ∃[ N ] ∃[ ⊢N ] V ≡ val (ƛ N) (⊢ƛ ⊢N) (ƛ̬ N)
--        × eval (N [ ⊢v⇒trm W ] , wt-subst (⊢v⇒wt W) ⊢N) k ≡ halt ⊢t
-- eval-app-inv {A}{B}{val (ƛ N) (⊢ƛ ⊢N) (ƛ̬ N)}{val W ⊢W w}{k}{⊢t} evalV·W =
--   N , (⊢N , (refl , evalV·W))

-- project-blame-inv : ∀{Γ}{V}{G}{H}{⊢V}{v}
--    → project{Γ}{H} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ halt hblame
--    → G ≢ H
-- project-blame-inv{G = G}{H} eqProj
--     with G ≡ᵍ H
-- ... | no neq = λ G=H → neq G=H
-- ... | yes refl
--     with eqProj
-- ... | ()

-- project-value-inv : ∀{Γ}{V}{G}{H}{⊢V}{v}{W}
--    → project{Γ}{H} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ halt (` W)
--    → G ≡ H
-- project-value-inv{G = G}{H} eqProj
--     with G ≡ᵍ H
-- ... | yes refl = refl
-- ... | no neq
--     with eqProj
-- ... | ()

-- project-value-inv2 : ∀{Γ}{V}{G}{⊢V}{v}{W}
--    → project{Γ}{G} (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) ≡ halt (` W)
--    → W ≡ (val V ⊢V v)
-- project-value-inv2{G = G}{W = val W ⊢W w} eqProj 
--     with G ≡ᵍ G
-- ... | no neq
--     with eqProj
-- ... | ()
-- project-value-inv2{G = G}{W = val W ⊢W w} eqProj  | yes refl
--     with eqProj
-- ... | refl = refl    

-- eval-sound : ∀{A} → (M : [] ⊢ A) → ∀{k}{⊢t} → eval M k ≡ halt ⊢t
--    → proj₁ M —↠ trm ⊢t
-- eval-sound (M , ⊢M) {0}{⊢t} ()
-- eval-sound (($ c) , ⊢$ c) {suc k}{` (val ($ c′) _ _)} refl = _ END
-- eval-sound ((L · M) , ⊢· ⊢L ⊢M) {suc k}{⊢t} eq
--     with letB-halt-inv{M = eval (L , ⊢L) k} eq
-- ... | inj₂ (eqL , refl) = app-blame-L (eval-sound (L , ⊢L) {k} eqL)
-- ... | inj₁ (V , eqL , eqLet) rewrite eqL
--     with letB-halt-inv{M = eval (M , ⊢M) k} eqLet
-- ... | inj₂ (eqM , refl) rewrite eqM =
--       let IHL = eval-sound (L , ⊢L) {k} eqL in
--       let IHM = eval-sound (M , ⊢M) {k} eqM in
--       app-blame-R IHL (Termue-` V) IHM
-- ... | inj₁ (W , eqM , eqLet2) rewrite eqM
--     with eval-app-inv{V = V}{W}{k} eq
-- ... | N , ⊢N , refl , evalN[W] =     
--       let IHL = eval-sound (L , ⊢L) {k} eqL in
--       let IHM = eval-sound (M , ⊢M) {k} eqM in
--       let IHNW = eval-sound (N [ ⊢v⇒trm W ] , wt-subst (⊢v⇒wt W) ⊢N) {k}
--                      evalN[W] in
--       app-beta IHL IHM (Termue-⊢v⇒trm W) IHNW
-- eval-sound ((ƛ N) , ⊢ƛ ⊢M) {suc k}{⊢t} refl = _ END
-- eval-sound ((M ⟨ G !⟩) , ⊢⟨!⟩ ⊢M) {suc k}{⊢t} eq
--     with letB-halt-inv{M = eval (M , ⊢M) k} eq
-- ... | inj₂ (eqM , refl) = inj-blame (eval-sound (M , ⊢M) {k} eqM)
-- ... | inj₁ ((val V ⊢V v) , eqM , refl) =
--     let IHM = eval-sound (M , ⊢M) {k} eqM in
--     reduce-inject IHM
-- eval-sound ((M ⟨ H ?⟩) , ⊢⟨?⟩ ⊢M H) {suc k}{⊢t} eq
--     with letB-halt-inv{M = eval (M , ⊢M) k} eq
-- ... | inj₂ (eqM , refl) = proj-blame (eval-sound (M , ⊢M) {k} eqM)
-- ... | inj₁ ((val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉)) , eqM , eq)
--     with letB-halt-inv{M = project (val (V ⟨ G !⟩) (⊢⟨!⟩ ⊢V) (v 〈 G 〉))} eq
-- ... | inj₂ (eqProj , refl) =
--       let IHM = eval-sound (M , ⊢M) {k} eqM in
--       let G≢H = project-blame-inv eqProj in
--       project-collide IHM v G≢H
-- ... | inj₁ (W , eqProj , eqW)
--     with eval-sound (⊢v⇒⊢A W) {k = k} eqW
-- ... | IHW 
--     with project-value-inv eqProj
-- ... | refl rewrite project-value-inv2 eqProj | value—↠ v IHW =
--      project-collapse (eval-sound (M , ⊢M) {k} eqM) v refl
-- eval-sound (.blame , ⊢blame) {suc k}{⊢t} refl = _ END

-- {- todo: eval-complete -}

