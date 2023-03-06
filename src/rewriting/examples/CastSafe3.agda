{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafe3 where

open import Agda.Primitive using (lzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using (Vec) renaming ([] to []̌; _∷_ to _∷̌_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction using (RecStruct)
open import Induction.WellFounded as WF
open import Data.Product.Relation.Binary.Lex.Strict
  using (×-Lex; ×-wellFounded; ×-preorder)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Sig
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastLogRel3

1+m∸n : (m n : ℕ) → n ≤ m → suc m ∸ n ≡ suc (m ∸ n)
1+m∸n m .zero z≤n = refl
1+m∸n (suc m) (suc n) (s≤s n≤m) = 1+m∸n m n n≤m

{-# REWRITE sub-var #-}

compatibility-var : ∀ {Γ A x}
  → Γ ∋ x ⦂ A
    -----------
  → Γ ⊨ ` x ⦂ A
compatibility-var {Γ}{A}{x} ∋x k γ 𝓖Γγk =
  let Vγx = lemma-𝓖 Γ γ k 𝓖Γγk ∋x in
  Val⇒Exp {A}{⟪ γ ⟫ (` x)} k Vγx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} k γ 𝓖Γγk = Val⇒Exp k G
    where G : 𝓥⟦ $ₜ ′ℕ ⟧ ($ n) k
          G rewrite V-base{k}{′ℕ}{′ℕ}{n} = refl

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} k γ 𝓖Γγk = Val⇒Exp k G
    where G : 𝓥⟦ $ₜ ′𝔹 ⟧ ($ b) k
          G rewrite V-base{k}{′𝔹}{′𝔹}{b} = refl

-- E-app : ∀{A}{B}{L}{L′}{M}{M′}{n}
--    → 𝓔⟦ A ⇒ B ⟧ L (suc n)
--    → (L→L′ : L —↠ L′)
--    → len L→L′ ≤ n
--    → 𝓔⟦ A ⟧ M (suc n)
--    → (M→M′ : M —↠ M′)
--    → len M→M′ ≤ n
--    → ∃[ N ] (L′ · M′ —→ N)
-- E-app {A}{B}{L}{L′}{M}{M′}{n} EL L→L′ lt1 EM M→M′ lt2
--     with EL L′ L→L′ (s≤s lt1)
-- ... | inj₂ (inj₁ (L″ , L′→L″)) = (_ , ξ (□· _) L′→L″)
-- ... | inj₂ (inj₂ refl) = (_ , ξ-blame (□· _))
-- ... | inj₁ Vv′
--     with EM M′ M→M′ (s≤s lt2)
-- ... | inj₂ (inj₁ (M″ , M′→M″)) = (_ , ξ (𝓥⇒Value L′ Vv′ ·□) M′→M″)
-- ... | inj₂ (inj₂ beq) rewrite beq = (_ , ξ-blame (𝓥⇒Value L′ Vv′ ·□))
-- ... | inj₁ Vw
--     --rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
--     with (𝓥⇒Value L′ Vv′)
-- ... | $̬ c
--     rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
--     = ⊥-elim Vv′
-- ... | v 〈 g 〉
--     rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
--     = ⊥-elim Vv′
-- ... | ƛ̬ N = (_ , β (𝓥⇒Value M′ Vw))

lemma5 : ∀ x y z
   → x ≤ y + z + suc x ∸ (y + z)
lemma5 x y z =
  begin
  x                          ≤⟨ ≤-step ≤-refl ⟩
  suc x                      ≤⟨ m≤m+n _ _ ⟩
  (suc x) + 0                  ≤⟨ ≤-reflexive (cong (λ X → (suc x) + X) (sym (n∸n≡0 (y + z)))) ⟩
  (suc x) + ((y + z) ∸ (y + z))  ≤⟨ ≤-reflexive (sym (+-∸-assoc (suc x) {y + z}{y + z} ≤-refl)) ⟩
  ((suc x) + (y + z)) ∸ (y + z)  ≤⟨ ≤-reflexive (cong (λ X → X ∸ (y + z)) (+-comm (suc x) (y + z))) ⟩
  ((y + z) + (suc x) ) ∸ (y + z)  ≤⟨ ≤-refl ⟩
  (y + z) + suc x ∸ (y + z)
  ∎
  where
  open ≤-Reasoning

-- lemma6 : ∀ n x y w z
--    → (<k : x ≤ n)
--    → (eq : x ≡ y + w + z)
--    → suc w ≤ suc n
-- lemma6 n x y w z <k eq = (s≤s (≤-trans (≤-trans (≤-trans (m≤n+m w (y + z))
--          (≤-reflexive (trans (+-assoc y z w) (trans (cong (λ X → y + X) (+-comm z w))
--          (sym (+-assoc y w z)))))) (≤-reflexive (sym eq))) <k))

lemma7 : ∀ n w x y z 
   → (<k : w ≤ n)
   → (eq : w ≡ y + z + suc x)
   → suc x ≤ suc n ∸ (y + z)
lemma7 n w x y z <k eq = (≤-trans (s≤s (≤-trans (≤-trans (lemma5 (x) (y) (z))
             (≤-reflexive (cong (λ X → X ∸ (y + z)) (sym eq))))
             (∸-monoˡ-≤ (y + z) <k))) (≤-reflexive (sym (1+m∸n n (y + z)
             (≤-trans (≤-trans (m≤m+n (y + z) (suc (x))) (≤-reflexive (sym eq))) <k)))))

-- {-
-- x = len L·M→N
-- y = len L→V
-- z = len M→W
-- w = len VW→N
-- -}
-- lemma8 : ∀ k′ x y z w
--    → x ≡ y + z + w
--    → x ≤ k′
--    → suc (y) ≤ suc k′
-- lemma8 k′ x y z w eq lt =
--     (s≤s (≤-trans (≤-trans (≤-trans (m≤m+n (y) _)
--             (≤-reflexive (sym (+-assoc (y) _ _))))
--             (≤-reflexive (sym eq))) lt))


-- {-
--  x = suc k′
--  y = len L→V
--  z = len M→W
--  -}
lemma9 : ∀ x y z
   → x ∸ (y + z) ≤ x ∸ y
lemma9 x y z = (∸-monoʳ-≤ {y}{y + z} x (m≤m+n y z))

lemma10 : ∀ x y z
   → x ∸ (y + z) ≤ x ∸ z
lemma10 x y z = (∸-monoʳ-≤ {z}{y + z} x (m≤n+m _ _))

lemma11 : ∀ k′ L·M→N L→L′ L′M→N
   → L·M→N ≡ L→L′ + L′M→N
   → L·M→N ≤ k′
   → L→L′ < suc k′
lemma11 k′ L·M→N L→L′ L′M→N refl <k = s≤s (≤-trans (m≤m+n _ _) <k)

-- Safe×Value⇒𝓥 : ∀ {A N k}
--   → (𝓥⟦ A ⟧ N k  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame)
--   → Value N
--     -----------
--   → 𝓥⟦ A ⟧ N k
-- Safe×Value⇒𝓥 {A} {N} {k} (inj₁ Vv) v = Vv
-- Safe×Value⇒𝓥 {A} {N} {k} (inj₂ (inj₁ (N′ , N→N′))) v = ⊥-elim (value-irreducible v N→N′)
-- Safe×Value⇒𝓥 {A} {N} {k} (inj₂ (inj₂ refl)) v = ⊥-elim (blame-not-value v refl)

𝓥[A⇒B]⇒ƛN : ∀{A B V k}
  → 𝓥⟦ A ⇒ B ⟧ V k
    --------------
  → ∃[ N ] V ≡ ƛ N
𝓥[A⇒B]⇒ƛN {A}{B}{` x}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V
𝓥[A⇒B]⇒ƛN {A}{B}{$ c}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V
𝓥[A⇒B]⇒ƛN {A}{B}{L · M}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V
𝓥[A⇒B]⇒ƛN {A}{B}{ƛ N}{k} 𝓥V = N , refl
𝓥[A⇒B]⇒ƛN {A}{B}{M ⟨ g !⟩}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V
𝓥[A⇒B]⇒ƛN {A}{B}{M ⟨ h ?⟩}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V
𝓥[A⇒B]⇒ƛN {A}{B}{blame}{k} 𝓥V
    rewrite unfold-SafeVal (k , size (A ⇒ B)) = ⊥-elim 𝓥V

app-inv-left : ∀{L M N}
  → (r1 : L · M —↠ N)
  → irred N
    --------------------------
  → (∃[ L′ ] Σ[ r2 ∈ (L —↠ L′) ] irred L′
        × Σ[ r3 ∈ (L′ · M —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-left {L} {M} {.(L · M)} (.(L · M) END) irredN =
    inj₁ (L , (_ END) , IL , (_ END) , refl)
    where IL : irred L
          IL (L′ , L→L′) = ⊥-elim (irredN (_ , (ξ (□· M) L→L′)))
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ (□· M₁) r1 ⟩ r2) irredN
    with app-inv-left r2 irredN
... | inj₁ (L′ , L→L′ , IL′ , r3 , eq) =
      inj₁ (L′ , (L —→⟨ r1 ⟩ L→L′) , IL′ , r3 , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ (v ·□) r1 ⟩ r2) irredN =
    inj₁ (value v , (_ END) , value-irred v ,
          ((value v · M) —→⟨ ξ (v ·□) r1 ⟩ r2) , refl)
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ-blame (□· M₁) ⟩ r2) irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-left {L} {M} {N} (.(L · M) —→⟨ ξ-blame (v ·□) ⟩ r2) irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-left {.(ƛ _)} {M} {N} (.(ƛ _ · M) —→⟨ β v ⟩ r2) irredN =
    inj₁ (_ , (_ END) , value-irred (ƛ̬ _) , (_ —→⟨ β v ⟩ r2) , refl)

app-inv-right : ∀{V M N}
  → (r1 : V · M —↠ N)
  → Value V
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M —↠ M′) ] irred M′
       × Σ[ r3 ∈ (V · M′ —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
app-inv-right {V}{M}{N} (.(_ · _) END) v irredN =
    inj₁ (M , (_ END) , irredM , (_ END) , refl)
    where irredM : irred M
          irredM (M′ , M→M′) = irredN ((V · M′) , (ξ (v ·□) M→M′))
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ (□· M) r1 ⟩ r2) v irredN =
    ⊥-elim (value-irreducible v r1)
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ (v′ ·□) r1 ⟩ r2) v irredN
    with app-inv-right r2 v′ irredN
... | inj₁ (M′ , M→M′ , iM′ , →N , eq) =
      inj₁ (M′ , (M —→⟨ r1 ⟩ M→M′) , iM′ , →N , cong suc eq)
... | inj₂ refl = inj₂ refl
app-inv-right {.blame} {M} {N} (.(blame · M) —→⟨ ξ-blame (□· M) ⟩ r2) () irredN
app-inv-right {V} {M} {N} (.(V · M) —→⟨ ξ-blame (v₁ ·□) ⟩ r2) v irredN
    with blame—↠ r2
... | refl = inj₂ refl
app-inv-right {.(ƛ _)} {M} {N} (.(ƛ _ · M) —→⟨ β w ⟩ r2) v irredN =
    inj₁ (M , (_ END) , value-irred w , (_ —→⟨ β w ⟩ r2) , refl)

frame-inv : ∀{F M N}
  → (r1 : F ⟦ M ⟧ —↠ N)
  → irred N
  → (∃[ M′ ] Σ[ r2 ∈ (M —↠ M′) ] irred M′
        × Σ[ r3 ∈ (F ⟦ M′ ⟧ —↠ N) ] len r1 ≡ len r2 + len r3)
    ⊎ N ≡ blame
frame-inv {□· M} {L} {N} r1 irN = app-inv-left r1 irN 
frame-inv {v ·□} {M} {N} r1 irN = app-inv-right r1 v irN
frame-inv {□⟨ g !⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ g !⟩ M→M′))
frame-inv {□⟨ g !⟩} {M} {N} (.(□⟨ g !⟩ ⟦ M ⟧) —→⟨ ξ □⟨ g₁ !⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ g !⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ —→⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ g !⟩} {M} {N} (.(□⟨ g !⟩ ⟦ M ⟧) —→⟨ ξ-blame □⟨ g₁ !⟩ ⟩ r2) irN
    with blame—↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ h ?⟩} {M} (_ END) irN = inj₁ (_ , (_ END) , irM , (_ END) , refl)
    where irM : irred M
          irM (M′ , M→M′) = irN (_ , (ξ □⟨ h ?⟩ M→M′))
frame-inv {□⟨ h ?⟩} {M} {N} (.(□⟨ h ?⟩ ⟦ M ⟧) —→⟨ ξ □⟨ h₁ ?⟩ r1 ⟩ r2) irN
    with frame-inv{□⟨ h ?⟩} r2 irN
... | inj₁ (M′ , r3 , irM′ , r4 , eq) = inj₁ (_ , (_ —→⟨ r1 ⟩ r3) , irM′ , r4 , cong suc eq)
... | inj₂ refl = inj₂ refl
frame-inv {□⟨ h ?⟩} {M} {N} (.(□⟨ h ?⟩ ⟦ M ⟧) —→⟨ ξ-blame □⟨ h₁ ?⟩ ⟩ r2) irN
    with blame—↠ r2
... | refl = inj₂ refl
frame-inv {□⟨ h ?⟩} {M} {N} (.(□⟨ h ?⟩ ⟦ M ⟧) —→⟨ collapse v g .h refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 g 〉) , (_ —→⟨ collapse v g h refl ⟩ r2) , refl)
frame-inv {□⟨ h ?⟩} {M} {N} (.(□⟨ h ?⟩ ⟦ M ⟧) —→⟨ collide v g .h eq refl ⟩ r2) irN =
  inj₁ (M , (_ END) , value-irred (v 〈 g 〉) , (_ —→⟨ collide v g h eq refl ⟩ r2) , refl)

frame-blame : ∀{F}{M}{N}
   → M —↠ N
   → M ≡ F ⟦ blame ⟧
   → irred N
   → N ≡ blame
frame-blame {F} {N} (.N END) refl irN = ⊥-elim (irN (_ , (ξ-blame F)))
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ (□· M₁) refl x₁ r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ (() ·□) refl x₁ r ⟩ M→N) refl irN
frame-blame {□· M} {.((□· M) ⟦ blame ⟧)} (.((□· M) ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ (□· M) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (value-irreducible v r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ (v₁ ·□) refl refl r ⟩ M→N) refl irN =
    ⊥-elim (blame-irreducible r)
frame-blame {v ·□} {.((v ·□) ⟦ blame ⟧)} (.((v ·□) ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN 
    with blame—↠ M→N
... | refl = refl
frame-blame {□⟨ g !⟩} {.(□⟨ g !⟩ ⟦ blame ⟧)} (.(□⟨ g !⟩ ⟦ blame ⟧) —→⟨ ξξ □⟨ g₁ !⟩ refl refl r ⟩ M→N) refl irN =
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ g !⟩} {.(□⟨ g !⟩ ⟦ blame ⟧)} (.(□⟨ g !⟩ ⟦ blame ⟧) —→⟨ ξξ-blame F x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl
frame-blame {□⟨ h ?⟩} {.(□⟨ h ?⟩ ⟦ blame ⟧)} (.(□⟨ h ?⟩ ⟦ blame ⟧) —→⟨ ξξ □⟨ h₁ ?⟩ refl refl r ⟩ M→N) refl irN = 
  ⊥-elim (blame-irreducible r)
frame-blame {□⟨ h ?⟩} {.(□⟨ h ?⟩ ⟦ blame ⟧)} (.(□⟨ h ?⟩ ⟦ blame ⟧) —→⟨ ξξ-blame □⟨ h₁ ?⟩ x ⟩ M→N) refl irN
    with blame—↠ M→N
... | refl = refl

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M k γ 𝓖Γγk = Goal
    where
    𝓔L : 𝓔⟦ A ⇒ B ⟧ (⟪ γ ⟫ L ) k
    𝓔L = ⊨L k γ 𝓖Γγk

    𝓔M : 𝓔⟦ A ⟧ (⟪ γ ⟫ M ) k
    𝓔M = ⊨M k γ 𝓖Γγk
    
    Goal : 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M)) k
    Goal N L·M→N (s≤s {n = k′} <k) irN
        with frame-inv {□· ⟪ γ ⟫ M} L·M→N irN
        {---- Case:  N ≡ blame -----}
    ... | inj₂ refl = inj₂ refl
        {---- Case:  ⟪ γ ⟫ L —↠ L′  and  irred L′  and  L′ · ⟪ γ ⟫ M —↠ N  ---}
    ... | inj₁ (L′ , L→L′ , irL′ , L′M→N , eq)
        with 𝓔L L′ L→L′
                (lemma11 k′ (len L·M→N) (len L→L′) (len L′M→N) eq <k) irL′
        {---- Subcase:  L′ ≡ blame  -----}
    ... | inj₂ refl = inj₂ (frame-blame{□· _} L′M→N refl irN)
    Goal N L·M→N (s≤s {n = k′} <k) irN
        | inj₁ (L′ , L→L′ , irL′ , L′M→N , eq)
        {---- Subcase:  𝓥⟦ A ⇒ B ⟧ L′  -----}
        | inj₁ 𝓥L′
        with frame-inv{𝓥⇒Value L′ 𝓥L′ ·□} L′M→N irN
        {---- Subsubcase:  N ≡ blame -----}
    ... | inj₂ refl = inj₂ refl
        {---- Subsubcase:  ⟪ γ ⟫ M —↠ M′  and   L′ · M′ —↠ N   -----}
    ... | inj₁ (M′ , M→M′ , irM′ , L′M′→N , eq2)
        with 𝓔M M′ M→M′ (lemma11 k′ _ _ _ eq2
               (≤-trans (≤-trans (m≤n+m _ _) (≤-reflexive (sym eq))) <k)) irM′
    ... | inj₂ refl = inj₂ (frame-blame{𝓥⇒Value L′ 𝓥L′ ·□} L′M′→N refl irN)
        {---- Subcase:  𝓥⟦ A ⟧ M′  -----}
    ... | inj₁ 𝓥M′
        with 𝓥[A⇒B]⇒ƛN 𝓥L′
    ... | (N′ , refl)
        with L′M′→N
    ... | .(ƛ N′ · M′) END = ⊥-elim (irN (_ , (β (𝓥⇒Value M′ 𝓥M′))))
    ... | .(ƛ N′ · M′) —→⟨ ξξ (□· M) refl refl r1 ⟩ r2 =
            ⊥-elim (value-irreducible (ƛ̬ N′) r1)
    ... | .(ƛ N′ · M′) —→⟨ ξξ (v ·□) refl refl r1 ⟩ r2 =
            ⊥-elim (value-irreducible (𝓥⇒Value M′ 𝓥M′) r1)
    ... | .(ƛ N′ · M′) —→⟨ β w ⟩ N′[M′]→N = SafeN
        where
        SafeN : 𝓥⟦ B ⟧ N (suc k′ ∸ len L·M→N) ⊎ N ≡ blame
        SafeN
            with mono-𝓥{suc k′ ∸ (len L→L′ + len M→M′)}
                   (≤⇒≤′ (lemma9 (suc k′) (len L→L′) (len M→M′))) 𝓥L′
               | mono-𝓥{suc k′ ∸ (len L→L′ + len M→M′)}
                   (≤⇒≤′ (lemma10 (suc k′) (len L→L′) (len M→M′))) 𝓥M′
        ... | 𝓥λN′ | 𝓥W
            rewrite V-fun {suc k′ ∸ (len L→L′ + len M→M′)}{A}{B}{N′}
            with 𝓥λN′ M′ _ ≤-refl 𝓥W N N′[M′]→N
                      (lemma7 k′ (len L·M→N) (len N′[M′]→N) (len L→L′)
                             (len M→M′) <k (trans eq (trans
                                 (cong (λ X → len L→L′ + X) eq2)
                                 (sym (+-assoc (len L→L′) _ _))))) irN
        ... | inj₁ 𝓥N = inj₁ (mono-𝓥 (≤⇒≤′ LT) 𝓥N)
            where
            LT2 : k′ ∸ (len L→L′ + len M→M′ + len N′[M′]→N)
                  ≤ (suc k′ ∸ (len L→L′ + len M→M′)) ∸ len N′[M′]→N
            LT2 = ≤-trans (∸-monoˡ-≤ (len L→L′ + len M→M′ + len N′[M′]→N)
                             (≤-step ≤-refl))
                         (≤-reflexive (sym (∸-+-assoc (suc k′)
                                (len L→L′ + len M→M′) (len N′[M′]→N))))

            open Eq.≡-Reasoning
            EQ : k′ ∸ (len L→L′ + len M→M′ + len N′[M′]→N) ≡ suc k′ ∸ len L·M→N
            EQ =
              begin
                k′ ∸ (len L→L′ + len M→M′ + len N′[M′]→N)
              ≡⟨ refl ⟩
                suc k′ ∸ (suc ((len L→L′ + len M→M′) + (len N′[M′]→N)))
              ≡⟨ cong (λ X → suc k′ ∸ X) (sym (+-suc (len L→L′ + len M→M′)
                                                  (len N′[M′]→N))) ⟩
                suc k′ ∸ ((len L→L′ + len M→M′) + suc (len N′[M′]→N))
              ≡⟨ cong (λ X → suc k′ ∸ X) (sym ((trans eq (trans
                                 (cong (λ X → len L→L′ + X) eq2)
                                 (sym (+-assoc (len L→L′) _ _)))))) ⟩
                suc k′ ∸ len L·M→N
              ∎
            LT : suc k′ ∸ len L·M→N
                 ≤ suc k′ ∸ (len L→L′ + len M→M′) ∸ len N′[M′]→N
            LT = (≤-trans (≤-reflexive (sym EQ)) LT2)
            
        ... | inj₂ refl = inj₂ refl

    ... | .(ƛ N′ · M′) —→⟨ ξξ-blame (v ·□) refl ⟩ N′[M′]→N
        with frame-blame{F = ((ƛ̬ N′) ·□)} L′M′→N refl irN
    ... | refl = inj₂ refl        

compatible-fun : ∀{Γ}{A}{B}{N}
    → (A ∷ Γ) ⊨ N ⦂ B
    → Γ ⊨ ƛ N ⦂ (A ⇒ B)
compatible-fun {Γ}{A}{B}{N} ⊨N k γ 𝓖Γγk =
  Val⇒Exp {V = ⟪ γ ⟫ (ƛ N)} k (G k 𝓖Γγk)
  where
    G : ∀ k → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⇒ B ⟧ (ƛ (⟪ ext γ ⟫ N)) k
    G k 𝓖Γγk rewrite V-fun {k}{A}{B}{⟪ ext γ ⟫ N} = H
      where
      H : ∀ V (j : ℕ) → j ≤ k
        → 𝓥⟦ A ⟧ V j
        → 𝓔⟦ B ⟧ ((⟪ ext γ ⟫ N) [ V ]) j
      H V j lt Vvj = ⊨N j (V • γ) (mono-SafeEnv j k _ (≤⇒≤′ lt) 𝓖Γγk , Vvj)

-- compatible-inject : ∀{Γ}{G}{g : Ground G}{M}
--     → Γ ⊨ M ⦂ G
--     → Γ ⊨ M ⟨ g !⟩ ⦂ ★
-- compatible-inject{Γ}{G}{g}{M} ⊨M k γ 𝓖Γγk = H
--   where
--   H : ∀ N → (M→N : (⟪ γ ⟫ M ⟨ g !⟩) —↠ N) → (len M→N < k)
--              → (𝓥⟦ ★ ⟧ N (k ∸ len M→N))
--                ⊎ (∃[ N′ ] (N —→ N′))
--                ⊎ N ≡ blame               
--   H N red (s≤s {n = n} <k)
--       with inject-multi-inv red
--       {-
--         Case 1:  M ⟨ g !⟩ —↠ blame ≡ N
--        -}
--   ... | inj₂ (inj₂ refl) =         inj₂ (inj₂ refl)
--       {-
--         Case 2:  M ⟨ g !⟩ —↠ M′ ⟨ g !⟩ ≡ N
--        -}
--   ... | inj₁ (M′ , γM—↠M′ , refl , eqlen)
--       with (⊨M k γ 𝓖Γγk) M′ γM—↠M′ (s≤s (≤-trans (≤-reflexive eqlen) <k))
--   ... | inj₂ (inj₁ (M″ , M′→M″)) = inj₂ (inj₁ (_ , ξ □⟨ g !⟩ M′→M″))
--   ... | inj₂ (inj₂ refl) =         inj₂ (inj₁ (_ , ξ-blame □⟨ g !⟩))
--   ... | inj₁ Vv′ =                 inj₁ Goal
--       where
--         LT : n ∸ len red ≤ suc n ∸ len γM—↠M′
--         LT = ≤-trans (≤-reflexive (cong (λ X → n ∸ X) (sym eqlen) ))
--                      (≤-trans (n≤1+n _)
--                         (≤-reflexive (sym (1+m∸n n _ (subst (λ X → X ≤ n) (sym eqlen) <k))) ))
                        
--         Goal : 𝓥⟦ ★ ⟧ (M′ ⟨ g !⟩) (suc n ∸ len red)
--         Goal rewrite 1+m∸n n (len red) <k = V-intro (mono-𝓥 (≤⇒≤′ LT) Vv′)
            
--   H N red (s≤s {n = n} <k)
--       {-
--         Case 3:  M ⟨ g !⟩ —↠ V ⟨ g !⟩ —↠ N
--        -}
--       | inj₂ (inj₁ (V , M→V , v , →N , eq))
--       with (⊨M k γ 𝓖Γγk) V M→V (s≤s (≤-trans (subst (λ X → len M→V ≤ X) (sym eq) (m≤m+n _ _)) <k))
--   ... | inj₁ Vv′
--       with value—↠ (v 〈 g 〉) →N
--   ... | refl rewrite 1+m∸n n (len red) <k =      
--         inj₁ (V-intro (mono-𝓥 (≤⇒≤′ LT) Vv′))
--       where →V≤red : len M→V ≤ len red
--             →V≤red = ≤-trans (m≤m+n (len M→V) (len →N)) (≤-reflexive (sym eq))
--             LT′ : n ∸ len red ≤ n ∸ len M→V
--             LT′ = ∸-monoʳ-≤{len M→V}{len red} n →V≤red
--             LT : n ∸ len red ≤ suc n ∸ len M→V
--             LT = ≤-trans (≤-step LT′) (≤-reflexive (sym (1+m∸n n (len M→V) (≤-trans →V≤red <k))))
        
--   H N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq))
--       | inj₂ (inj₁ (V′ , →V′)) = ⊥-elim (value-irreducible v →V′)
--   H N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq))
--       | inj₂ (inj₂ refl)
--       with v
--   ... | ()

  
-- blame-project : ∀{M}{N}{H}{h : Ground H}
--    → M —↠ N
--    → M ≡ (blame ⟨ h ?⟩)
--    → N ≡ M ⊎ N ≡ blame
-- blame-project {M} {.M} (.M END) eq = inj₁ refl
-- blame-project {M} {N} (.M —→⟨ ξξ (□⟨ h ?⟩) refl refl r ⟩ →N′) refl rewrite blame—↠ (unit r) 
--     with blame-project →N′ refl
-- ... | inj₁ refl = inj₁ refl
-- ... | inj₂ refl = inj₂ refl
-- blame-project {M} {N} (.M —→⟨ ξξ-blame F x ⟩ →N) refl rewrite blame—↠ →N = inj₂ refl
-- blame-project {.(ƛ _ · _)} {N} (.(ƛ _ · _) —→⟨ β x ⟩ →N) ()
-- blame-project {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collapse x g h () ⟩ →N) refl
-- blame-project {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collide x g h x₁ x₂ ⟩ →N) eq rewrite blame—↠ →N = inj₂ refl
      
-- compatible-project : ∀{Γ}{H}{h : Ground H}{M}
--     → Γ ⊨ M ⦂ ★
--     → Γ ⊨ M ⟨ h ?⟩ ⦂ H
-- compatible-project {Γ}{H}{h}{M} ⊨M k γ 𝓖Γγk = aux
--   where
--   aux : ∀ N → (M→N : (⟪ γ ⟫ M ⟨ h ?⟩) —↠ N) → (len M→N < k)
--              → (𝓥⟦ H ⟧ N (k ∸ len M→N))
--                ⊎ (∃[ N′ ] (N —→ N′))
--                ⊎ N ≡ blame               
--   aux N red (s≤s {n = n} <k)
--       with project-multi-inv2 red
--   {- Case 1 -}    
--   ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
--   {- Case 2 -}      
--   ... | inj₁ (M′ , →M′ , refl , eq)
--       with (⊨M k γ 𝓖Γγk) M′ →M′ (s≤s (≤-trans (≤-reflexive eq) <k))
--   ... | inj₂ (inj₁ (M″ , M′→)) = inj₂ (inj₁ (_ , ξ □⟨ h ?⟩ M′→))
--   ... | inj₂ (inj₂ refl) = inj₂ (inj₁ (_ , ξ-blame □⟨ h ?⟩))
--   ... | inj₁ Vv′
--       rewrite 1+m∸n n (len →M′) (≤-trans (≤-reflexive eq) <k)
--       with V-dyn-inv2 M′ Vv′
--   ... | (V′ , G , g , refl , Vv″)
--       with g ≡ᵍ h
--   ... | yes refl = inj₂ (inj₁ (_ , collapse (𝓥⇒Value V′ Vv″) g h refl))
--   ... | no neq = inj₂ (inj₁ (_ , collide (𝓥⇒Value V′ Vv″) g h neq refl))
--   {- Case 3 -}        
--   aux N red (s≤s <k)
--       | inj₂ (inj₁ (V , →V , v , →N , eq))
--       with (⊨M k γ 𝓖Γγk) V →V (s≤s (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k))
--   ... | inj₂ (inj₁ (V′ , V→)) = ⊥-elim (value-irreducible v V→)
--   ... | inj₂ (inj₂ refl)
--       with blame-project →N refl
--   ... | inj₂ refl = inj₂ (inj₂ refl)
--   ... | inj₁ refl
--       with v
--   ... | ()
--   aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq))
--       | inj₁ Vv′
--       rewrite 1+m∸n n (len →V) (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k)
--       with V-dyn-inv2 V Vv′
--   ... | (V′ , G , g , refl , Vv″)
--       with →N
--   ... | _ END =
--       inj₂ (inj₁ (aux′ g h))
--       where aux′ : ∀{G}{H} (g : Ground G) (h : Ground H) → ∃[ L ] (((V′ ⟨ g !⟩) ⟨ h ?⟩) —→ L)
--             aux′ g h
--                 with g ≡ᵍ h
--             ... | yes refl = _ , (collapse (𝓥⇒Value V′ Vv″) g h refl)
--             ... | no neq = _ , (collide (𝓥⇒Value V′ Vv″) g h neq refl)
--   ... | _ —→⟨ ξξ (□⟨ _ ?⟩) refl x₁ r1 ⟩ r2 = ⊥-elim (value-irreducible v r1)
--   ... | _ —→⟨ ξξ-blame (□⟨ _ ?⟩) () ⟩ r2
--   ... | _ —→⟨ collide x g₁ .h x₁ refl ⟩ r2
--       with blame—↠ r2
--   ... | refl = inj₂ (inj₂ refl)
--   aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq))
--       | inj₁ Vv′
--       | (V′ , G , g , refl , Vv″)
--       | _ —→⟨ collapse _ g₁ .h refl ⟩ r2
--       with value—↠ (𝓥⇒Value V′ Vv″) r2
--   ... | refl =
--         inj₁ (mono-𝓥 (≤⇒≤′ LT) Vv″)
--       where LT : suc n ∸ len red ≤ n ∸ len →V
--             LT = ≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) eq))
--                 (≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) (+-suc (len →V) (len r2))))
--                 (∸-monoʳ-≤{len →V}{len →V + len r2} n (m≤m+n (len →V) (len r2)) ))

-- compatible-blame : ∀{Γ}{A}
--    → Γ ⊨ blame ⦂ A
-- compatible-blame{Γ}{A} k γ 𝓖Γγk = Goal
--   where
--   Goal : 𝓔⟦ A ⟧ blame k
--   Goal N M→N <k
--       with blame—↠ M→N
--   ... | refl = inj₂ (inj₂ refl)

-- fundamental : ∀ {Γ A} → (M : Term)
--   → Γ ⊢ M ⦂ A
--     ----------
--   → Γ ⊨ M ⦂ A
-- fundamental {Γ} {A} .(` _) (⊢` ∋x) = compatibility-var ∋x
-- fundamental {Γ} {.($ₜ ′ℕ)} .($ _) (⊢$ ′ℕ) = compatible-nat
-- fundamental {Γ} {.($ₜ ′𝔹)} .($ _) (⊢$ ′𝔹) = compatible-bool
-- fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) = compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
-- fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) = compatible-fun {N = N} (fundamental N ⊢N)
-- fundamental {Γ} {.★} (M ⟨ g !⟩) (⊢⟨!⟩ ⊢M g) = compatible-inject {M = M} (fundamental M ⊢M)
-- fundamental {Γ} {A} (M ⟨ h ?⟩) (⊢⟨?⟩ ⊢M h) = compatible-project {M = M} (fundamental M ⊢M)
-- fundamental {Γ} {A} .blame ⊢blame = compatible-blame

-- type-safety : ∀ {A} → (M N : Term)
--   → [] ⊢ M ⦂ A
--   → M —↠ N
--   → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
-- type-safety M N ⊢M M→N
--     with fundamental M ⊢M (suc (len M→N)) id tt N M→N ≤-refl
-- ... | inj₁ VN = inj₁ (𝓥⇒Value _ VN)    
-- ... | inj₂ (inj₁ red) = inj₂ (inj₁ red)    
-- ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
