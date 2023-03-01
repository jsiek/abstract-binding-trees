{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafe2 where

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
open import rewriting.examples.CastLogRel2

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

E-app : ∀{A}{B}{L}{L′}{M}{M′}{n}
   → 𝓔⟦ A ⇒ B ⟧ L (suc n)
   → (L→L′ : L —↠ L′)
   → len L→L′ ≤ n
   → 𝓔⟦ A ⟧ M (suc n)
   → (M→M′ : M —↠ M′)
   → len M→M′ ≤ n
   → ∃[ N ] (L′ · M′ —→ N)
E-app {A}{B}{L}{L′}{M}{M′}{n} EL L→L′ lt1 EM M→M′ lt2
    with EL L′ L→L′ (s≤s lt1)
... | inj₂ (inj₁ (L″ , L′→L″)) = (_ , ξ (□· _) L′→L″)
... | inj₂ (inj₂ refl) = (_ , ξ-blame (□· _))
... | inj₁ Vv′
    with EM M′ M→M′ (s≤s lt2)
... | inj₂ (inj₁ (M″ , M′→M″)) = (_ , ξ (𝓥⇒Value L′ Vv′ ·□) M′→M″)
... | inj₂ (inj₂ beq) rewrite beq = (_ , ξ-blame (𝓥⇒Value L′ Vv′ ·□))
... | inj₁ Vw
    --rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
    with (𝓥⇒Value L′ Vv′)
... | $̬ c
    rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
    = ⊥-elim Vv′
... | v 〈 g 〉
    rewrite unfold-SafeVal (suc n ∸ len L→L′ , suc (size A ⊔ size B))
    = ⊥-elim Vv′
... | ƛ̬ N = (_ , β (𝓥⇒Value M′ Vw))

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

lemma6 : ∀ n x y w z
   → (<k : x ≤ n)
   → (eq : x ≡ y + w + z)
   → suc w ≤ suc n
lemma6 n x y w z <k eq = (s≤s (≤-trans (≤-trans (≤-trans (m≤n+m w (y + z))
         (≤-reflexive (trans (+-assoc y z w) (trans (cong (λ X → y + X) (+-comm z w))
         (sym (+-assoc y w z)))))) (≤-reflexive (sym eq))) <k))

lemma7 : ∀ n w x y z 
   → (<k : w ≤ n)
   → (eq : w ≡ y + z + suc x)
   → suc x ≤ suc n ∸ (y + z)
lemma7 n w x y z <k eq = (≤-trans (s≤s (≤-trans (≤-trans (lemma5 (x) (y) (z))
             (≤-reflexive (cong (λ X → X ∸ (y + z)) (sym eq))))
             (∸-monoˡ-≤ (y + z) <k))) (≤-reflexive (sym (1+m∸n n (y + z)
             (≤-trans (≤-trans (m≤m+n (y + z) (suc (x))) (≤-reflexive (sym eq))) <k)))))

{-
x = len L·M→N
y = len L→V
z = len M→W
w = len VW→N
-}
lemma8 : ∀ k′ x y z w
   → x ≡ y + z + w
   → x ≤ k′
   → suc (y) ≤ suc k′
lemma8 k′ x y z w eq lt =
    (s≤s (≤-trans (≤-trans (≤-trans (m≤m+n (y) _)
            (≤-reflexive (sym (+-assoc (y) _ _))))
            (≤-reflexive (sym eq))) lt))


{-
 x = suc k′
 y = len L→V
 z = len M→W
 -}
lemma9 : ∀ x y z
   → x ∸ (y + z) ≤ x ∸ y
lemma9 x y z = (∸-monoʳ-≤ {y}{y + z} x (m≤m+n y z))

lemma10 : ∀ x y z
   → x ∸ (y + z) ≤ x ∸ z
lemma10 x y z = (∸-monoʳ-≤ {z}{y + z} x (m≤n+m _ _))

Safe×Value⇒𝓥 : ∀ {A N k}
  → (𝓥⟦ A ⟧ N k  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame)
  → Value N
    -----------
  → 𝓥⟦ A ⟧ N k
Safe×Value⇒𝓥 {A} {N} {k} (inj₁ Vv) v = Vv
Safe×Value⇒𝓥 {A} {N} {k} (inj₂ (inj₁ (N′ , N→N′))) v = ⊥-elim (value-irreducible v N→N′)
Safe×Value⇒𝓥 {A} {N} {k} (inj₂ (inj₂ refl)) v = ⊥-elim (blame-not-value v refl)

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

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M k γ 𝓖Γγk = Goal
    where
    Goal : 𝓔⟦ B ⟧ (⟪ γ ⟫ (L · M)) k
    Goal N L·M→N (s≤s {n = k′} <k)
        with app-multi-inv L·M→N
        {-
           Case 1:    L · M —↠ L′ · M
         -}
    ... | inj₁ (L′ , L→L′ , refl , len[L·M→N]≡len[L→L′])
        with ⊨L k γ 𝓖Γγk | ⊨M k γ 𝓖Γγk
    ... | EL | EM = inj₂ (inj₁ (E-app EL L→L′ LT EM (_ END) z≤n))
        where LT : len L→L′ ≤ k′
              LT = (≤-trans (≤-reflexive (sym len[L·M→N]≡len[L→L′])) <k)
        {-
           Case 2:    L · M —↠ V · M′
         -}
    Goal N L·M→N (s≤s {n = k′} len[L·M→N]≤k′)
        | inj₂ (inj₁ (V , M′ , L→V , v′ , M→M′ , refl , len[L·M→N]≡len[L→V]+len[M→M′])) =
          inj₂ (inj₁ (E-app (⊨L k γ 𝓖Γγk) L→V LT1 (⊨M k γ 𝓖Γγk) M→M′ LT2))
        where LT1 : len L→V ≤ k′
              LT1 = (≤-trans (≤-trans (m≤m+n (len L→V) (len M→M′))
                                      (≤-reflexive (sym len[L·M→N]≡len[L→V]+len[M→M′]))) len[L·M→N]≤k′)
              LT2 : len M→M′ ≤ k′
              LT2 = (≤-trans (≤-trans (m≤n+m (len M→M′) (len L→V))
                                      (≤-reflexive (sym len[L·M→N]≡len[L→V]+len[M→M′]))) len[L·M→N]≤k′)
        {-
           Case 3:    L · M —↠ blame
         -}
    Goal N L·M→N (s≤s len[L·M→N]≤k′)
        | inj₂ (inj₂ (inj₂ refl)) = inj₂ (inj₂ refl)
        {-
           Case 4:    L · M —↠ V · W —↠ N
         -}
    Goal N L·M→N (s≤s {n = k′} len[L·M→N]≤k′)
        | inj₂ (inj₂ (inj₁ (V , W , L→V , v′ , M→W , w , VW→N , len[L·M→N]≡len[L→V]+len[M→W]+len[VW→N])))
        with Safe×Value⇒𝓥 (⊨L k γ 𝓖Γγk V L→V (lemma8 k′ (len L·M→N) (len L→V) (len M→W) (len VW→N)
                                                 len[L·M→N]≡len[L→V]+len[M→W]+len[VW→N] len[L·M→N]≤k′)) v′
           | Safe×Value⇒𝓥 (⊨M k γ 𝓖Γγk W M→W (lemma6 k′ (len L·M→N) (len L→V) (len M→W) (len VW→N)
                                                 len[L·M→N]≤k′ len[L·M→N]≡len[L→V]+len[M→W]+len[VW→N])) w
    ... | 𝓥V | Vw′
        with 𝓥[A⇒B]⇒ƛN 𝓥V
    ... | (N′ , refl)
        with VW→N
    ... | _ END = inj₂ (inj₁ (_ , β w))
    ... | _ —→⟨ ξ (_ ·□) r₁ ⟩ r₂ =                          ⊥-elim (value-irreducible w r₁)
    ... | _ —→⟨ ξ (□· _) r₁ ⟩ r₂ =                          ⊥-elim (value-irreducible v′ r₁)
    ... | _ —→⟨ ξ-blame (_ ·□) ⟩ r₂ =                       ⊥-elim (blame-not-value w refl)
    ... | _ —→⟨ β w″ ⟩ N[W]—↠N
        {-
          Subcase: (ƛ N′) · W —→ N′ [ W ] —↠ N
        -}
        with mono-𝓥 (≤⇒≤′ (lemma9 (suc k′) (len L→V) (len M→W))) 𝓥V
           | mono-𝓥 (≤⇒≤′ (lemma10 (suc k′) (len L→V) (len M→W))) Vw′ 
    ... | Vv″ | Vw″ rewrite V-fun {suc k′ ∸ (len L→V + len M→W)}{A}{B}{N′} 
        with Vv″ W _ ≤-refl Vw″ N N[W]—↠N (lemma7 k′ (len L·M→N) (len N[W]—↠N) (len L→V) (len M→W)
                                             len[L·M→N]≤k′ len[L·M→N]≡len[L→V]+len[M→W]+len[VW→N])
    ... | inj₁ VN =
          inj₁ (mono-𝓥 (≤⇒≤′ (≤-trans (≤-reflexive (sym EQ)) LT2)) VN)
        where
          LT2 : k′ ∸ (len L→V + len M→W + len N[W]—↠N) ≤ (suc k′ ∸ (len L→V + len M→W)) ∸ len N[W]—↠N
          LT2 = ≤-trans (∸-monoˡ-≤ (len L→V + len M→W + len N[W]—↠N) (≤-step ≤-refl))
                       (≤-reflexive (sym (∸-+-assoc (suc k′) (len L→V + len M→W) (len N[W]—↠N))))

          open Eq.≡-Reasoning
          EQ : k′ ∸ (len L→V + len M→W + len N[W]—↠N) ≡ suc k′ ∸ len L·M→N
          EQ =
            begin
              k′ ∸ (len L→V + len M→W + len N[W]—↠N)
            ≡⟨ refl ⟩
              suc k′ ∸ (suc ((len L→V + len M→W) + (len N[W]—↠N)))
            ≡⟨ cong (λ X → suc k′ ∸ X) (sym (+-suc (len L→V + len M→W) (len N[W]—↠N))) ⟩
              suc k′ ∸ ((len L→V + len M→W) + suc (len N[W]—↠N))
            ≡⟨ cong (λ X → suc k′ ∸ X) (sym len[L·M→N]≡len[L→V]+len[M→W]+len[VW→N]) ⟩
              suc k′ ∸ len L·M→N
            ∎
    ... | inj₂ (inj₁ (N″ , N→)) = inj₂ (inj₁ (N″ , N→))
    ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)


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

compatible-inject : ∀{Γ}{G}{g : Ground G}{M}
    → Γ ⊨ M ⦂ G
    → Γ ⊨ M ⟨ g !⟩ ⦂ ★
compatible-inject{Γ}{G}{g}{M} ⊨M k γ 𝓖Γγk = H
  where
  H : ∀ N → (M→N : (⟪ γ ⟫ M ⟨ g !⟩) —↠ N) → (len M→N < k)
             → (𝓥⟦ ★ ⟧ N (k ∸ len M→N))
               ⊎ (∃[ N′ ] (N —→ N′))
               ⊎ N ≡ blame               
  H N red (s≤s {n = n} <k)
      with inject-multi-inv red
  ... | inj₂ (inj₂ refl) =         inj₂ (inj₂ refl)
  ... | inj₁ (M′ , γM—↠M′ , refl , eqlen)
      with ⊨M k γ 𝓖Γγk
  ... | EM 
      with EM M′ γM—↠M′ (s≤s (≤-trans (≤-reflexive eqlen) <k))
  ... | inj₂ (inj₁ (M″ , M′→M″)) = inj₂ (inj₁ (_ , ξ □⟨ g !⟩ M′→M″))
  ... | inj₂ (inj₂ refl) =         inj₂ (inj₁ (_ , ξ-blame □⟨ g !⟩))
  ... | inj₁ Vv′ =                 inj₁ Goal
      where
        LT : n ∸ len red ≤ suc n ∸ len γM—↠M′
        LT = ≤-trans (≤-reflexive (cong (λ X → n ∸ X) (sym eqlen) ))
                     (≤-trans (n≤1+n _)
                        (≤-reflexive (sym (1+m∸n n _ (subst (λ X → X ≤ n) (sym eqlen) <k))) ))
                        
        Goal : 𝓥⟦ ★ ⟧ (M′ ⟨ g !⟩) (suc n ∸ len red)
        Goal rewrite 1+m∸n n (len red) <k = V-intro (mono-𝓥 (≤⇒≤′ LT) Vv′)
            
  H N red (s≤s {n = n} <k)
      | inj₂ (inj₁ (V , →V , v , →N , eq))
      with ⊨M k γ 𝓖Γγk
  ... | EM
      with EM V →V (s≤s (≤-trans (subst (λ X → len →V ≤ X) (sym eq) (m≤m+n _ _)) <k))
  ... | inj₁ Vv′
      with value—↠ (v 〈 g 〉) →N
  ... | refl rewrite 1+m∸n n (len red) <k =      
        inj₁ (V-intro (mono-𝓥 (≤⇒≤′ LT) Vv′))
      where →V≤red : len →V ≤ len red
            →V≤red = ≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))
            LT′ : n ∸ len red ≤ n ∸ len →V
            LT′ = ∸-monoʳ-≤{len →V}{len red} n →V≤red
            LT : n ∸ len red ≤ suc n ∸ len →V
            LT = ≤-trans (≤-step LT′) (≤-reflexive (sym (1+m∸n n (len →V) (≤-trans →V≤red <k))))
        
  H N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM
      | inj₂ (inj₁ (V′ , →V′)) = ⊥-elim (value-irreducible v →V′)
  H N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM      
      | inj₂ (inj₂ refl)
      with v
  ... | ()

  
blame-project : ∀{M}{N}{H}{h : Ground H}
   → M —↠ N
   → M ≡ (blame ⟨ h ?⟩)
   → N ≡ M ⊎ N ≡ blame
blame-project {M} {.M} (.M END) eq = inj₁ refl
blame-project {M} {N} (.M —→⟨ ξξ (□⟨ h ?⟩) refl refl r ⟩ →N′) refl rewrite blame—↠ (unit r) 
    with blame-project →N′ refl
... | inj₁ refl = inj₁ refl
... | inj₂ refl = inj₂ refl
blame-project {M} {N} (.M —→⟨ ξξ-blame F x ⟩ →N) refl rewrite blame—↠ →N = inj₂ refl
blame-project {.(ƛ _ · _)} {N} (.(ƛ _ · _) —→⟨ β x ⟩ →N) ()
blame-project {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collapse x g h () ⟩ →N) refl
blame-project {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collide x g h x₁ x₂ ⟩ →N) eq rewrite blame—↠ →N = inj₂ refl
      
compatible-project : ∀{Γ}{H}{h : Ground H}{M}
    → Γ ⊨ M ⦂ ★
    → Γ ⊨ M ⟨ h ?⟩ ⦂ H
compatible-project {Γ}{H}{h}{M} ⊨M k γ 𝓖Γγk = aux
  where
  aux : ∀ N → (M→N : (⟪ γ ⟫ M ⟨ h ?⟩) —↠ N) → (len M→N < k)
             → (𝓥⟦ H ⟧ N (k ∸ len M→N))
               ⊎ (∃[ N′ ] (N —→ N′))
               ⊎ N ≡ blame               
  aux N red (s≤s {n = n} <k)
      with project-multi-inv2 red
  {- Case 1 -}    
  ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
  {- Case 2 -}      
  ... | inj₁ (M′ , →M′ , refl , eq)
      with ⊨M k γ 𝓖Γγk
  ... | EM 
      with EM M′ →M′ (s≤s (≤-trans (≤-reflexive eq) <k))
  ... | inj₂ (inj₁ (M″ , M′→)) = inj₂ (inj₁ (_ , ξ □⟨ h ?⟩ M′→))
  ... | inj₂ (inj₂ refl) = inj₂ (inj₁ (_ , ξ-blame □⟨ h ?⟩))
  ... | inj₁ Vv′
      rewrite 1+m∸n n (len →M′) (≤-trans (≤-reflexive eq) <k)
      with V-dyn-inv2 M′ Vv′
  ... | (V′ , G , g , refl , Vv″)
      with g ≡ᵍ h
  ... | yes refl = inj₂ (inj₁ (_ , collapse (𝓥⇒Value V′ Vv″) g h refl))
  ... | no neq = inj₂ (inj₁ (_ , collide (𝓥⇒Value V′ Vv″) g h neq refl))
  {- Case 3 -}        
  aux N red (s≤s <k)
      | inj₂ (inj₁ (V , →V , v , →N , eq))
      with ⊨M k γ 𝓖Γγk
  ... | EM 
      with EM V →V (s≤s (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k))
  ... | inj₂ (inj₁ (V′ , V→)) = ⊥-elim (value-irreducible v V→)
  ... | inj₂ (inj₂ refl)
      with blame-project →N refl
  ... | inj₂ refl = inj₂ (inj₂ refl)
  ... | inj₁ refl
      with v
  ... | ()
  aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM
      | inj₁ Vv′
      rewrite 1+m∸n n (len →V) (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k)
      with V-dyn-inv2 V Vv′
  ... | (V′ , G , g , refl , Vv″)
      with →N
  ... | _ END =
      inj₂ (inj₁ (aux′ g h))
      where aux′ : ∀{G}{H} (g : Ground G) (h : Ground H) → ∃[ L ] (((V′ ⟨ g !⟩) ⟨ h ?⟩) —→ L)
            aux′ g h
                with g ≡ᵍ h
            ... | yes refl = _ , (collapse (𝓥⇒Value V′ Vv″) g h refl)
            ... | no neq = _ , (collide (𝓥⇒Value V′ Vv″) g h neq refl)
  ... | _ —→⟨ ξξ (□⟨ _ ?⟩) refl x₁ r1 ⟩ r2 = ⊥-elim (value-irreducible v r1)
  ... | _ —→⟨ ξξ-blame (□⟨ _ ?⟩) () ⟩ r2
  ... | _ —→⟨ collide x g₁ .h x₁ refl ⟩ r2
      with blame—↠ r2
  ... | refl = inj₂ (inj₂ refl)
  aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM
      | inj₁ Vv′
      | (V′ , G , g , refl , Vv″)
      | _ —→⟨ collapse _ g₁ .h refl ⟩ r2
      with value—↠ (𝓥⇒Value V′ Vv″) r2
  ... | refl =
        inj₁ (mono-𝓥 (≤⇒≤′ LT) Vv″)
      where LT : suc n ∸ len red ≤ n ∸ len →V
            LT = ≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) eq))
                (≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) (+-suc (len →V) (len r2))))
                (∸-monoʳ-≤{len →V}{len →V + len r2} n (m≤m+n (len →V) (len r2)) ))

compatible-blame : ∀{Γ}{A}
   → Γ ⊨ blame ⦂ A
compatible-blame{Γ}{A} k γ 𝓖Γγk = Goal
  where
  Goal : 𝓔⟦ A ⟧ blame k
  Goal N M→N <k
      with blame—↠ M→N
  ... | refl = inj₂ (inj₂ refl)

fundamental : ∀ {Γ A} → (M : Term)
  → Γ ⊢ M ⦂ A
    ----------
  → Γ ⊨ M ⦂ A
fundamental {Γ} {A} .(` _) (⊢` ∋x) = compatibility-var ∋x
fundamental {Γ} {.($ₜ ′ℕ)} .($ _) (⊢$ ′ℕ) = compatible-nat
fundamental {Γ} {.($ₜ ′𝔹)} .($ _) (⊢$ ′𝔹) = compatible-bool
fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) = compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) = compatible-fun {N = N} (fundamental N ⊢N)
fundamental {Γ} {.★} (M ⟨ g !⟩) (⊢⟨!⟩ ⊢M g) = compatible-inject {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} (M ⟨ h ?⟩) (⊢⟨?⟩ ⊢M h) = compatible-project {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} .blame ⊢blame = compatible-blame

type-safety : ∀ {A} → (M N : Term)
  → [] ⊢ M ⦂ A
  → M —↠ N
  → Value N  ⊎  (∃[ N′ ] (N —→ N′))  ⊎  N ≡ blame   
type-safety M N ⊢M M→N
    with fundamental M ⊢M (suc (len M→N)) id tt N M→N ≤-refl
... | inj₁ VN = inj₁ (𝓥⇒Value _ VN)    
... | inj₂ (inj₁ red) = inj₂ (inj₁ red)    
... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
