{-# OPTIONS --without-K --rewriting #-}
module rewriting.examples.CastSafe where

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
open import rewriting.examples.CastLogRel

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
  Val⇒Exp {A}{⟪ proj₁ γ ⟫ (` x)} k Vγx

compatible-nat : ∀{Γ}{n : ℕ} → Γ ⊨ ($ n) ⦂ ($ₜ ′ℕ)
compatible-nat {Γ}{n} k γ 𝓖Γγk = Val⇒Exp k G
    where G : 𝓥⟦ $ₜ ′ℕ ⟧ ($̬ n) k
          G rewrite V-base{k}{′ℕ}{′ℕ}{n} = refl

compatible-bool : ∀{Γ}{b : 𝔹} → Γ ⊨ ($ b) ⦂ ($ₜ ′𝔹)
compatible-bool {Γ}{b} k γ 𝓖Γγk = Val⇒Exp k G
    where G : 𝓥⟦ $ₜ ′𝔹 ⟧ ($̬ b) k
          G rewrite V-base{k}{′𝔹}{′𝔹}{b} = refl

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


E-app : ∀{A}{B}{L}{L′}{M}{M′}{n}
   → 𝓔⟦ A ⇒ B ⟧ L (suc n)
   → (L→L′ : L —↠ L′)
   → len L→L′ ≤ n
   → 𝓔⟦ A ⟧ M (suc n)
   → (M→M′ : M —↠ M′)
   → len M→M′ ≤ n
   → ∃[ N ] (L′ · M′ —→ N)
E-app {A}{B}{L}{L′}{M}{M′}{n} EL L→L′ lt1 EM M→M′ lt2
    rewrite E-def (A ⇒ B) L (suc n) | E-def A M (suc n) | E-def B (L · M) (suc n)
    with EL L′ L→L′ (s≤s lt1)
... | inj₂ (inj₁ (L″ , L′→L″)) = (_ , ξ (□· _) L′→L″)
... | inj₂ (inj₂ refl) = (_ , ξ-blame (□· _))
... | inj₁ (v′ , Vv′)
    with EM M′ M→M′ (s≤s lt2)
... | inj₂ (inj₁ (M″ , M′→M″)) = (_ , ξ (v′ ·□) M′→M″)
... | inj₂ (inj₂ beq) rewrite beq = (_ , ξ-blame (v′ ·□))
... | inj₁ (w , Vw ) rewrite unfold-Safe (suc n ∸ len L→L′ , suc (size A ⊔ size B))
    with v′
... | $̬ c = ⊥-elim Vv′
... | v 〈 g 〉 = ⊥-elim Vv′
... | ƛ̬ N = (_ , β w)

lemma6 : ∀ n x y w z
   → (<k : x ≤ n)
   → (eq : x ≡ y + w + z)
   → suc w ≤ suc n
lemma6 n x y w z <k eq = (s≤s (≤-trans (≤-trans (≤-trans (m≤n+m w (y + z))
         (≤-reflexive (trans (+-assoc y z w) (trans (cong (λ X → y + X) (+-comm z w))
         (sym (+-assoc y w z)))))) (≤-reflexive (sym eq))) <k))

compatible-app : ∀{Γ}{A}{B}{L}{M}
    → Γ ⊨ L ⦂ (A ⇒ B)
    → Γ ⊨ M ⦂ A
      -------------------
    → Γ ⊨ L · M ⦂ B
compatible-app {Γ}{A}{B}{L}{M} ⊨L ⊨M k γ 𝓖Γγk 
    rewrite E-def B (⟪ proj₁ γ ⟫ (L · M)) k = Goal
    where
    Goal : (N : Term) (M→N : ⟪ proj₁ γ ⟫ L · ⟪ proj₁ γ ⟫ M —↠ N)
       → suc (len M→N) ≤ k
       → Data.Product.Σ (Value N) (proj₁ (Safe (k ∸ len M→N , size B) B refl))
        ⊎ Data.Product.Σ Term (_—→_ N) ⊎ N ≡ blame
    Goal N L·M→N (s≤s {n = n} <k)
        with app-multi-inv L·M→N
        {-
           Case 1:    L · M —↠ L′ · M
         -}
    ... | inj₁ (L′ , L→L′ , refl , eq)
        with ⊨L k γ 𝓖Γγk | ⊨M k γ 𝓖Γγk
    ... | EL | EM = inj₂ (inj₁ (E-app EL L→L′ LT  EM (_ END) z≤n))
        where LT = (≤-trans (≤-reflexive (sym eq)) <k)
        {-
           Case 2:    L · M —↠ V · M′
         -}
    Goal N L·M→N (s≤s {n = n} <k)
        | inj₂ (inj₁ (V , M′ , L→V , v′ , M→M′ , refl , eq))
        with ⊨L k γ 𝓖Γγk | ⊨M k γ 𝓖Γγk
    ... | EL | EM = inj₂ (inj₁ (E-app EL L→V LT1 EM M→M′ LT2))
        where LT1 = (≤-trans (≤-trans (m≤m+n (len L→V) (len M→M′)) (≤-reflexive (sym eq))) <k)
              LT2 = (≤-trans (≤-trans (m≤n+m (len M→M′) (len L→V)) (≤-reflexive (sym eq))) <k)
        {-
           Case 3:    L · M —↠ V · W —↠ N
         -}
    Goal N L·M→N (s≤s {n = n} <k)
        | inj₂ (inj₂ (V , W , L→V , v′ , M→W , w , VW→N , eq))
        with ⊨L k γ 𝓖Γγk |  ⊨M k γ 𝓖Γγk
    ... | EL | EM
        rewrite E-def (A ⇒ B) (⟪ proj₁ γ ⟫ L) (suc n)
                | E-def A (⟪ proj₁ γ ⟫ M) (suc n)
        with EL V L→V (s≤s (≤-trans (≤-trans (≤-trans (m≤m+n (len L→V) _)
                             (≤-reflexive (sym (+-assoc (len L→V) _ _))))
                             (≤-reflexive (sym eq))) <k))
    ... | inj₂ (inj₂ beq) =                                 ⊥-elim (blame-not-value v′ beq)
    ... | inj₂ (inj₁ (V′ , V→V′)) =                         ⊥-elim (value-irreducible v′ V→V′)
    ... | inj₁ (v′ , Vv′)
        with EM W M→W (lemma6 n (len L·M→N) (len L→V) (len M→W) (len VW→N) <k eq)
    ... | inj₂ (inj₂ beq) =                                 ⊥-elim (blame-not-value w beq)
    ... | inj₂ (inj₁ (W′ , W→W′)) =                         ⊥-elim (value-irreducible w W→W′)
    ... | inj₁ (w′ , Vw′)
        with v′
    ... | $̬ c rewrite unfold-Safe (suc n ∸ len L→V , suc (size A ⊔ size B)) = ⊥-elim Vv′
    ... | v 〈 g 〉 rewrite unfold-Safe (suc n ∸ len L→V , suc (size A ⊔ size B)) = ⊥-elim Vv′
    ... | ƛ̬ N′
        with VW→N
    ... | _ END = inj₂ (inj₁ (_ , β w))
    ... | _ —→⟨ ξ (_ ·□) r₁ ⟩ r₂ =                          ⊥-elim (value-irreducible w r₁)
    ... | _ —→⟨ ξ (□· _) r₁ ⟩ r₂ =                          ⊥-elim (value-irreducible v′ r₁)
    ... | _ —→⟨ ξ-blame (_ ·□) ⟩ r₂ =                       ⊥-elim (blame-not-value w refl)
    ... | _ —→⟨ β w″ ⟩ N[W]—↠N
        {-
          Subcase: (ƛ N′) · W —→ N′ [ W ] —↠ N
        -}
        with mono-𝓥 {k ∸ (len L→V + len M→W)} (≤⇒≤′ (∸-monoʳ-≤ {len L→V}{len L→V + len M→W} (suc n) (m≤m+n (len L→V) (len M→W)))) Vv′
           | mono-𝓥 {k ∸ (len L→V + len M→W)} (≤⇒≤′ (∸-monoʳ-≤ {len M→W}{len L→V + len M→W} (suc n) (m≤n+m _ _))) Vw′ 
    ... | Vv″ | Vw″ rewrite V-fun {suc n ∸ (len L→V + len M→W)}{A}{B}{N′} 
        with Vv″ w′ _ ≤-refl Vw″
    ... | EN
        rewrite E-def B (⟪ W • id ⟫ N′) (suc n ∸ (len L→V + len M→W)) 
        with EN N N[W]—↠N ((≤-trans (s≤s (≤-trans (≤-trans (lemma5 (len N[W]—↠N) (len L→V) (len M→W))
                      (≤-reflexive (cong (λ X → X ∸ (len L→V + len M→W)) (sym eq))))
                      (∸-monoˡ-≤ (len L→V + len M→W) <k))) (≤-reflexive (sym (1+m∸n n (len L→V + len M→W)
                      (≤-trans (≤-trans (m≤m+n (len L→V + len M→W) (suc (len N[W]—↠N))) (≤-reflexive (sym eq))) <k))))))
    ... | inj₁ (vN , VN) = inj₁ (vN , mono-𝓥 (≤⇒≤′ (≤-trans (≤-reflexive (sym EQ)) LT2)) VN)
        where
          LT2 : n ∸ (len L→V + len M→W + len N[W]—↠N) ≤ (suc n ∸ (len L→V + len M→W)) ∸ len N[W]—↠N
          LT2 = ≤-trans (∸-monoˡ-≤ (len L→V + len M→W + len N[W]—↠N) (≤-step ≤-refl))
                       (≤-reflexive (sym (∸-+-assoc (suc n) (len L→V + len M→W) (len N[W]—↠N))))

          open Eq.≡-Reasoning
          EQ : n ∸ (len L→V + len M→W + len N[W]—↠N) ≡ suc n ∸ len L·M→N
          EQ =
            begin
              n ∸ (len L→V + len M→W + len N[W]—↠N)                   ≡⟨ refl ⟩
              suc n ∸ (suc ((len L→V + len M→W) + (len N[W]—↠N)))
                                                           ≡⟨ cong (λ X → suc n ∸ X) (sym (+-suc (len L→V + len M→W) (len N[W]—↠N))) ⟩
              suc n ∸ ((len L→V + len M→W) + suc (len N[W]—↠N))         ≡⟨ cong (λ X → suc n ∸ X) (sym eq) ⟩
              suc n ∸ len L·M→N
              ∎
              

    ... | inj₂ (inj₁ (N″ , N→)) = inj₂ (inj₁ (N″ , N→))
    ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)



compatible-fun : ∀{Γ}{A}{B}{N}
    → (A ∷ Γ) ⊨ N ⦂ B
    → Γ ⊨ ƛ N ⦂ (A ⇒ B)
compatible-fun {Γ}{A}{B}{N} ⊨N k γ 𝓖Γγk =
  Val⇒Exp {V = ⟪ proj₁ γ ⟫ (ƛ N)}{ƛ̬ ⟪ ext (proj₁ γ) ⟫ N} k (G k 𝓖Γγk)
  where
    G : ∀ k → 𝓖⟦ Γ ⟧ γ k → 𝓥⟦ A ⇒ B ⟧ (ƛ̬ ⟪ ext (proj₁ γ) ⟫ N) k
    G k 𝓖Γγk rewrite V-fun {k}{A}{B}{⟪ ext (proj₁ γ) ⟫ N} = H
      where
      H : ∀ {V} (v : Value V) (j : ℕ) → j ≤ k
        → 𝓥⟦ A ⟧ v j
        → 𝓔⟦ B ⟧ ((⟪ ext (proj₁ γ) ⟫ N) [ V ]) j
      H {V} v j lt Vvj =
        ⊨N j γ′ (mono-SafeEnv j k _ (≤⇒≤′ lt) 𝓖Γγk , Vvj)
        where γ′ = (V • proj₁ γ , λ { zero → v ; (suc x) → proj₂ γ x})
              lt2 = (≤⇒≤′ (≤-trans lt (n≤1+n k)))

compatible-inject : ∀{Γ}{G}{g : Ground G}{M}
    → Γ ⊨ M ⦂ G
    → Γ ⊨ M ⟨ g !⟩ ⦂ ★
compatible-inject{Γ}{G}{g}{M} ⊨M k γ 𝓖Γγk
  rewrite E-def ★ (⟪ proj₁ γ ⟫ M ⟨ g !⟩) k = H
  where
  H : ∀ N → (M→N : (⟪ proj₁ γ ⟫ M ⟨ g !⟩) —↠ N) → (len M→N < k)
             → (Σ[ v ∈ Value N ] 𝓥⟦ ★ ⟧ v (k ∸ len M→N))
               ⊎ (∃[ N′ ] (N —→ N′))
               ⊎ N ≡ blame               
  H N red (s≤s {n = n} <k)
      with inject-multi-inv red
  ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
  ... | inj₁ (M′ , →M′ , refl , eqlen)
      with ⊨M k γ 𝓖Γγk
  ... | EM rewrite E-def G (⟪ proj₁ γ ⟫ M) k
      with EM M′ →M′ (s≤s (≤-trans (≤-reflexive eqlen) <k))
  ... | inj₂ (inj₁ (M″ , M′→)) = inj₂ (inj₁ (_ , ξ □⟨ g !⟩ M′→))
  ... | inj₂ (inj₂ refl) = inj₂ (inj₁ (_ , ξ-blame □⟨ g !⟩))
  ... | inj₁ (v′ , Vv′) = inj₁ ((v′ 〈 g 〉) , Goal)
      where
        lt : n ∸ len red ≤ suc n ∸ len →M′
        lt = ≤-trans (≤-reflexive (cong (λ X → n ∸ X) (sym eqlen) ))
                     (≤-trans (n≤1+n _)
                        (≤-reflexive (sym (1+m∸n n _ (subst (λ X → X ≤ n) (sym eqlen) <k))) ))
        Goal : proj₁ (Safe (suc n ∸ len red , 0) ★ refl) (v′ 〈 g 〉)
        Goal rewrite 1+m∸n n (len red) <k = V-intro (mono-𝓥 (≤⇒≤′ lt) Vv′)
            
  H N red (s≤s {n = n} <k)
      | inj₂ (inj₁ (V , →V , v , →N , eq))
      with ⊨M k γ 𝓖Γγk
  ... | EM
      rewrite E-def G (⟪ proj₁ γ ⟫ M) k
      with EM V →V (s≤s (≤-trans (subst (λ X → len →V ≤ X) (sym eq) (m≤m+n _ _)) <k))
  ... | inj₁ (v′ , Vv′)
      with value—↠ (v 〈 g 〉) →N
  ... | refl rewrite 1+m∸n n (len red) <k =      
        inj₁ ((v′ 〈 g 〉) , V-intro (mono-𝓥 (≤⇒≤′ LT) Vv′))
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

  
aux2 : ∀{M}{N}{H}{h : Ground H} → M —↠ N → M ≡ (blame ⟨ h ?⟩) → N ≡ M ⊎ N ≡ blame
aux2 {M} {.M} (.M END) eq = inj₁ refl
aux2 {M} {N} (.M —→⟨ ξξ (□⟨ h ?⟩) refl refl r ⟩ →N′) refl rewrite blame—↠ (unit r) 
    with aux2 →N′ refl
... | inj₁ refl = inj₁ refl
... | inj₂ refl = inj₂ refl
aux2 {M} {N} (.M —→⟨ ξξ-blame F x ⟩ →N) refl rewrite blame—↠ →N = inj₂ refl
aux2 {.(ƛ _ · _)} {N} (.(ƛ _ · _) —→⟨ β x ⟩ →N) ()
aux2 {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collapse x g h () ⟩ →N) refl
aux2 {.(_ ⟨ h ?⟩)} {N} (.(_ ⟨ h ?⟩) —→⟨ collide x g h x₁ x₂ ⟩ →N) eq rewrite blame—↠ →N = inj₂ refl
      
compatible-project : ∀{Γ}{H}{h : Ground H}{M}
    → Γ ⊨ M ⦂ ★
    → Γ ⊨ M ⟨ h ?⟩ ⦂ H
compatible-project {Γ}{H}{h}{M} ⊨M k γ 𝓖Γγk
  rewrite E-def H (⟪ proj₁ γ ⟫ M ⟨ h ?⟩) k = aux
  where
  aux : ∀ N → (M→N : (⟪ proj₁ γ ⟫ M ⟨ h ?⟩) —↠ N) → (len M→N < k)
             → (Σ[ v ∈ Value N ] 𝓥⟦ H ⟧ v (k ∸ len M→N))
               ⊎ (∃[ N′ ] (N —→ N′))
               ⊎ N ≡ blame               
  aux N red (s≤s {n = n} <k)
      with project-multi-inv2 red
  {- Case 1 -}    
  ... | inj₂ (inj₂ refl) = inj₂ (inj₂ refl)
  {- Case 2 -}      
  ... | inj₁ (M′ , →M′ , refl , eq)
      with ⊨M k γ 𝓖Γγk
  ... | EM rewrite E-def ★ (⟪ proj₁ γ ⟫ M) k
      with EM M′ →M′ (s≤s (≤-trans (≤-reflexive eq) <k))
  ... | inj₂ (inj₁ (M″ , M′→)) = inj₂ (inj₁ (_ , ξ □⟨ h ?⟩ M′→))
  ... | inj₂ (inj₂ refl) = inj₂ (inj₁ (_ , ξ-blame □⟨ h ?⟩))
  ... | inj₁ (v′ , Vv′)
      rewrite 1+m∸n n (len →M′) (≤-trans (≤-reflexive eq) <k)
      with V-dyn-inv Vv′
  ... | (V′ , G , g , refl , v″)
      with g ≡ᵍ h
  ... | yes refl = inj₂ (inj₁ (_ , collapse v″ g h refl))
  ... | no neq = inj₂ (inj₁ (_ , collide v″ g h neq refl))
  {- Case 3 -}        
  aux N red (s≤s <k)
      | inj₂ (inj₁ (V , →V , v , →N , eq))
      with ⊨M k γ 𝓖Γγk
  ... | EM rewrite E-def ★ (⟪ proj₁ γ ⟫ M) k
      with EM V →V (s≤s (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k))
  ... | inj₂ (inj₁ (V′ , V→)) = ⊥-elim (value-irreducible v V→)
  ... | inj₂ (inj₂ refl)
      with aux2 →N refl
  ... | inj₂ refl = inj₂ (inj₂ refl)
  ... | inj₁ refl
      with v
  ... | ()
  aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM
      | inj₁ (v′ , Vv′)
      rewrite 1+m∸n n (len →V) (≤-trans (≤-trans (m≤m+n (len →V) (len →N)) (≤-reflexive (sym eq))) <k)
      with V-dyn-inv2 Vv′
  ... | (V′ , G , g , refl , v″ , Vv″)
      with →N
  ... | _ END =
      inj₂ (inj₁ (aux′ g h))
      where aux′ : ∀{G}{H} (g : Ground G) (h : Ground H) → ∃[ L ] (((V′ ⟨ g !⟩) ⟨ h ?⟩) —→ L)
            aux′ g h
                with g ≡ᵍ h
            ... | yes refl = _ , (collapse v″ g h refl)
            ... | no neq = _ , (collide v″ g h neq refl)
  ... | _ —→⟨ ξξ (□⟨ _ ?⟩) refl x₁ r1 ⟩ r2 = ⊥-elim (value-irreducible v r1)
  ... | _ —→⟨ ξξ-blame (□⟨ _ ?⟩) () ⟩ r2
  ... | _ —→⟨ collide x g₁ .h x₁ refl ⟩ r2
      with blame—↠ r2
  ... | refl = inj₂ (inj₂ refl)
  aux N red (s≤s {n = n} <k) | inj₂ (inj₁ (V , →V , v , →N , eq)) | EM
      | inj₁ (v′ , Vv′)
      | (V′ , G , g , refl , v″ , Vv″)
      | _ —→⟨ collapse _ g₁ .h refl ⟩ r2
      with value—↠ v″ r2
  ... | refl =
        inj₁ (v″ , mono-𝓥 (≤⇒≤′ LT) Vv″)
      where LT : suc n ∸ len red ≤ n ∸ len →V
            LT = ≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) eq))
                (≤-trans (≤-reflexive (cong (λ X → suc n ∸ X) (+-suc (len →V) (len r2))))
                (∸-monoʳ-≤{len →V}{len →V + len r2} n (m≤m+n (len →V) (len r2)) ))

compatible-blame : ∀{Γ}{A}
   → Γ ⊨ blame ⦂ A
compatible-blame{Γ}{A} k γ 𝓖Γγk rewrite E-def A blame k = Goal
  where
  Goal : (N : Term) (M→N : blame —↠ N) → suc (len M→N) ≤ k →
           Data.Product.Σ (Value N) (proj₁ (Safe (k ∸ len M→N , size A) A refl))
           ⊎ Data.Product.Σ Term (_—→_ N) ⊎ N ≡ blame
  Goal N M→N <k
      with blame—↠ M→N
  ... | refl = inj₂ (inj₂ refl)

fundamental : ∀ {Γ A} → (M : Term)
  → (Γ ⊢ M ⦂ A)
    -----------
  → (Γ ⊨ M ⦂ A)

fundamental {Γ} {A} .(` _) (⊢` ∋x) = compatibility-var ∋x
fundamental {Γ} {.($ₜ ′ℕ)} .($ _) (⊢$ ′ℕ) = compatible-nat
fundamental {Γ} {.($ₜ ′𝔹)} .($ _) (⊢$ ′𝔹) = compatible-bool
fundamental {Γ} {A} (L · M) (⊢· ⊢L ⊢M) = compatible-app{L = L}{M} (fundamental L ⊢L) (fundamental M ⊢M)
fundamental {Γ} {.(_ ⇒ _)} (ƛ N) (⊢ƛ ⊢N) = compatible-fun {N = N} (fundamental N ⊢N)
fundamental {Γ} {.★} (M ⟨ g !⟩) (⊢⟨!⟩ ⊢M g) = compatible-inject {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} (M ⟨ h ?⟩) (⊢⟨?⟩ ⊢M h) = compatible-project {M = M} (fundamental M ⊢M)
fundamental {Γ} {A} .blame ⊢blame = compatible-blame

