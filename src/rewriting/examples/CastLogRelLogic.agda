{-# OPTIONS --rewriting #-}
module rewriting.examples.CastLogRelLogic where

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Nat.Properties
open import Data.Product using (_,_;_×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst; trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Var
open import rewriting.examples.Cast
open import rewriting.examples.CastDeterministic
open import rewriting.examples.StepIndexedLogic

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

𝒱ᶠ⟦_⟧ : Type → Term → Fun ℰ⊎𝒱-type ⊤ Continuous
𝒱ᶠ⟦ A ⟧ V = recur (inj₁ (A , V))

ℰᶠ⟦_⟧ : Type → Term → Fun ℰ⊎𝒱-type ⊤ Continuous
ℰᶠ⟦ A ⟧ M = recur (inj₂ (A , M))

pre-𝒱 : Type → Term → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-𝒱 ★ (V ⟨ G , g !⟩ ) =
    (Value V)ᶠ ×ᶠ ▷ᶠ (𝒱ᶠ⟦ G ⟧ V)
pre-𝒱 ($ₜ ι) (op-lit {ι′} c ⦅ nil ⦆) =   -- ($ c)
    (ι ≡ ι′)ᶠ
pre-𝒱 (A ⇒ B) (ƛ N) =
    ∀ᶠ[ W ] ▷ᶠ (𝒱ᶠ⟦ A ⟧ W) →ᶠ ▷ᶠ (ℰᶠ⟦ B ⟧ (N [ W ]))

-- bogus cases for ★
pre-𝒱 ★ (` x) = (⊥) ᶠ
pre-𝒱 ★ ($ c) = (⊥) ᶠ
pre-𝒱 ★ (ƛ N) = (⊥) ᶠ
pre-𝒱 ★ (L · M) = (⊥) ᶠ
pre-𝒱 ★ (M ⟨ H , h ?⟩) = (⊥) ᶠ
pre-𝒱 ★ blame = (⊥) ᶠ

-- bogus cases for ι
pre-𝒱 ($ₜ ι) (` x) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (ƛ N) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (L · M) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (M ⟨ G , g !⟩) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) (M ⟨ H , h ?⟩) = (⊥) ᶠ
pre-𝒱 ($ₜ ι) blame = (⊥) ᶠ

-- bogus cases for A ⇒ B
pre-𝒱 (A ⇒ B) (` x) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) ($ c) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (L · M) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (M ⟨ G , g !⟩) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) (M ⟨ H , h ?⟩) = (⊥) ᶠ
pre-𝒱 (A ⇒ B) blame = (⊥) ᶠ

-- Type Safety = Progress & Preservation
pre-ℰ : Type → Term
       → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-ℰ A M = (pre-𝒱 A M ⊎ᶠ (reducible M)ᶠ ⊎ᶠ (Blame M)ᶠ)    -- Progress
             ×ᶠ (∀ᶠ[ N ] (M —→ N)ᶠ →ᶠ ▷ᶠ (ℰᶠ⟦ A ⟧ N))        -- Preservation

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Fun ℰ⊎𝒱-type ⊤ Wellfounded
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M

ℰ⊎𝒱 : Fun ℰ⊎𝒱-type ℰ⊎𝒱-type Wellfounded
ℰ⊎𝒱 = flipᶠ pre-ℰ⊎𝒱 tt

-- Semantically Well Typed Value
𝒱⟦_⟧ : (A : Type) → Term → Setᵒ
𝒱⟦ A ⟧ V = (μᵒ ℰ⊎𝒱) (inj₁ (A , V))

-- Semantically Well Typed Term
ℰ⟦_⟧ : (A : Type) → Term → Setᵒ
ℰ⟦ A ⟧ M = (μᵒ ℰ⊎𝒱) (inj₂ (A , M))

ℰ⊎𝒱-fixpointᵒ : ∀ X → (μᵒ ℰ⊎𝒱) X ≡ᵒ ((fun ℰ⊎𝒱) (μᵒ ℰ⊎𝒱)) X
ℰ⊎𝒱-fixpointᵒ X = apply-≡ᵖ (fixpoint ℰ⊎𝒱) X 

progress : Type → Term → Setᵒ
progress A M = (𝒱⟦ A ⟧ M) ⊎ᵒ (reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)))

ℰ-stmt : ∀{A}{M}
  → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                                  ≡⟨ ≡ᵒ-refl refl ⟩
  (μᵒ ℰ⊎𝒱) (inj₂ (A , M))                  ≡⟨ ℰ⊎𝒱-fixpointᵒ (inj₂ (A , M)) ⟩
  ((fun ℰ⊎𝒱) (μᵒ ℰ⊎𝒱)) (inj₂ (A , M))
                  ≡⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (ℰ⊎𝒱-fixpointᵒ (inj₁ (A , M))))
                                       (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M
  QEDᵒ

ℰ-progress : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ progress A M
ℰ-progress 𝓟⊢ℰM = proj₁ᵒ (substᵒ ℰ-stmt 𝓟⊢ℰM )

ℰ-preservation : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝓟 ⊢ᵒ preservation A M
ℰ-preservation 𝓟⊢ℰM = proj₂ᵒ (substᵒ ℰ-stmt 𝓟⊢ℰM )

ℰ-intro : ∀ {𝓟}{A}{M}
  → 𝓟 ⊢ᵒ progress A M
  → 𝓟 ⊢ᵒ preservation A M
    ----------------------
  → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝓟⊢prog 𝓟⊢pres = substᵒ (≡ᵒ-sym (ℰ-stmt)) (𝓟⊢prog ,ᵒ 𝓟⊢pres)

ℰ-blame : ∀{𝓟}{A} → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ blame
ℰ-blame {𝓟}{A} =
    ℰ-intro (inj₂ᵒ (inj₂ᵒ (⊢ᵒ-Sᵒ-intro isBlame)))
            (Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ blame→ → ⊥-elim (blame-irreducible blame→)))

𝒱⇒Value : ∀ {k} A M
   → # (𝒱⟦ A ⟧ M) (suc k)
     ---------------------
   → Value M
𝒱⇒Value ★ (M ⟨ G , g !⟩) (v , _) = v 〈 g 〉
𝒱⇒Value ($ₜ ι) ($ c) 𝒱M = $̬ c
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = ƛ̬ N
-- vacuous cases
𝒱⇒Value ★ (` x) ()
𝒱⇒Value ★ ($ c) ()
𝒱⇒Value ★ (ƛ N) ()
𝒱⇒Value ★ (L · M) ()
𝒱⇒Value ★ (M ⟨ H , h ?⟩) ()
𝒱⇒Value ★ blame ()
𝒱⇒Value ($ₜ ι) (` x) ()
𝒱⇒Value ($ₜ ι) (ƛ N) ()
𝒱⇒Value ($ₜ ι) (L · M) ()
𝒱⇒Value ($ₜ ι) (M ⟨ G , g !⟩) ()
𝒱⇒Value ($ₜ ι) (M ⟨ H , h ?⟩) ()
𝒱⇒Value ($ₜ ι) blame ()
𝒱⇒Value (A ⇒ B) (` x) ()
𝒱⇒Value (A ⇒ B) ($ c) ()
𝒱⇒Value (A ⇒ B) (L · M) ()
𝒱⇒Value (A ⇒ B) (M ⟨ G , g !⟩) ()
𝒱⇒Value (A ⇒ B) (M ⟨ H , h ?⟩) ()
𝒱⇒Value (A ⇒ B) blame ()

V-base : ∀{ι}{ι′}{c : rep ι′}
   → (𝒱⟦ $ₜ ι ⟧ ($ c)) ≡ᵒ (ι ≡ ι′)ᵒ
V-base = ≡ᵒ-intro (λ k z → z) (λ k z → z)

V-dyn : ∀{G}{V}{g : Ground G}
   → 𝒱⟦ ★ ⟧ (V ⟨ G , g !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ V))
V-dyn {G}{V}{g} =
   let X = (inj₁ (★ , V ⟨ G , g !⟩)) in
   𝒱⟦ ★ ⟧ (V ⟨ G , g !⟩)                              ≡⟨ ≡ᵒ-refl refl ⟩
   (μᵒ ℰ⊎𝒱) X                                     ≡⟨ ℰ⊎𝒱-fixpointᵒ X ⟩
   ((fun ℰ⊎𝒱) (μᵒ ℰ⊎𝒱)) X                        ≡⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ V)
   QEDᵒ

V-dyn-elim : ∀{𝓟}{V}{R}
   → 𝓟 ⊢ᵒ 𝒱⟦ ★ ⟧ V
   → (∀ W G (g : Ground G) → V ≡ W ⟨ G , g !⟩
             → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ W))
             → 𝓟 ⊢ᵒ R)
     ----------------------------------------------
   → 𝓟 ⊢ᵒ R
V-dyn-elim {𝓟}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G 𝒱Vsn ⊢𝒱V cont }
  where
  G : ∀{V}{n}
      → # (𝒱⟦ ★ ⟧ V) (suc n)
      → 𝓟 ⊢ᵒ 𝒱⟦ ★ ⟧ V
      → (∀ W G g → V ≡ W ⟨ G , g !⟩
                → 𝓟 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ G ⟧ W))
                → 𝓟 ⊢ᵒ R)
      → 𝓟 ⊢ᵒ R
  G {W ⟨ G , g !⟩}{n} 𝒱Vsn ⊢𝒱V cont
      with 𝒱⇒Value ★ (W ⟨ G , g !⟩) 𝒱Vsn
  ... | w 〈 g 〉 =
      let ⊢▷𝒱W = proj₂ᵒ (substᵒ (V-dyn{V = W}{g}) ⊢𝒱V) in
      cont W _ g refl (⊢ᵒ-Sᵒ-intro w ,ᵒ ⊢▷𝒱W)
  G {` x}{n} ()
  G {$ c}{n} ()
  G {ƛ N}{n} ()
  G {L · M}{n} ()
  G {M ⟨ H , h ?⟩}{n} ()
  G {blame}{n} ()
  
V-fun : ∀{A B}{N}
   → (𝒱⟦ A ⇒ B ⟧ (ƛ N))
      ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
V-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   (𝒱⟦ A ⇒ B ⟧ (ƛ N))                                  ≡⟨ ≡ᵒ-refl refl ⟩
   (μᵒ ℰ⊎𝒱) X                                          ≡⟨ ℰ⊎𝒱-fixpointᵒ X ⟩
   ((fun ℰ⊎𝒱) (μᵒ ℰ⊎𝒱)) X                             ≡⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
   QEDᵒ

V-fun-elim : ∀{𝓟}{A}{B}{V}{R}
   → 𝓟 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝓟 ⊢ᵒ R
V-fun-elim {𝓟}{A}{B}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G {V} 𝒱Vsn ⊢𝒱V cont}
  where
  G : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝓟 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝓟 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝓟 ⊢ᵒ R)
     → 𝓟 ⊢ᵒ R
  G{ƛ N}{n} 𝒱V ⊢𝒱V cont = cont N refl λ {W} →
      instᵒ{P = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (substᵒ V-fun ⊢𝒱V) W
  G{` x}{n} ()
  G{$ c}{n} ()
  G{L · M}{n} ()
  G{M ⟨ G , g !⟩}{n} ()
  G{M ⟨ H , h ?⟩}{n} ()
  G{blame}{n} ()

{- Semantic Type Safety -}

𝓖⟦_⟧ : (Γ : List Type) → Subst → List Setᵒ
𝓖⟦ [] ⟧ σ = []
𝓖⟦ A ∷ Γ ⟧ σ = (𝒱⟦ A ⟧ (σ 0)) ∷ 𝓖⟦ Γ ⟧ (λ x → σ (suc x))

_⊨_⦂_ : List Type → Term → Type → Set
Γ ⊨ M ⦂ A = ∀ (γ : Subst) → 𝓖⟦ Γ ⟧ γ ⊢ᵒ ℰ⟦ A ⟧ (⟪ γ ⟫ M)

lookup-𝓖 : (Γ : List Type) → (γ : Subst)
  → ∀ {A}{y} → (Γ ∋ y ⦂ A)
  → 𝓖⟦ Γ ⟧ γ ⊢ᵒ 𝒱⟦ A ⟧ (γ y)
lookup-𝓖 (B ∷ Γ) γ {A} {zero} refl = Zᵒ
lookup-𝓖 (B ∷ Γ) γ {A} {suc y} ∋y =
    Sᵒ (lookup-𝓖 Γ (λ x → γ (suc x)) ∋y) 

{- Semantic Values are Semantic Expressions -}

𝒱⇒ℰ : ∀{A}{𝓟}{V}
   → 𝓟 ⊢ᵒ 𝒱⟦ A ⟧ V
     ---------------
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝓟}{V} 𝓟⊢𝒱V =
    ⊢ᵒ-intro
    λ n ⊨𝓟n →
    let 𝒱V = (⊢ᵒ-elim 𝓟⊢𝒱V) n ⊨𝓟n in
    (inj₁ 𝒱V) , λ { N zero x V→N → tt ;
                     N (suc j) (s≤s j≤) V→N →
                         ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V) V→N)}

{- ℰ-frame (Monadic Bind Lemma) -}

ℰ-f-cont : Type → Type → Frame → Term → Setᵒ
ℰ-f-cont A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)

ℰ-fp : Type → Type → Frame → Term → Setᵒ
ℰ-fp A B F M = ℰ⟦ B ⟧ M
                →ᵒ ℰ-f-cont A B F M
                →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-frame-prop : Type → Type → Frame → Setᵒ
ℰ-frame-prop A B F = ∀ᵒ[ M ] ℰ-fp A B F M

frame-prop-lemma : ∀{𝓟}{A}{B}{M}{F}
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ-frame-prop A B F
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M
   → 𝓟 ⊢ᵒ ▷ᵒ ℰ-f-cont A B F M
   → 𝓟 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M ⟧))
frame-prop-lemma{𝓟}{A}{B}{M}{F} IH ℰM V→FV =
  let IH′ = instᵒ (▷∀{P = λ M → ℰ-fp A B F M} IH) M in
  appᵒ (▷→ (appᵒ (▷→ IH′) ℰM)) V→FV

ℰ-f-cont-lemma : ∀{𝓟}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝓟 ⊢ᵒ ℰ-f-cont A B F M
     -----------------------
   → 𝓟 ⊢ᵒ ℰ-f-cont A B F M′
ℰ-f-cont-lemma {𝓟}{A}{B}{F}{M}{M′} M→M′ ℰ-cont =
   Λᵒ[ V ]
    let M→V→ℰFV : 𝓟 ⊢ᵒ (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M→V→ℰFV = instᵒ ℰ-cont V in
    let M′→V→ℰFV : 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝓟 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M′→V→ℰFV = ⊢ᵒ-intro λ{ zero (𝒱Vn , M′→Vn , ⊨𝓟n) →
                                tz (ℰ⟦ A ⟧ (F ⟦ V ⟧))
                             ; (suc n) (𝒱Vsn , M′→Vsn , ⊨𝓟sn) →
                               ⊢ᵒ-elim M→V→ℰFV (suc n) ⊨𝓟sn (suc n) ≤-refl
                               (M —→⟨ M→M′ ⟩ M′→Vsn)
                               (suc n) ≤-refl 𝒱Vsn } in
    →ᵒI (→ᵒI M′→V→ℰFV)

ℰ-frame-aux : ∀{𝓟}{A}{B}{F} → 𝓟 ⊢ᵒ ℰ-frame-prop A B F
ℰ-frame-aux {𝓟}{A}{B}{F} = ⊢ᵒ-lob Goal
 where     
 Goal : ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟 ⊢ᵒ ℰ-frame-prop A B F
 Goal = Λᵒ[ M ] →ᵒI (→ᵒI Goal′)
  where
  Goal′ : ∀{M}
     → (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟
        ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  Goal′{M} =
   let ⊢ℰM : 𝓟′ ⊢ᵒ ℰ⟦ B ⟧ M
       ⊢ℰM = Sᵒ Zᵒ in
   case3ᵒ (ℰ-progress ⊢ℰM) Mval Mred Mblame
   where
   𝓟′ = (ℰ-f-cont A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-frame-prop A B F ∷ 𝓟

   Mval : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval =
     let ⊢𝒱M : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ 𝒱⟦ B ⟧ M
         ⊢𝒱M = Zᵒ in
     let ℰcontFM : 𝒱⟦ B ⟧ M ∷ 𝓟′ ⊢ᵒ ℰ-f-cont A B F M
         ℰcontFM = Sᵒ Zᵒ in
     let Cont = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
     appᵒ (appᵒ (instᵒ{P = Cont} ℰcontFM M)
                          (⊢ᵒ-Sᵒ-intro (M END)))
               ⊢𝒱M

   Mred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred
         (Sᵒ⊢ᵒ λ redM → Λᵒ[ N ] →ᵒI (Sᵒ⊢ᵒ λ FM→N → (redM⇒▷ℰN redM FM→N)))
    where
    progressMred : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred =
       let redFM : (reducible M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ Zᵒ λ {(M′ , M→M′) → _ , (ξ F M→M′)} in
       inj₂ᵒ (inj₁ᵒ redFM)

    redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N)
       → 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    redM⇒▷ℰN {N} rM FM→N =
         let finv = frame-inv2{M}{N}{F} rM FM→N in
         let M′ = proj₁ finv in
         let M→M′ = proj₁ (proj₂ finv) in
         let N≡ = proj₂ (proj₂ finv) in

         let IH : 𝓟′ ⊢ᵒ ▷ᵒ ℰ-frame-prop A B F
             IH = Sᵒ (Sᵒ Zᵒ) in
         let ℰM : 𝓟′ ⊢ᵒ ℰ⟦ B ⟧ M
             ℰM = Sᵒ Zᵒ in
         let ▷ℰM′ : 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
             ▷ℰM′ = appᵒ (instᵒ{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                           (ℰ-preservation ℰM) M′)
                         (⊢ᵒ-Sᵒ-intro M→M′) in
         let M→V→𝒱V→ℰFV : 𝓟′ ⊢ᵒ ℰ-f-cont A B F M
             M→V→𝒱V→ℰFV = Zᵒ in
         let M′→V→𝒱V→ℰFV : 𝓟′ ⊢ᵒ ℰ-f-cont A B F M′
             M′→V→𝒱V→ℰFV = ℰ-f-cont-lemma{𝓟′}{A}{B} M→M′ M→V→𝒱V→ℰFV in
         let ▷ℰFM′ : 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
             ▷ℰFM′ = frame-prop-lemma IH ▷ℰM′ (⊢ᵒ-mono M′→V→𝒱V→ℰFV) in
         subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡) ▷ℰFM′

   Mblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mblame = ℰ-intro progressMblame
            (Sᵒ⊢ᵒ λ blameM → Λᵒ[ N ]
               →ᵒI (Sᵒ⊢ᵒ λ FM→N → blameM⇒▷ℰN blameM FM→N))
    where
    progressMblame : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMblame =
       let redFM : (Blame M)ᵒ ∷ 𝓟′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = Sᵒ→Tᵒ⇒⊢ᵒ Zᵒ λ {isBlame → _ , (ξ-blame F)} in
       inj₂ᵒ (inj₁ᵒ redFM)

    blameM⇒▷ℰN : ∀{N} → Blame M → (F ⟦ M ⟧ —→ N)
       → 𝓟′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    blameM⇒▷ℰN {N} isBlame FM→N =
        let eq = blame-frame FM→N in
        subst (λ N → 𝓟′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym eq) (⊢ᵒ-mono ℰ-blame)


ℰ-frame : ∀{𝓟}{A}{B}{F}{M}
   → 𝓟 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝓟 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
     ----------------------------------------------------------
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-frame {𝓟}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{𝓟}{P = λ M → ℰ-fp A B F M} ℰ-frame-aux M)
             ⊢ℰM)
       ⊢𝒱V→ℰFV

{- The following lemma is currently not used. -}
exp-▷ : ∀{𝓟}{A}{M N : Term}
   → 𝓟 ⊢ᵒ (M —→ N)ᵒ
   → 𝓟 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
     -------------------
   → 𝓟 ⊢ᵒ ℰ⟦ A ⟧ M
exp-▷{𝓟}{A}{M}{N} 𝓟⊢M→N ⊢▷ℰN =
  substᵒ (≡ᵒ-sym (ℰ-stmt{A}{M})) Goal 
  where
  redM : 𝓟 ⊢ᵒ reducible M ᵒ
  redM = Sᵒ→Tᵒ⇒⊢ᵒ 𝓟⊢M→N λ M→N → _ , M→N

  ⊢prog : 𝓟 ⊢ᵒ progress A M
  ⊢prog = inj₂ᵒ{𝓟}{𝒱⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
            (inj₁ᵒ{𝓟}{(reducible M)ᵒ}{(Blame M)ᵒ} redM)
          
  ⊢pres : 𝓟 ⊢ᵒ preservation A M
  ⊢pres = ⊢ᵒ-∀-intro {P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))}
      λ N′ → ⊢ᵒ-intro
        λ { zero ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝓟n (suc j) (s≤s j≤n) M→N′ →
              let ⊨𝓟sj = (downClosed-Πᵒ 𝓟 (suc n) ⊨𝓟n (suc j) (s≤s j≤n)) in
              subst (λ X → # (ℰ⟦ A ⟧ X) j)
                  (deterministic (((⊢ᵒ-elim 𝓟⊢M→N) (suc j) ⊨𝓟sj)) M→N′)
                  ((⊢ᵒ-elim ⊢▷ℰN) (suc j) ⊨𝓟sj)}
          
  Goal : 𝓟 ⊢ᵒ progress A M ×ᵒ preservation A M
  Goal = ⊢prog ,ᵒ ⊢pres

