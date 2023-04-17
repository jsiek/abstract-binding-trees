{-# OPTIONS --rewriting #-}
module rewriting.examples.CastLogRelLogic2 where

open import Data.List using (List; []; _∷_; length)
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
open import rewriting.examples.CastDeterministic
open import rewriting.examples.StepIndexedLogic2

ℰ⊎𝒱-type : Set
ℰ⊎𝒱-type = (Type × Term) ⊎ (Type × Term)

ℰ⊎𝒱-ctx : Context
ℰ⊎𝒱-ctx = ℰ⊎𝒱-type ∷ []

ℰˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
ℰˢ⟦ A ⟧ M = (inj₂ (A , M)) ∈ zeroˢ

𝒱ˢ⟦_⟧ : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Now ∅)
𝒱ˢ⟦ A ⟧ V = (inj₁ (A , V)) ∈ zeroˢ

pre-𝒱 : Type → Term → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-𝒱 ★ (V ⟨ G !⟩ )  = (Value V)ˢ ×ˢ ▷ˢ (𝒱ˢ⟦ gnd⇒ty G ⟧ V)
pre-𝒱 ($ₜ ι) ($ c)        = (ι ≡ typeof c)ˢ
pre-𝒱 (A ⇒ B) (ƛ N)      = ∀ˢ[ W ] ▷ˢ (𝒱ˢ⟦ A ⟧ W) →ˢ ▷ˢ (ℰˢ⟦ B ⟧ (N [ W ]))
pre-𝒱 A M                = ⊥ ˢ

-- Type Safety = Progress & Preservation
pre-ℰ : Type → Term
       → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ A M = (pre-𝒱 A M ⊎ˢ (reducible M)ˢ ⊎ˢ (Blame M)ˢ)    -- Progress
             ×ˢ (∀ˢ[ N ] (M —→ N)ˢ →ˢ ▷ˢ (ℰˢ⟦ A ⟧ N))        -- Preservation

pre-ℰ⊎𝒱 : ℰ⊎𝒱-type → Setˢ ℰ⊎𝒱-ctx (cons Later ∅)
pre-ℰ⊎𝒱 (inj₁ (A , V)) = pre-𝒱 A V
pre-ℰ⊎𝒱 (inj₂ (A , M)) = pre-ℰ A M

ℰ⊎𝒱 : ℰ⊎𝒱-type → Setᵒ
ℰ⊎𝒱 X = μᵒ pre-ℰ⊎𝒱 X

-- Semantically Well Typed Value
𝒱⟦_⟧ : (A : Type) → Term → Setᵒ
𝒱⟦ A ⟧ V = ℰ⊎𝒱 (inj₁ (A , V))

-- Semantically Well Typed Term
ℰ⟦_⟧ : (A : Type) → Term → Setᵒ
ℰ⟦ A ⟧ M = ℰ⊎𝒱 (inj₂ (A , M))

{-
foo : ∀ (X : ℰ⊎𝒱-type) → Type → Term → ⊤
foo X A M =
   let m = #(μˢ ℰ⊎𝒱 X) ttᵖ in
   let n = #(ℰ⊎𝒱 X) {!!} in
   let x = ℰ⟦ A ⟧ M in
   let fp = ≡ˢ-elim (fixpointˢ {[]}{∅}{ℰ⊎𝒱-type} ℰ⊎𝒱 X) ttᵖ in
   {!!}
-}

ℰ⊎𝒱-fixpointᵒ : ∀ X
   → ℰ⊎𝒱 X ≡ᵒ # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)
ℰ⊎𝒱-fixpointᵒ X = fixpointᵒ pre-ℰ⊎𝒱 X 

progress : Type → Term → Setᵒ
progress A M = (𝒱⟦ A ⟧ M) ⊎ᵒ (reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ

preservation : Type → Term → Setᵒ
preservation A M = (∀ᵒ[ N ] ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)))

ℰ-stmt : ∀{A}{M}
  → ℰ⟦ A ⟧ M ≡ᵒ progress A M ×ᵒ preservation A M
ℰ-stmt {A}{M} =
  ℰ⟦ A ⟧ M                                                  ⩦⟨ ≡ᵒ-refl refl ⟩
  μᵒ pre-ℰ⊎𝒱 (inj₂ (A , M))              ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 (inj₂ (A , M)) ⟩
  # (pre-ℰ⊎𝒱 (inj₂ (A , M))) (ℰ⊎𝒱 , ttᵖ)
              ⩦⟨ cong-×ᵒ (cong-⊎ᵒ (≡ᵒ-sym (fixpointᵒ pre-ℰ⊎𝒱 (inj₁ (A , M))))
                                  (≡ᵒ-refl refl)) (≡ᵒ-refl refl) ⟩
  progress A M ×ᵒ preservation A M
  ∎

ℰ-progress : ∀ {𝒫}{A}{M}
  → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝒫 ⊢ᵒ progress A M
ℰ-progress 𝒫⊢ℰM = proj₁ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )

ℰ-preservation : ∀ {𝒫}{A}{M}
  → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
  → 𝒫 ⊢ᵒ preservation A M
ℰ-preservation 𝒫⊢ℰM = proj₂ᵒ (substᵒ ℰ-stmt 𝒫⊢ℰM )

ℰ-intro : ∀ {𝒫}{A}{M}
  → 𝒫 ⊢ᵒ progress A M
  → 𝒫 ⊢ᵒ preservation A M
    ----------------------
  → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
ℰ-intro 𝒫⊢prog 𝒫⊢pres = substᵒ (≡ᵒ-sym (ℰ-stmt)) (𝒫⊢prog ,ᵒ 𝒫⊢pres)

𝒱-base : ∀{ι}{c : Lit} → (𝒱⟦ $ₜ ι ⟧ ($ c)) ≡ᵒ (ι ≡ typeof c)ᵒ
𝒱-base = ≡ᵒ-intro λ k → (λ x → x) , (λ x → x)

𝒱-base-intro : ∀{𝒫}{ι}{c : Lit}
   → 𝒫 ⊢ᵒ (ι ≡ typeof c)ᵒ
     -----------------------
   → 𝒫 ⊢ᵒ (𝒱⟦ $ₜ ι ⟧ ($ c))
𝒱-base-intro{𝒫}{ι}{c} ⊢ι≡tyc = substᵒ (≡ᵒ-sym 𝒱-base) ⊢ι≡tyc

𝒱-base-elim : ∀{𝒫}{ι}{c : Lit}{R}
   → 𝒫 ⊢ᵒ (𝒱⟦ $ₜ ι ⟧ ($ c))
   → (ι ≡ typeof c → 𝒫 ⊢ᵒ R)
     -----------------------
   → 𝒫 ⊢ᵒ R
𝒱-base-elim ⊢𝒱c cont = ⊢ᵒ-sucP ⊢𝒱c λ {n} 𝒱csn → cont 𝒱csn

𝒱-dyn : ∀{G}{V} → 𝒱⟦ ★ ⟧ (V ⟨ G !⟩) ≡ᵒ ((Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ V))
𝒱-dyn {G}{V} =
   let X = (inj₁ (★ , V ⟨ G !⟩)) in
   𝒱⟦ ★ ⟧ (V ⟨ G !⟩)                              ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                 ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                  ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (Value V)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ V)       ∎

𝒱-dyn-intro : ∀{𝒫}{G}{V}
   → 𝒫 ⊢ᵒ (Value V)ᵒ
   → 𝒫 ⊢ᵒ ▷ᵒ 𝒱⟦ gnd⇒ty G ⟧ V
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ ⟧ (V ⟨ G !⟩)
𝒱-dyn-intro ⊢v ⊢𝒱V = substᵒ (≡ᵒ-sym 𝒱-dyn)  (⊢v ,ᵒ ⊢𝒱V)

𝒱⇒Value : ∀ {k} A M
   → # (𝒱⟦ A ⟧ M) (suc k)
     ---------------------
   → Value M
𝒱⇒Value ★ (M ⟨ G !⟩) (v , _) = v 〈 G 〉
𝒱⇒Value ($ₜ ι) ($ c) 𝒱M = $̬ c
𝒱⇒Value (A ⇒ B) (ƛ N) 𝒱M = ƛ̬ N

𝒱-dyn-elim : ∀{𝒫}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ ★ ⟧ V
   → (∀ W G → V ≡ W ⟨ G !⟩
             → 𝒫 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ W))
             → 𝒫 ⊢ᵒ R)
     ----------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-dyn-elim {𝒫}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G 𝒱Vsn ⊢𝒱V cont }
  where
  G : ∀{V}{n}
      → # (𝒱⟦ ★ ⟧ V) (suc n)
      → 𝒫 ⊢ᵒ 𝒱⟦ ★ ⟧ V
      → (∀ W G → V ≡ W ⟨ G !⟩
               → 𝒫 ⊢ᵒ ((Value W)ᵒ ×ᵒ ▷ᵒ (𝒱⟦ gnd⇒ty G ⟧ W))
               → 𝒫 ⊢ᵒ R)
      → 𝒫 ⊢ᵒ R
  G {W ⟨ G !⟩}{n} 𝒱Vsn ⊢𝒱V cont
      with 𝒱⇒Value ★ (W ⟨ G !⟩) 𝒱Vsn
  ... | w 〈 _ 〉 =
      let ⊢▷𝒱W = proj₂ᵒ (substᵒ (𝒱-dyn{V = W}) ⊢𝒱V) in
      cont W _ refl (constᵒI w ,ᵒ ⊢▷𝒱W)
  
𝒱-fun : ∀{A B}{N}
   → (𝒱⟦ A ⇒ B ⟧ (ƛ N))
      ≡ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
𝒱-fun {A}{B}{N} =
   let X = (inj₁ (A ⇒ B , ƛ N)) in
   𝒱⟦ A ⇒ B ⟧ (ƛ N)                                         ⩦⟨ ≡ᵒ-refl refl ⟩
   ℰ⊎𝒱 X                                         ⩦⟨ fixpointᵒ pre-ℰ⊎𝒱 X ⟩
   # (pre-ℰ⊎𝒱 X) (ℰ⊎𝒱 , ttᵖ)                            ⩦⟨ ≡ᵒ-refl refl ⟩ 
   (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
   ∎

𝒱-fun-intro : ∀{𝒫}{A}{B}{N}
  → 𝒫 ⊢ᵒ (∀ᵒ[ W ] ((▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))))
    -------------------------------------------------------------
  → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ (ƛ N)
𝒱-fun-intro {𝒫}{A}{B}{V} 𝒱W→ℰNW = (substᵒ (≡ᵒ-sym 𝒱-fun) 𝒱W→ℰNW)

𝒱-fun-elim : ∀{𝒫}{A}{B}{V}{R}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
   → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝒫 ⊢ᵒ R)
     --------------------------------------------------------------------
   → 𝒫 ⊢ᵒ R
𝒱-fun-elim {𝒫}{A}{B}{V}{R} ⊢𝒱V cont =
  ⊢ᵒ-sucP ⊢𝒱V λ { 𝒱Vsn → G {V} 𝒱Vsn ⊢𝒱V cont}
  where
  G : ∀{V}{n}
     → # (𝒱⟦ A ⇒ B ⟧ V) (suc n)
     → 𝒫 ⊢ᵒ 𝒱⟦ A ⇒ B ⟧ V
     → (∀ N → V ≡ ƛ N
             → (∀{W} → 𝒫 ⊢ᵒ (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ]))))
             → 𝒫 ⊢ᵒ R)
     → 𝒫 ⊢ᵒ R
  G{ƛ N}{n} 𝒱V ⊢𝒱V cont = cont N refl λ {W} →
      instᵒ{P = λ W → (▷ᵒ (𝒱⟦ A ⟧ W)) →ᵒ (▷ᵒ (ℰ⟦ B ⟧ (N [ W ])))}
                 (substᵒ 𝒱-fun ⊢𝒱V) W

ℰ-blame : ∀{𝒫}{A} → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ blame
ℰ-blame {𝒫}{A} =
    ℰ-intro (inj₂ᵒ (inj₂ᵒ (constᵒI isBlame)))
        (Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ blame→N → ⊥-elim (blame-irreducible blame→N)))

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

𝒱⇒ℰ : ∀{A}{𝒫}{V}
   → 𝒫 ⊢ᵒ 𝒱⟦ A ⟧ V
     ---------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ V
𝒱⇒ℰ {A}{𝒫}{V} 𝒫⊢𝒱V =
    ⊢ᵒ-intro
    λ n ⊨𝒫n →
    let 𝒱V = (⊢ᵒ-elim 𝒫⊢𝒱V) n ⊨𝒫n in
    (inj₁ 𝒱V) , λ { N zero x V→N → tt ;
                     N (suc j) (s≤s j≤) V→N →
                         ⊥-elim (value-irreducible (𝒱⇒Value A V 𝒱V) V→N)}

{- ℰ-bind (Monadic Bind Lemma) -}

𝒱V→ℰF[V] : Type → Type → Frame → Term → Setᵒ
𝒱V→ℰF[V] A B F M = ∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)

ℰ-fp : Type → Type → Frame → Term → Setᵒ
ℰ-fp A B F M = ℰ⟦ B ⟧ M →ᵒ 𝒱V→ℰF[V] A B F M →ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)

ℰ-bind-prop : Type → Type → Frame → Setᵒ
ℰ-bind-prop A B F = ∀ᵒ[ M ] ℰ-fp A B F M

frame-prop-lemma : ∀{𝒫}{A}{B}{M}{F}
   → 𝒫 ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
   → 𝒫 ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ ▷ᵒ 𝒱V→ℰF[V] A B F M
   → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M ⟧))
frame-prop-lemma{𝒫}{A}{B}{M}{F} IH ℰM V→FV =
  appᵒ (▷→ (appᵒ (▷→ (instᵒ (▷∀{P = λ M → ℰ-fp A B F M} IH) M)) ℰM)) V→FV

𝒱V→ℰF[V]-expansion : ∀{𝒫}{A}{B}{F}{M}{M′}
   → M —→ M′
   → 𝒫 ⊢ᵒ 𝒱V→ℰF[V] A B F M
     -----------------------
   → 𝒫 ⊢ᵒ 𝒱V→ℰF[V] A B F M′
𝒱V→ℰF[V]-expansion {𝒫}{A}{B}{F}{M}{M′} M→M′ 𝒱V→ℰF[V][M] =
   Λᵒ[ V ]
    let M′→V→ℰFV : 𝒱⟦ B ⟧ V ∷ (M′ —↠ V)ᵒ ∷ 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧)
        M′→V→ℰFV = ⊢ᵒ-sucP (Sᵒ Zᵒ) λ M′→V → 
                     let M—↠V = constᵒI (M —→⟨ M→M′ ⟩ M′→V) in
                     let M→V→ℰFV = ⊢ᵒ-weaken(⊢ᵒ-weaken(instᵒ 𝒱V→ℰF[V][M] V)) in
                     appᵒ (appᵒ M→V→ℰFV M—↠V) Zᵒ in
    →ᵒI (→ᵒI M′→V→ℰFV)

ℰ-bind-aux : ∀{𝒫}{A}{B}{F} → 𝒫 ⊢ᵒ ℰ-bind-prop A B F
ℰ-bind-aux {𝒫}{A}{B}{F} = lobᵒ Goal
 where     
 Goal : ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫 ⊢ᵒ ℰ-bind-prop A B F
 Goal = Λᵒ[ M ] →ᵒI (→ᵒI Goal′)
  where
  Goal′ : ∀{M}
     → (𝒱V→ℰF[V] A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫
        ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
  Goal′{M} =
   let ⊢ℰM : 𝒫′ ⊢ᵒ ℰ⟦ B ⟧ M
       ⊢ℰM = Sᵒ Zᵒ in
   case3ᵒ (ℰ-progress ⊢ℰM) Mval Mred Mblame
   where
   𝒫′ = (𝒱V→ℰF[V] A B F M) ∷ ℰ⟦ B ⟧ M ∷ ▷ᵒ ℰ-bind-prop A B F ∷ 𝒫

   Mval : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mval =
     let ⊢𝒱M : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ 𝒱⟦ B ⟧ M
         ⊢𝒱M = Zᵒ in
     let ℰcontFM : 𝒱⟦ B ⟧ M ∷ 𝒫′ ⊢ᵒ 𝒱V→ℰF[V] A B F M
         ℰcontFM = Sᵒ Zᵒ in
     let Cont = λ V → (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧) in
     appᵒ (appᵒ (instᵒ{P = Cont} ℰcontFM M)
                          (constᵒI (M END)))
               ⊢𝒱M

   Mred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mred = ℰ-intro progressMred
            (constᵒE Zᵒ λ redM →
               ⊢ᵒ-weaken (Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ FM→N →
                                           (⊢ᵒ-weaken (redM⇒▷ℰN redM FM→N)))))
    where
    progressMred : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMred =
       let redFM : (reducible M)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = constᵒE Zᵒ λ {(M′ , M→M′) → constᵒI (_ , (ξ F M→M′))} in
       inj₂ᵒ (inj₁ᵒ redFM)

    redM⇒▷ℰN : ∀{N} → reducible M → (F ⟦ M ⟧ —→ N)
       → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    redM⇒▷ℰN {N} rM FM→N =
         let finv = frame-inv2{M}{N}{F} rM FM→N in
         let M′ = proj₁ finv in
         let M→M′ = proj₁ (proj₂ finv) in
         let N≡ = proj₂ (proj₂ finv) in

         let IH : 𝒫′ ⊢ᵒ ▷ᵒ ℰ-bind-prop A B F
             IH = Sᵒ (Sᵒ Zᵒ) in
         let ℰM : 𝒫′ ⊢ᵒ ℰ⟦ B ⟧ M
             ℰM = Sᵒ Zᵒ in
         let ▷ℰM′ : 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ B ⟧ M′
             ▷ℰM′ = appᵒ (instᵒ{P = λ N → (M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ B ⟧ N)}
                           (ℰ-preservation ℰM) M′)
                         (constᵒI M→M′) in
         let M→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ 𝒱V→ℰF[V] A B F M
             M→V→𝒱V→ℰFV = Zᵒ in
         let M′→V→𝒱V→ℰFV : 𝒫′ ⊢ᵒ 𝒱V→ℰF[V] A B F M′
             M′→V→𝒱V→ℰFV = 𝒱V→ℰF[V]-expansion{𝒫′}{A}{B} M→M′ M→V→𝒱V→ℰFV in
         let ▷ℰFM′ : 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ (F ⟦ M′ ⟧))
             ▷ℰFM′ = frame-prop-lemma IH ▷ℰM′ (monoᵒ M′→V→𝒱V→ℰFV) in
         subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym N≡) ▷ℰFM′

   Mblame : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
   Mblame = ℰ-intro progressMblame
            (constᵒE Zᵒ λ blameM →
             ⊢ᵒ-weaken (Λᵒ[ N ] →ᵒI (constᵒE Zᵒ λ FM→N →
                                           ⊢ᵒ-weaken (blameM⇒▷ℰN blameM FM→N))))
    where
    progressMblame : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ progress A (F ⟦ M ⟧)
    progressMblame =
       let redFM : (Blame M)ᵒ ∷ 𝒫′ ⊢ᵒ (reducible (F ⟦ M ⟧))ᵒ
           redFM = constᵒE Zᵒ λ {isBlame → constᵒI (_ , (ξ-blame F))} in
       inj₂ᵒ (inj₁ᵒ redFM)

    blameM⇒▷ℰN : ∀{N} → Blame M → (F ⟦ M ⟧ —→ N)
       → 𝒫′ ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
    blameM⇒▷ℰN {N} isBlame FM→N =
        let eq = blame-frame FM→N in
        subst (λ N → 𝒫′ ⊢ᵒ ▷ᵒ ℰ⟦ A ⟧ N) (sym eq) (monoᵒ ℰ-blame)

ℰ-bind : ∀{𝒫}{A}{B}{F}{M}
   → 𝒫 ⊢ᵒ ℰ⟦ B ⟧ M
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] (M —↠ V)ᵒ →ᵒ 𝒱⟦ B ⟧ V →ᵒ ℰ⟦ A ⟧ (F ⟦ V ⟧))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ (F ⟦ M ⟧)
ℰ-bind {𝒫}{A}{B}{F}{M} ⊢ℰM ⊢𝒱V→ℰFV =
  appᵒ (appᵒ (instᵒ{𝒫}{P = λ M → ℰ-fp A B F M} ℰ-bind-aux M)
             ⊢ℰM)
       ⊢𝒱V→ℰFV

{- The following lemma is currently not used. -}
exp-▷ : ∀{𝒫}{A}{M N : Term}
   → 𝒫 ⊢ᵒ (M —→ N)ᵒ
   → 𝒫 ⊢ᵒ ▷ᵒ (ℰ⟦ A ⟧ N)
     -------------------
   → 𝒫 ⊢ᵒ ℰ⟦ A ⟧ M
exp-▷{𝒫}{A}{M}{N} 𝒫⊢M→N ⊢▷ℰN =
  substᵒ (≡ᵒ-sym (ℰ-stmt{A}{M})) Goal 
  where
  redM : 𝒫 ⊢ᵒ reducible M ᵒ
  redM = constᵒE 𝒫⊢M→N λ M→N → constᵒI (_ , M→N)

  ⊢prog : 𝒫 ⊢ᵒ progress A M
  ⊢prog = inj₂ᵒ{𝒫}{𝒱⟦ A ⟧ M}{(reducible M)ᵒ ⊎ᵒ (Blame M)ᵒ}
            (inj₁ᵒ{𝒫}{(reducible M)ᵒ}{(Blame M)ᵒ} redM)
          
  ⊢pres : 𝒫 ⊢ᵒ preservation A M
  ⊢pres = ⊢ᵒ-∀-intro {P = λ N → ((M —→ N)ᵒ →ᵒ ▷ᵒ (ℰ⟦ A ⟧ N))}
      λ N′ → ⊢ᵒ-intro
        λ { zero ⊨𝒫n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝒫n .zero z≤n M→N′ → tt ;
            (suc n) ⊨𝒫n (suc j) (s≤s j≤n) M→N′ →
              let ⊨𝒫sj = (downClosed-Πᵒ 𝒫 (suc n) ⊨𝒫n (suc j) (s≤s j≤n)) in
              subst (λ X → # (ℰ⟦ A ⟧ X) j)
                  (deterministic (((⊢ᵒ-elim 𝒫⊢M→N) (suc j) ⊨𝒫sj)) M→N′)
                  ((⊢ᵒ-elim ⊢▷ℰN) (suc j) ⊨𝒫sj)}
          
  Goal : 𝒫 ⊢ᵒ progress A M ×ᵒ preservation A M
  Goal = ⊢prog ,ᵒ ⊢pres

