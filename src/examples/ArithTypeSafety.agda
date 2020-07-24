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

𝑉 : List Type → Var → Type → Type → Set
𝑉 Γ x A B = A ≡ B

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
             ; ret-pres = λ x → x ; shift-⊢v = shift-⊢v
             ; 𝑉-⊢v = λ { refl ⊢v⦂ → ⊢v⦂ } ; prev-𝑉 = λ x → x }

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
type-safety M ⊢M = fold-preserves ⊢M (λ ()) op-pres
