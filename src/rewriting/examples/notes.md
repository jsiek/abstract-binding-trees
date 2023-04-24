
There's a lot of freedom in how to define ℰ.
What properties of ℰ does the fundemantal lemma depend on?

𝒱⇒ℰ : ∀{c : Prec}{𝒫}{V V′}
   → 𝒫 ⊢ᵒ 𝒱⟦ c ⟧ V V′
     -----------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ V V′

ℰ-blame : ∀{𝒫}{c}{M} → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ M blame

ℰ-bind : ∀{𝒫}{c d : Prec}{F}{F′}{M}{M′}
   → 𝒫 ⊢ᵒ ℰ⟦ d ⟧ M M′ 
   → 𝒫 ⊢ᵒ (∀ᵒ[ V ] ∀ᵒ[ V′ ] (M —↠ V)ᵒ →ᵒ (M′ —↠ V′)ᵒ
              →ᵒ 𝒱⟦ d ⟧ V V′ →ᵒ ℰ⟦ c ⟧ (F ⦉ V ⦊) (F′ ⦉ V′ ⦊))
     ----------------------------------------------------------
   → 𝒫 ⊢ᵒ ℰ⟦ c ⟧ (F ⦉ M ⦊) (F′ ⦉ M′ ⦊)

compatibility




--------------------------------------------------------------------
lemma15a  (change initial P to Q)
      ↓ᵒ j (iter j (toFun δ F) P a)
   ≡ᵒ ↓ᵒ j (iter j (toFun δ F) Q a)

lemma15b (increase iterations)
  j ≤ k → 
     ↓ᵒ j (iter j (toFun δ F) P a)
  ≡ᵒ ↓ᵒ j (iter k (toFun δ F) P a)

lemma18a (mu to iter)
      ↓ᵒ k (muˢ F δ a) 
   ≡ᵒ ↓ᵒ k (iter k (toFun δ F) ⊤ᵖ a)

lemma18b (unrolled mu to iter + 1)
      ↓ᵒ (suc j) (# (F a) (muˢ F δ , δ))
   ≡ᵒ ↓ᵒ (suc j) (iter (suc j) (toFun δ F) ⊤ᵖ a)

lemma17  (↓ᵖ is idempotent)
      ↓ᵖ k (↓ᵖ (suc k) P) a ≡ᵒ ↓ᵖ k P a

lemma17c
   j < k →
   ↓ᵖ j (↓ᵖ k P) a ≡ᵒ ↓ᵖ j P a

lemma19a (unroll mu and toFun)
      ↓ᵒ j (muˢ F δ a) ≡ᵒ ↓ᵒ j (# (F a) (muˢ F δ , δ))

--------------------------------------------------------------------
  ↓ᵒ k′ (muˢ S δ) a 
= ↓ᵒ k′ (# (S a) (muˢ S δ , δ))      by lemma19a
?
= ↓ᵒ k′ (# (S a) (muˢ S (↓ᵈ k x δ) , (↓ᵈ k x δ)))   by lemma19a
= ↓ᵖ k′ (muˢ S (↓ᵈ k x δ)) a
--------------------------------------------------------------------

↓ᵒ k (muˢ S δ a)                     lemma18a
↓ᵒ k (iter k (toFun δ S) ⊤ᵖ a)

             (λ P a → # (S a) (P, δ))

↓ᵒ k (iter k (toFun (↓ᵈ k x δ) S) ⊤ᵖ a)       lemma18a
↓ᵒ k (muˢ S (↓ᵈ k x δ) a)

 
X[1] = # (S a) (⊤ᵖ , δ)
X[2] = # (S a) (X[1] , δ)
X[3] = # (S a) (X[2] , δ)
...
X[k] = # (S a) (X[k-1] , δ)
     = iter k (toFun δ S) ⊤ᵖ a

  ↓ᵒ k (iter k (toFun δ S) ⊤ᵖ a)
= ↓ᵒ k (# (S a) (X[k-1] , δ))
= ↓ᵒ k (# (S a) (↓ᵒ (k-1) X[k-1] , δ))
= ↓ᵒ k (# (S a) (↓ᵒ (k-1) (# (S a) (↓ᵒ (k-2) X[k-2] , δ)) , δ))
...
= ↓ᵒ k (# (S a) ... (↓ᵒ 1 (# (S a) (⊤ᵖ , δ)) , δ) ...)

  iter k (toFun δ S) ⊤ᵖ a
= iter k F[S,a] ⟨ ⊤ᵖ , δ ⟩

  ↓ᵒ k (iter k (toFun δ S) ⊤ᵖ a)            def. F[S,a]
= ↓ᵒ k (iter k F[S,a] ⟨ ⊤ᵖ , δ ⟩)           lemma15a
= ↓ᵒ k (iter k F[S,a] ⟨ ⊤ᵖ , ↓ᵈ k x δ ⟩)    def. F[S,a]
= ↓ᵒ k (iter k (toFun (↓ᵈ k x δ) S) ⊤ᵖ a)

F[S,a] ⟨X,D⟩ = ⟨# (S a) (X,D) , D⟩


