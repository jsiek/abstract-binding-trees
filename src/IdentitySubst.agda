open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)

module IdentitySubst (Op : Set) (sig : Op → List ℕ) where

