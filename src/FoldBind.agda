{-# OPTIONS --cumulativity #-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List using (List; []; _∷_)
open import Sig

module FoldBind (Op : Set) (sig : Op → List Sig) where


