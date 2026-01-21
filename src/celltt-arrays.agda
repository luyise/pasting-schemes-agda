{-# OPTIONS --without-K #-}

module celltt-arrays where

open import lists.arrays
  public
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import elementary-number-theory.natural-numbers
  renaming (succ-ℕ to succ)

replicate : (n : ℕ) → {A : UU} → A → array A
replicate n a = (n , λ _ → a)
