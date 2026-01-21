{-# OPTIONS --without-K #-}

module finite-decidable-families where

open import agda-unimath-deps

abstract
  everyone-or-witness :
      (n : ℕ)
    → (F : Fin n → UU)
    → (∀ i → is-decidable (F i))
    → (∀ i → F i) + (Σ (Fin n) λ i → ¬ (F i))
  everyone-or-witness zero-ℕ F dec-F = inl λ ()
  everyone-or-witness (succ n) F dec-F
    with dec-F (inr star)
  ... | inr ¬FSn = inr (inr star , ¬FSn)
  ... | inl FSn
      with everyone-or-witness n (F ∘ inl) (dec-F ∘ inl)
  ...    | inr (i , ¬Fi) = inr (inl i , ¬Fi)
  ...    | inl ∀i≤n-Fi = inl ∀iFi
        where
          ∀iFi : ∀ i → F i
          ∀iFi (inr star) = FSn
          ∀iFi (inl i) = ∀i≤n-Fi i

abstract
  is-decidable-total-family :
      (n : ℕ)
    → (F : Fin n → UU)
    → (∀ i → is-decidable (F i))
    → is-decidable (∀ i → F i)
  is-decidable-total-family n F dec-F
    with everyone-or-witness n F dec-F
  ... | inr (i , ¬Fi) = inr (λ ∀F → ¬Fi (∀F i))
  ... | inl ∀F = inl ∀F
