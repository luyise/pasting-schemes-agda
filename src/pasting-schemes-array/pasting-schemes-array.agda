{-# OPTIONS --flat-split #-}

module pasting-schemes-array.pasting-schemes-array where

open import agda-unimath-deps

open import celltt-arrays
open import finite-ords
open import finite-decidable-families

-- defining the type (set) of pasting schemes

data PS : UU where
  cons : array PS → PS

∗ : PS
∗ = cons (0 , λ ())

-- length of a pasting scheme

PS-len : PS → ℕ
PS-len (cons (n , _)) = n
PS-vec : (P : PS) → Fin (PS-len P) → PS
PS-vec (cons (_ , P)) = P

-- suspension of pasting schemes

$ : PS → PS
$ P = cons (1 , λ _ → P)

iter-$ : (n : ℕ) → PS → PS
iter-$ 0 = id
iter-$ (succ n) = $ ∘ (iter-$ n)

-- defining some pasting schemes

𝑂 : ℕ → PS
𝑂 n = iter-$ n ∗

𝑂₀ : PS
𝑂₀ = 𝑂 0

𝑂₁ : PS
𝑂₁ = 𝑂 1

𝑂₂ : PS
𝑂₂ = 𝑂 2

Δ : ℕ → PS
Δ n = cons (replicate n ∗)

Δ₀ : PS
Δ₀ = Δ 0

Δ₁ : PS
Δ₁ = Δ 1

Δ₂ : PS
Δ₂ = Δ 2

-- The type of pasting schemes has decidable equality, and is a set.

abstract
  uncons-PS-Id : ∀ {n} {m} {P} {Q}
    → cons(n , P) ＝ cons(m , Q)
    → (n , P) ＝ (m , Q)
  uncons-PS-Id refl = refl

abstract
  has-decidable-equality-PS : has-decidable-equality PS
  has-decidable-equality-PS (cons(n , P)) (cons (m , Q))
    with has-decidable-equality-ℕ n m
  ... | inr n≠m = inr Neq
      where
        Neq : ¬ (cons(n , P) ＝ cons(m , Q))
        Neq Eq = n≠m (ap pr1 (uncons-PS-Id Eq))
  has-decidable-equality-PS (cons(n , P)) (.cons(n , Q)) | inl refl
      with everyone-or-witness n (λ i → P i ＝ Q i) (λ i → has-decidable-equality-PS (P i) (Q i))
  ...   | inr (i , Pi≠Qi) = inr Neq
        where
          Neq : ¬ (cons(n , P) ＝ cons(n , Q))
          Neq Eq = Pi≠Qi (ap (ev i) (inv trP=P ∙ trP=Q))
            where
              nP=nQ : Id {A = array PS} (n , P) (n , Q)
              nP=nQ = uncons-PS-Id Eq
              -- trP=Q :
              -- trP=Q
              trP=Q : (tr (λ c → Fin (pr1 c) → PS) (uncons-PS-Id Eq) P) ＝ Q
              trP=Q = apd pr2 nP=nQ
              trP=P : (tr (λ c → Fin (pr1 c) → PS) (uncons-PS-Id Eq) P) ＝ P
              trP=P
                rewrite inv
                  (substitution-law-tr (λ k → Fin k → PS) pr1 nP=nQ {P})
                rewrite center (is-set-ℕ n n (ap pr1 nP=nQ) refl)
                = refl
  ...   | inl ∀iPi=Qi = inl (ap (λ X → cons(n , X)) (eq-htpy ∀iPi=Qi))

abstract
  is-set-PS : is-set PS
  is-set-PS = is-set-has-decidable-equality (has-decidable-equality-PS)
