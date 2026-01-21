{-# OPTIONS --flat-split #-}

module pasting-schemes-array.pasting-schemes-array-maps-properties where

open import agda-unimath-deps
open import utilities

open import pasting-schemes-array.pasting-schemes-array
open import pasting-schemes-array.pasting-schemes-array-maps
open import pasting-schemes-array.pasting-schemes-array-maps-composition
open import celltt-arrays
open import finite-ords

-- suspended morphisms preserves left and right points

leftpoint-coh : {P Q : PS} → (σ : P →PS Q) →
  ($→ σ) ∘PS leftpoint ($ P) ＝ leftpoint ($ Q)
leftpoint-coh {cons(n , P)} {cons(m , Q)} (f , δ)
  = eq-pair-Σ
      refl
      ( eq-htpy λ _
      → eq-htpy λ () )

rightpoint-coh : {P Q : PS} → (σ : P →PS Q) →
  ($→ σ) ∘PS rightpoint ($ P) ＝ rightpoint ($ Q)
rightpoint-coh {cons(n , P)} {cons(m , Q)} (f , δ)
  = eq-pair-Σ
      refl
      ( eq-htpy λ _
      → eq-htpy λ () )

-- the leftpoint of the i-th subshape inclusion is the i-th point

leftpoint-subshape-inclusion :
    ((n , P) : array PS)
  → (i : Fin n)
  → subshape-inclusion (n , P) i ∘PS leftpoint ($ (P i))
    ＝ pick-point (cons(n , P)) (inl i)
leftpoint-subshape-inclusion (n , P) i
  = eq-pair-Σ refl (eq-htpy λ _ → eq-htpy λ ())

-- the rightpoint of the i-th subshape inclusion is the (i+1)-th point

rightpoint-subshape-inclusion :
    ((n , P) : array PS)
  → (i : Fin n)
  → subshape-inclusion (n , P) i ∘PS rightpoint ($ (P i))
    ＝ pick-point (cons(n , P)) (succ-Fin (1+ n) (inl i))
rightpoint-subshape-inclusion (n , P) i
  = eq-pair-Σ refl (eq-htpy λ _ → eq-htpy λ ())

-- there is a commuting commuting square
--
--   ∗ -------- left -----> $(P(i+1))
--   |                           |
--  right                      ⊆(i+1)
--   |                           |
--   v                           v
-- $(P(i)) ----- ⊆(i) -------> P !! Ps

left-right-subshape :
    (n : ℕ)
  → (P : Fin (1+ n) → PS)
  → (i : Fin n)
  → let Si = (succ-Fin (1+ n) (inl i)) in
    subshape-inclusion (1+ n , P) (inl i) ∘PS rightpoint ($ (P (inl i)))
    ＝ subshape-inclusion (1+ n , P) Si ∘PS leftpoint ($ (P Si))
left-right-subshape n P i =
  eq-pair-Σ refl (eq-htpy λ _ → eq-htpy λ ())

-- compressing maps

is-compr :
    {P Q : PS}
  → (P →PS Q)
  → UU
is-compr {cons(n , P)} {cons(m , Q)} (f , δ) =
    -- f(Sn) ≤ f(0)
  leq-Fin (1+ m) (pr1 f (inr star)) (succ-Fin (1+ m) (pr1 f (zero-Fin n)))
  × -- recursive condition
  ∀ k i p → is-compr (δ k i p)

abstract
  is-prop-is-compr :
      {P Q : PS}
    → (σ : P →PS Q)
    → is-prop (is-compr σ)
  is-prop-is-compr {cons(n , P)} {cons(m , Q)} (f , δ) =
    is-prop-product
      ( is-prop-leq-Fin (1+ m)
          (pr1 f (inr star))
          (succ-Fin (1+ m) (pr1 f (zero-Fin n)))
      )
      ( is-prop-Π λ k →
        is-prop-Π λ i →
        is-prop-Π λ p →
          is-prop-is-compr (δ k i p)
      )

abstract
  has-decidable-equality-→PS : (P Q : PS) → has-decidable-equality (P →PS Q)
  has-decidable-equality-→PS (cons (n , P)) (cons (m , Q)) =
    has-decidable-equality-Σ
      (has-decidable-equality→≤ n m)
      has-decidable-equality'
    where private
      has-decidable-equality'' :
          ∀ (f : [ n ] →≤ [ m ])
        → ∀ (k : Fin m)
        → ∀ (i : Fin n)
        → has-decidable-equality (dual n m f k ＝ in-Fin i → P i →PS Q k)
      has-decidable-equality'' f k i
        with has-decidable-equality-Fin++ n (dual n m f k) (in-Fin i)
      ... | inl dual=in-Fin = has-decidable-equality-equiv equiv3
              (has-decidable-equality-Fin-maps 1 (λ _ →  P i →PS Q k)
              λ _ → has-decidable-equality-→PS (P i) (Q k))
            where
              equiv1 : Id (dual n m f k) (in-Fin i) ≃ ⊤
              equiv1 = equiv-unit-is-contr
                (is-proof-irrelevant-is-prop
                  (is-set-Fin++ n _ _)
                  dual=in-Fin)
              equiv2 : ⊤ ≃ Fin 1
              equiv2 = inv-equiv equiv-Fin-one-ℕ
              equiv3 :
                ((dual n m f k ＝ in-Fin i) → P i →PS Q k)
                ≃ (Fin 1 → P i →PS Q k)
              equiv3 = equiv-function-type (P i →PS Q k)
                (equiv2 ∘e equiv1) id-equiv
      ... | inr dual≠in-Fin =
              λ ϕ ψ → inl
                (eq-htpy {f = ϕ} {g = ψ} (λ p → ex-falso (dual≠in-Fin p)))

      has-decidable-equality' : (f : [ n ] →≤ [ m ])
        → has-decidable-equality
          ((k : Fin m) (i : Fin n) → dual n m f k ＝ in-Fin i → P i →PS Q k)
      has-decidable-equality' f = has-decidable-equality-Fin-maps m
        (λ k → (i : Fin n) → dual n m f k ＝ in-Fin i → P i →PS Q k)
        λ k → has-decidable-equality-Fin-maps n
          (λ i → dual n m f k ＝ in-Fin i → P i →PS Q k)
          λ i → has-decidable-equality'' f k i

abstract
  is-set-→PS : (P Q : PS) → is-set (P →PS Q)
  is-set-→PS P Q = is-set-has-decidable-equality (has-decidable-equality-→PS P Q)
