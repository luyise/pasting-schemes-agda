{-# OPTIONS --flat-split #-}

module pasting-schemes-array.pasting-schemes-array-maps where

open import agda-unimath-deps

open import pasting-schemes-array.pasting-schemes-array
open import celltt-arrays
open import finite-ords
open import utilities

open import flat-modality

-- defining sets of morphisms in the category Θ
-- maps (n , P) → (m , Q) are pairs of a map
-- f : [ n ] → [ m ] of posets
-- together with a pasting scheme morphism
-- P (dual f i) → Q i for each i ∈ Fin m

infixr 5 _→PS_
_→PS_ : PS → PS → UU

cons (n , P') →PS cons (m , Q') =
  Σ ([ n ] →≤ [ m ]) λ f
  → (k : Fin m)
  → (i : Fin n)
  → (dual n m f k ＝ in-Fin i)
  → P' i →PS Q' k

-- defining terminal maps and checking they are terminal

∗-term-map : (P : PS) → (P →PS ∗)
pr1 (∗-term-map (cons (n , P'))) = [0]-term-map
pr2 (∗-term-map (cons (n , P'))) ()

private
  path-[0] : {x y : Fin 1} → x ＝ y
  path-[0] {inr star} {inr star} = refl

  map-is-term-map : (P : PS) → (σ : P →PS ∗) → (∗-term-map P ＝ σ)
  map-is-term-map (cons (n , P')) (f , α) =
    eq-pair-Σ
      (eq-pair-Σ
        (eq-htpy (λ _ → path-[0]))
        (center (is-prop-preserves-order-Poset [ n ] [ 0 ] (pr1 f) _ _)))
      (eq-htpy λ ())

  map-is-term-map♭ :
      (@♭ P : PS)
    → (σ : ♭(P →PS ∗))
    → (intro-flat (∗-term-map P) ＝ σ)
  map-is-term-map♭ (cons (n , P')) (intro-flat (f , α)) =
    map-inv-equiv (crisp-extensionality-flat _ _) (intro-flat path)
    where
      path : ∗-term-map (cons (pair n P')) ＝ pair f α
      path =
        eq-pair-Σ
          (eq-pair-Σ
            (eq-htpy (λ _ → path-[0]))
            (center (is-prop-preserves-order-Poset [ n ] [ 0 ] (pr1 f) _ _)))
          (eq-htpy λ ())

∗-is-term : (P : PS) → is-contr (P →PS ∗)
∗-is-term P = ∗-term-map P , map-is-term-map P

-- this one will be used to proove that \yo(1) is pointwise contractible.

∗-is-term♭ : (@♭ P : PS) → is-contr (♭(P →PS ∗))
∗-is-term♭ P = intro-flat (∗-term-map P) , map-is-term-map♭ P

-- defining constant morphism : [ P₁ , ... , Pₙ ] → [ Q₁ , ... , Qₘ ]

const-PS→ :
    (P : PS)
  → (Q : PS)
  → (x : Fin (1+ (PS-len Q)))
  → P →PS Q
pr1 (const-PS→ (cons (n , _)) (cons (m , _)) x)
  = const-fin-Poset n m x
pr2 (const-PS→ (cons (n , _)) (cons (m , _)) x) k i p
  = ex-falso (neq-in-Fin-dual-const n m x k i p)

-- defining the i-th point of any pasting scheme

pick-point :
    (P : PS)
  → (i : Fin (1+ (PS-len P)))
  → ∗ →PS P
pick-point P i = const-PS→ _ _ i

-- defining source and target of the arrow

in-∗ : ∗ →PS 𝑂₁
in-∗ = pick-point _ (zero-Fin 1)

in+∗ : ∗ →PS 𝑂₁
in+∗ = pick-point _ (one-Fin 1)

-- defining the identity morphism

id→PS : (P : PS) → P →PS P
pr1 (id→PS (cons(n , P'))) = id-hom-Poset [ n ]
pr2 (id→PS (cons(n , P'))) k i p = tr F path (id→PS (P' k))
  where
    F = λ x → P' x →PS P' k
    path = dual-id' n p

-- defining the zero-map : P →PS Q
-- which sends everything to the left point

zero-map : (P Q : PS) → P →PS Q
zero-map P (cons (m , _)) = const-PS→ P _ (zero-Fin m)

-- -- functoriality of the suspension

$→ : {P Q : PS} → (P →PS Q) → ($ P →PS $ Q)
pr1 ($→ σ) = id-hom-Poset [ 1 ]
pr2 ($→ {P} {Q} σ) k _ _ = σ

-- left and right extremal points of a pasting scheme

leftpoint : (P : PS) → ∗ →PS P
leftpoint (cons (n , _)) = pick-point _ (zero-Fin n)

rightpoint : (P : PS) → ∗ →PS P
rightpoint _ = pick-point _ (inr star)

-- subshape inclusion
-- for any pasting scheme P and any i ∈ [ len P ],
-- there is a map ($ Pi) → P

module _ where

  private
    pattern zero = inl (inr star)
    pattern one = inr star

  -- [1] → [n] : 0 ↦ i ; 1 ↦ i+1
  subinterval-inclusion :
      (n : ℕ)
    → (i : Fin n)
    → [ 1 ] →≤ [ n ]
  pr1 (subinterval-inclusion n i) zero = inl i
  pr1 (subinterval-inclusion n i) one = succ-Fin (1+ n) (inl i)
  pr2 (subinterval-inclusion n i) zero zero  leq
    = refl-leq-Fin (1+ n) (inl i)
  pr2 (subinterval-inclusion n i) zero one   leq
    = leq-succ-Fin n i
  pr2 (subinterval-inclusion n i) one  one   leq
    = refl-leq-Fin (1+ n) (succ-Fin (1+ n) (inl i))

  abstract
    dual-subinterval-inclusion-inr :
        (n : ℕ)
      → (i : Fin n)
      → (k : Fin n)
      → (le-Fin n i k)
      → dual 1 n (subinterval-inclusion n i) k ＝ inr
    dual-subinterval-inclusion-inr n i k i<k
      = compute-dual-inr 1 n (subinterval-inclusion n i) k
          (le-Fin-leq-succ (1+ n) (inl i) (inl k) i<k)

    dual-subinterval-inclusion-inl :
        (n : ℕ)
      → (i : Fin n)
      → (k : Fin n)
      → (le-Fin n k i)
      → dual 1 n (subinterval-inclusion n i) k ＝ inl
    dual-subinterval-inclusion-inl n i k k<i
      = compute-dual-inl 1 n (subinterval-inclusion n i) k k<i

    dual-subinterval-inclusion-in-Fin :
        (n : ℕ)
      → (i : Fin n)
      → dual 1 n (subinterval-inclusion n i) i ＝ in-Fin (inr star)
    dual-subinterval-inclusion-in-Fin n i
      = compute-dual-in-Fin 1 n (subinterval-inclusion n i) i (inr star)
          (refl-leq-Fin n i)
          (le-succ-Fin n i)

  subshape-inclusion :
      ((n , P) : array PS)
    → (i : Fin n)
    → $ (P i) →PS cons (n , P)
  pr1 (subshape-inclusion (n , P) i) = subinterval-inclusion n i
  pr2 (subshape-inclusion (n , P) i) k (inr star) p = tr F k=i (id→PS (P k))
    where
      F = λ x → P x →PS P k
      abstract
        k≤i : leq-Fin n k i
        k≤i with le-or-leq n k i
        ... | inl k≤i = k≤i
        ... | inr i<k
            rewrite (dual-subinterval-inclusion-inr n i k i<k)
            = ex-falso (inr≠in-Fin 1 _ p)
        i≤k : leq-Fin n i k
        i≤k with le-or-leq n i k
        ... | inl i≤k = i≤k
        ... | inr k<i
            rewrite (dual-subinterval-inclusion-inl n i k k<i)
            = ex-falso (inl≠in-Fin 1 _ p)
        k=i : k ＝ i
        k=i = antisymmetric-leq-Fin n k i k≤i i≤k

-- subshape retraction
-- for any pasting scheme P and any i ∈ [ len P ],
-- there is a map P → ($ Pi)

module _ where

  private
    pattern zero = inl (inr star)
    pattern one = inr star

  private
    subinterval-retraction-aux :
        (n : ℕ)
      → (i : Fin n)
      → (k : Fin (1+ n))
      → ( leq-Fin (1+ n) k (inl i)
        + le-Fin (1+ n) (inl i) k )
      → Fin 2
    subinterval-retraction-aux n i k (inl k≤i) = zero
    subinterval-retraction-aux n i k (inr i<k) = one

  -- [n] → [1] : k <= i ↦ 0 ; k >= i+1 ↦ 1
  subinterval-retraction :
      (n : ℕ)
    → (i : Fin n)
    → [ n ] →≤ [ 1 ]
  pr1 (subinterval-retraction n i) k =
    subinterval-retraction-aux n i k (le-or-leq (1+ n) k (inl i))
  pr2 (subinterval-retraction n i) j k j≤k
    with le-or-leq (1+ n) j (inl i)
  ... | inl j≤i = zero-leq-Fin 1 (pr1 (subinterval-retraction n i) k)
  ... | inr i<j
      with le-or-leq (1+ n) k (inl i)
  ... | inl k≤i = ex-falso (asymetric-le-Fin (1+ n) (inl i) i<i)
      where
        i<k : le-Fin (1+ n) (inl i) k
        i<k = le-leq-trans (1+ n) (inl i) j k i<j j≤k
        i<i : le-Fin (1+ n) (inl i) (inl i)
        i<i = le-leq-trans (1+ n) (inl i) k (inl i) i<k k≤i
  ... | inr i<k = _

  abstract
    subinterval-retraction-zero :
        (n : ℕ)
      → (i : Fin n)
      → (k : Fin (1+ n))
      → leq-Fin (1+ n) k (inl i)
      → pr1 (subinterval-retraction n i) k ＝ zero
    subinterval-retraction-zero n i k k≤i
      with le-or-leq (1+ n) k (inl i)
    ... | inl _ = refl
    ... | inr i<k = ex-falso (asymetric-le-Fin (1+ n) (inl i) i<i)
        where
          i<i : le-Fin (1+ n) (inl i) (inl i)
          i<i = le-leq-trans (1+ n) (inl i) k (inl i) i<k k≤i

    subinterval-retraction-one :
        (n : ℕ)
      → (i : Fin n)
      → (k : Fin (1+ n))
      → le-Fin (1+ n) (inl i) k
      → pr1 (subinterval-retraction n i) k ＝ one
    subinterval-retraction-one n i k i<k
      with le-or-leq (1+ n) k (inl i)
    ... | inr _ = refl
    ... | inl k≤i = ex-falso (asymetric-le-Fin (1+ n) (inl i) i<i)
        where
          i<i : le-Fin (1+ n) (inl i) (inl i)
          i<i = le-leq-trans (1+ n) (inl i) k (inl i) i<k k≤i

  abstract
    dual-subinterval-retraction :
        (n : ℕ)
      → (i : Fin n)
      → dual n 1 (subinterval-retraction n i) (inr star) ＝ in-Fin i
    dual-subinterval-retraction n i =
      compute-dual-in-Fin n 1 (subinterval-retraction n i) (inr star)
        i p1 p2
        where
          i≤i : leq-Fin (1+ n) (inl i) (inl i)
          i≤i = refl-leq-Fin (1+ n) (inl i)
          p1 : leq-Fin (1+ 1)
                  (pr1 (subinterval-retraction n i) (inl i))
                  zero
          p1 rewrite
            subinterval-retraction-zero n i (inl i) i≤i
            = star
          i<Si : le-Fin (1+ n) (inl i) (succ-Fin (1+ n) (inl i))
          i<Si = le-succ-Fin n i
          p2 : le-Fin (1+ 1)
                  zero
                  (pr1 (subinterval-retraction n i) (succ-Fin (1+ n) (inl i)))
          p2 rewrite
            subinterval-retraction-one n i (succ-Fin (1+ n) (inl i)) i<Si
            = star

  subshape-retraction :
      ((n , P) : array PS)
    → (i : Fin n)
    → cons (n , P) →PS $ (P i)
  pr1 (subshape-retraction (n , P) i) = subinterval-retraction n i
  pr2 (subshape-retraction (n , P) i) (inr star) j p = tr F i=j (id→PS (P i))
    where
      F = λ x → P x →PS P i
      abstract
        dual=i : dual n 1 (subinterval-retraction n i) one ＝ in-Fin i
        dual=i = dual-subinterval-retraction n i
        i=j : i ＝ j
        i=j = is-inj-in-Fin n i j (inv dual=i ∙ p)
