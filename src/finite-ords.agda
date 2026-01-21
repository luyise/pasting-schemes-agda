{-# OPTIONS --without-K #-}

module finite-ords where

open import utilities
open import agda-unimath-deps

Poset₀ : UU₁
Poset₀ = Poset lzero lzero

[_] : ℕ → Poset₀
[ n ] = Fin-Poset (1+ n)

le-Fin-leq-succ :
    (n : ℕ)
  → (i j : Fin n)
  → (le-Fin n i j)
  → (leq-Fin n (succ-Fin n i) j)
le-Fin-leq-succ (2+ n) (inl (inl i)) (inl j) i<j
  = le-Fin-leq-succ (1+ n) (inl i) j i<j
le-Fin-leq-succ (2+ n) _ (inr star) _ = star

leq-Fin-succ-le :
    (n : ℕ)
  → (i : Fin n)
  → (j : Fin (1+ n))
  → (leq-Fin (1+ n) (succ-Fin (1+ n) (inl i)) j)
  → (le-Fin (1+ n) (inl i) j)
leq-Fin-succ-le (1+ n) (inl i) (inl j) 1+i≤j = leq-Fin-succ-le n i j 1+i≤j
leq-Fin-succ-le (1+ n) i (inr star) 1+i≤j = star

neg-le-is-leq :
    (n : ℕ)
  → (i j : Fin n)
  → ¬ (le-Fin n i j)
  → leq-Fin n j i
neg-le-is-leq (1+ n) (inl i) (inl j) ¬i<j = neg-le-is-leq n i j ¬i<j
neg-le-is-leq (1+ n) (inl i) (inr star) p = ex-falso (p star)
neg-le-is-leq (1+ n) (inr star) _ _ = star

le-leq-trans :
    (n : ℕ)
  → (i j k : Fin n)
  → le-Fin n i j
  → leq-Fin n j k
  → le-Fin n i k
le-leq-trans (1+ n) (inl i) (inl j) (inl k) p q = le-leq-trans n i j k p q
le-leq-trans (1+ n) (inl i) (inl j) (inr star) _ _ = star
le-leq-trans (1+ n) (inl i) (inr star) (inr star) _ _ = star

le-or-leq :
    (n : ℕ)
  → (i j : Fin n)
  → ( leq-Fin n i j
    + le-Fin n j i )
le-or-leq (1+ n) (inl i) (inl j) = le-or-leq n i j
le-or-leq (1+ n) (inr star) (inl j) = inr star
le-or-leq (1+ n) i (inr star) = inl star

asymetric-le-Fin :
    (n : ℕ)
  → (i : Fin n)
  → ¬ (le-Fin n i i)
asymetric-le-Fin (1+ n) (inl i) p
  = asymetric-le-Fin n i p

zero-leq-Fin :
    (n : ℕ)
  → (i : Fin (1+ n))
  → leq-Fin (1+ n) (zero-Fin n) i
zero-leq-Fin (1+ n) (inl i) = zero-leq-Fin n i
zero-leq-Fin n (inr star) = star

le-succ-Fin :
    (n : ℕ)
  → (i : Fin n)
  → le-Fin (1+ n) (inl i) (succ-Fin (1+ n) (inl i))
le-succ-Fin (1+ n) (inl x) = le-succ-Fin n x
le-succ-Fin (1+ n) (inr star) = star

data Fin++ (n : ℕ) : UU where
  inl : Fin++ n
  inr : Fin++ n
  in-Fin : Fin n → Fin++ n

inl≠in-Fin :
    (n : ℕ)
  → (i : Fin n)
  → ¬ (inl ＝ in-Fin {n} i)
inl≠in-Fin _ _ ()

inr≠in-Fin :
    (n : ℕ)
  → (i : Fin n)
  → ¬ (inr ＝ in-Fin {n} i)
inr≠in-Fin _ _ ()

inl≠inr :
    (n : ℕ)
  → ¬ (Id {A = Fin++ n} inl inr)
inl≠inr _ ()

is-inj-in-Fin :
    (n : ℕ)
  → (i j : Fin n)
  → in-Fin {n} i ＝ in-Fin j
  → i ＝ j
is-inj-in-Fin n i j refl = refl

has-decidable-equality-Fin++ :
  (n : ℕ) → has-decidable-equality (Fin++ n)
has-decidable-equality-Fin++ n inl inl = inl refl
has-decidable-equality-Fin++ n inl inr = inr λ ()
has-decidable-equality-Fin++ n inl (in-Fin _) = inr λ ()
has-decidable-equality-Fin++ n inr inl = inr λ ()
has-decidable-equality-Fin++ n inr inr = inl refl
has-decidable-equality-Fin++ n inr (in-Fin _) = inr λ ()
has-decidable-equality-Fin++ n (in-Fin _) inl = inr λ ()
has-decidable-equality-Fin++ n (in-Fin _) inr = inr λ ()
has-decidable-equality-Fin++ n (in-Fin i) (in-Fin j)
  with has-decidable-equality-Fin n i j
... | inl i=j = inl (ap in-Fin i=j)
... | inr i≠j = inr (i≠j ∘ (is-inj-in-Fin n i j))

is-set-Fin++ : (n : ℕ) → is-set (Fin++ n)
is-set-Fin++ n = is-set-has-decidable-equality (has-decidable-equality-Fin++ n)

Fin++-inj :
    {n : ℕ}
  → Fin++ n
  → Fin++ (1+ n)
Fin++-inj inl = inl
Fin++-inj inr = inr
Fin++-inj (in-Fin i) = in-Fin (inl i)

is-in-fin : {n : ℕ} (x : Fin++ n) → UU
is-in-fin inl = ⊥
is-in-fin inr = ⊥
is-in-fin (in-Fin _) = ⊤

Fin++-to-Fin :
    {n : ℕ}
  → (x : Fin++ n)
  → is-in-fin x
  → Fin n
Fin++-to-Fin (in-Fin x) _ = x

Fin++-to-Fin-id :
    {n : ℕ}
  → {x y : Fin++ n}
  → (p : x ＝ y)
  → (π : is-in-fin x)
  → Fin++-to-Fin x π ＝ Fin++-to-Fin y (tr is-in-fin p π)
Fin++-to-Fin-id {n} {x} {y} p π = ap f α
  where
    f : Σ (Fin++ n) is-in-fin → Fin n
    f (x , y) = Fin++-to-Fin x y
    α : Id {A = Σ (Fin++ n) is-in-fin} (x , π) (y , tr is-in-fin p π)
    α = eq-pair-eq-base p

Fin++-to-Fin-ε :
    {n : ℕ}
  → (x : Fin++ n)
  → (π : is-in-fin x)
  → in-Fin (Fin++-to-Fin x π) ＝ x
Fin++-to-Fin-ε (in-Fin x) _ = refl

eval-Kleisli-++ :
    (n m : ℕ)
  → (f : Fin n → Fin++ m)
  → Fin++ n
  → Fin++ m
eval-Kleisli-++ n m f inl = inl
eval-Kleisli-++ n m f inr = inr
eval-Kleisli-++ n m f (in-Fin x) = f x

comp-Kleisli-++ :
    (n m l : ℕ)
  → (g : Fin m → Fin++ l)
  → (f : Fin n → Fin++ m)
  → Fin n → Fin++ l
comp-Kleisli-++ n m l g f k
  = eval-Kleisli-++ m l g (f k)

infixr 5 _→≤_
_→≤_ : Poset₀ → Poset₀ → UU
_→≤_ = hom-Poset

abstract
  equivalence-Fin-~-× : ∀ (n : ℕ) → ∀ (A : Fin (1+ n) → UU)
    → ((i : Fin (1+ n)) → A i) ≃ ((i : Fin n) → A (inl i)) × (A (inr star))
  equivalence-Fin-~-× n A =
    (λ f → (λ x → f (inl x)) , f (inr star)) ,
    (inverse-map , λ f → refl) ,
    (inverse-map , λ g → eq-htpy (htpy g))
    where
      inverse-map : ((i : Fin n) → A (inl i)) × (A (inr star))
        → ((i : Fin (1+ n)) → A i)
      inverse-map (g , a) (inl x) = g x
      inverse-map (g , a) (inr star) = a

      htpy : (g : (i : Fin (1+ n)) → A i)
        → inverse-map ((λ x → g (inl x)) , g (inr star)) ~ g
      htpy g (inl x) = refl
      htpy g (inr star) = refl

  has-decidable-equality-Fin-maps :
    ∀ (n : ℕ) → ∀ (A : Fin n → UU)
    → ((i : Fin n) → has-decidable-equality (A i))
    → has-decidable-equality ((i : Fin n) → A i)
  has-decidable-equality-Fin-maps zero-ℕ A _ f g =
    is-decidable-equiv (equiv-funext {f = f} {g = g}) (inl λ ())
  has-decidable-equality-Fin-maps (1+ n) A has-dec-eq-A =
    has-decidable-equality-equiv
      (equivalence-Fin-~-× n A)
      (has-decidable-equality-product
        (has-decidable-equality-Fin-maps n
          (A ∘ inl) (λ i → has-dec-eq-A (inl i)))
        (has-dec-eq-A (inr star)))

abstract
  has-decidable-equality→≤ : ∀ n m → has-decidable-equality ([ n ] →≤ [ m ])
  has-decidable-equality→≤ n m = has-decidable-equality-Σ
    (has-decidable-equality-maps (1+ n))
    (λ f → has-decidable-equality-is-prop
      (pr2 (preserves-order-prop-Poset [ n ] [ m ] f)))
    where
      has-decidable-equality-maps : ∀ (k : ℕ) →
        has-decidable-equality (Fin k → Fin (1+ m))
      has-decidable-equality-maps k =
        has-decidable-equality-Fin-maps
          k (λ _ → Fin (1+ m))
          (λ _ → has-decidable-equality-Fin (1+ m))

[0]-term-map :
  {n : ℕ} → [ n ] →≤ [ 0 ]
[0]-term-map = const _ (zero-Fin 0) , _

const-hom-Poset :
    (P : Poset₀)
  → (Q : Poset₀)
  → (x : type-Poset Q)
  → hom-Poset P Q
pr1 (const-hom-Poset _ _ x) = const _ x
pr2 (const-hom-Poset _ Q x) a b a≤b = refl-leq-Poset Q x

const-fin-Poset :
    (n m : ℕ)
  → (x : Fin (1+ m))
  → [ n ] →≤ [ m ]
const-fin-Poset n m x = const-hom-Poset [ n ] [ m ] x

has-preimage :
    (n m : ℕ)
  → (f : [ n ] →≤ [ m ])
  → (k : Fin m)
  → UU
has-preimage n m f k =
  Σ (Fin n) λ i
  → leq-Fin (1+ m) (f' (inl i)) (inl k)
  × le-Fin (1+ m) (inl k) (f' (succ-Fin (1+ n) (inl i)))
  where
    f' : Fin (1+ n) → Fin (1+ m)
    f' = map-hom-Poset [ n ] [ m ] f

abstract
  all-elements-equal-has-preimage :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → all-elements-equal (has-preimage n m f k)
  all-elements-equal-has-preimage n m f k
    (i , leq-i , le-i) (j , leq-j , le-j)
    = eq-pair-Σ
        (is-injective-inl-Fin n
          (antisymmetric-leq-Fin (1+ n) (inl i) (inl j) i≤j j≤i))
        (center (is-prop-product' _ _))
    where
      f' : Fin (1+ n) → Fin (1+ m)
      f' = map-hom-Poset [ n ] [ m ] f

      is-prop-leq-Fin' : is-prop (leq-Fin (1+ m) (f' (inl j)) (inl k))
      is-prop-leq-Fin' = is-prop-leq-Fin (1+ m) (f' (inl j)) (inl k)

      is-prop-le-Fin' :
        is-prop (le-Fin (1+ m) (inl k) (f' (succ-Fin (1+ n) (inl j))))
      is-prop-le-Fin'
        = is-prop-le-Fin (1+ m) (inl k) (f' (succ-Fin (1+ n) (inl j)))

      is-prop-product'
        : is-prop ((leq-Fin (1+ m) (f' (inl j)) (inl k)) × (le-Fin (1+ m) (inl k) (f' (succ-Fin (1+ n) (inl j)))))
      is-prop-product'
        = is-prop-product is-prop-leq-Fin' is-prop-le-Fin'

      ¬j<i : ¬ le-Fin n j i
      ¬j<i j<i = asymetric-le-Fin (1+ m) (inl k) k<k
        where
          -- j+1 ≤ i
          1+j≤i : leq-Fin (1+ n) (succ-Fin (1+ n) (inl j)) (inl i)
          1+j≤i = le-Fin-leq-succ (1+ n) (inl j) (inl i) j<i

          -- f (j+1) ≤ f i
          fleq :
            leq-Fin (1+ m) (f' (succ-Fin (1+ n) (inl j))) (f' (inl i))
          fleq
            = preserves-order-map-hom-Poset [ n ] [ m ]
                f (succ-Fin (1+ n) (inl j)) (inl i) 1+j≤i

          -- k < f i
          k<fi : le-Fin (1+ m) (inl k) (f' (inl i))
          k<fi = le-leq-trans (1+ m) (inl k) _ (f' (inl i)) le-j fleq

          -- k < k
          k<k : le-Fin (1+ m) (inl k) (inl k)
          k<k = le-leq-trans (1+ m) (inl k) (f' (inl i)) (inl k) k<fi leq-i

      i≤j : leq-Fin n i j
      i≤j = neg-le-is-leq n j i ¬j<i

      ¬i<j : ¬ le-Fin n i j
      ¬i<j i<j = asymetric-le-Fin (1+ m) (inl k) k<k
        where
          -- i+1 ≤ j
          1+i≤j : leq-Fin (1+ n) (succ-Fin (1+ n) (inl i)) (inl j)
          1+i≤j = le-Fin-leq-succ (1+ n) (inl i) (inl j) i<j

          -- f (i+1) ≤ f j
          fleq : leq-Fin (1+ m) (f' (succ-Fin (1+ n) (inl i))) (f' (inl j))
          fleq = preserves-order-map-hom-Poset [ n ] [ m ]
                    f (succ-Fin (1+ n) (inl i)) (inl j) 1+i≤j

          -- k < f j
          k<fj : le-Fin (1+ m) (inl k) (f' (inl j))
          k<fj = le-leq-trans (1+ m) (inl k) _ (f' (inl j)) le-i fleq

          -- k < k
          k<k : le-Fin (1+ m) (inl k) (inl k)
          k<k = le-leq-trans (1+ m) (inl k) (f' (inl j)) (inl k) k<fj leq-j

      j≤i : leq-Fin n j i
      j≤i = neg-le-is-leq n i j ¬i<j

abstract
  is-prop-has-preimage :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → is-prop (has-preimage n m f k)
  is-prop-has-preimage n m f k
    = is-prop-all-elements-equal (all-elements-equal-has-preimage n m f k)

preimage++ :
    (n m : ℕ)
  → (f : [ n ] →≤ [ m ])
  → (k : Fin m)
  → UU
preimage++ n m f k =
    le-Fin (1+ m) (inl k) (f' (zero-Fin n))
  + leq-Fin (1+ m) (f' (inr star)) (inl k)
  + has-preimage n m f k
  where
    f' : Fin (1+ n) → Fin (1+ m)
    f' = map-hom-Poset [ n ] [ m ] f

abstract
  all-elements-equal-preimage++ :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → all-elements-equal (preimage++ n m f k)

  all-elements-equal-preimage++ n m f k (inl k<f0) (inl k<f0')
    = ap _ (center
      (is-prop-le-Fin (1+ m) (inl k) (f' (zero-Fin n)) k<f0 k<f0'))
    where
      f' : Fin (1+ n) → Fin (1+ m)
      f' = map-hom-Poset [ n ] [ m ] f

  all-elements-equal-preimage++ n m f k (inl k<f0) (inr (inl fmax≤k))
    = ex-falso (asymetric-le-Fin (1+ m) (inl k) k<k)
    where
      f' : Fin (1+ n) → Fin (1+ m)
      f' = map-hom-Poset [ n ] [ m ] f

      f0≤fmax : leq-Fin (1+ m) (f' (zero-Fin n)) (f' (inr star))
      f0≤fmax = preserves-order-map-hom-Poset [ n ] [ m ]
                  f (zero-Fin n) (inr star) star

      k<fmax : le-Fin (1+ m) (inl k) (f' (inr star))
      k<fmax = le-leq-trans (1+ m) (inl k) _ (f' (inr star)) k<f0 f0≤fmax

      k<k : le-Fin (1+ m) (inl k) (inl k)
      k<k = le-leq-trans (1+ m) (inl k) (f' (inr star)) (inl k) k<fmax fmax≤k

  all-elements-equal-preimage++ n m f k (inl k<f0) (inr (inr (i , fi≤k , _)))
    = ex-falso (asymetric-le-Fin (1+ m) (inl k) k<k)
    where
      f' : Fin (1+ n) → Fin (1+ m)
      f' = map-hom-Poset [ n ] [ m ] f

      f0≤fi : leq-Fin (1+ m) (f' (zero-Fin n)) (f' (inl i))
      f0≤fi = preserves-order-map-hom-Poset [ n ] [ m ]
                f (zero-Fin n) (inl i) (zero-leq-Fin n (inl i))

      k<fi : le-Fin (1+ m) (inl k) (f' (inl i))
      k<fi = le-leq-trans (1+ m) (inl k) _ (f' (inl i)) k<f0 f0≤fi

      k<k : le-Fin (1+ m) (inl k) (inl k)
      k<k = le-leq-trans (1+ m) (inl k) (f' (inl i)) (inl k) k<fi fi≤k

  all-elements-equal-preimage++ n m f k (inr (inl fmax≤k)) (inl k<f0)
    = inv (all-elements-equal-preimage++ n m f k (inl k<f0) (inr (inl fmax≤k)))

  all-elements-equal-preimage++ n m f k (inr (inr p)) (inl k<f0)
    = inv (all-elements-equal-preimage++ n m f k (inl k<f0) (inr (inr p)))

  all-elements-equal-preimage++ n m f k (inr (inl fmax≤k)) (inr (inl fmax≤k'))
    = ap _ (center
        (is-prop-leq-Fin (1+ m) (pr1 f (inr star)) (inl k) fmax≤k fmax≤k'))

  all-elements-equal-preimage++ n m f k
      (inr (inl fmax≤k)) (inr (inr (i , _ , k<fSi)))
    = ex-falso (asymetric-le-Fin (1+ m) (inl k) k<k)
    where
      f' : Fin (1+ n) → Fin (1+ m)
      f' = map-hom-Poset [ n ] [ m ] f

      fSi≤fmax : leq-Fin (1+ m) (f' (succ-Fin (1+ n) (inl i))) (f' (inr star))
      fSi≤fmax = preserves-order-map-hom-Poset [ n ] [ m ] f (succ-Fin (1+ n) (inl i)) (inr star) star

      k<fmax : le-Fin (1+ m) (inl k) (f' (inr star))
      k<fmax = le-leq-trans (1+ m) (inl k) _ (f' (inr star)) k<fSi fSi≤fmax

      k<k : le-Fin (1+ m) (inl k) (inl k)
      k<k = le-leq-trans (1+ m) (inl k) (f' (inr star)) (inl k) k<fmax fmax≤k

  all-elements-equal-preimage++ n m f k (inr (inr x)) (inr (inl y))
    = inv (all-elements-equal-preimage++ n m f k (inr (inl y)) (inr (inr x)))

  all-elements-equal-preimage++ n m f k (inr (inr p)) (inr (inr q))
    = ap _ (all-elements-equal-has-preimage n m f k p q)

abstract
  is-prop-preimage++ :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → is-prop (preimage++ n m f k)
  is-prop-preimage++ n m f k
    = is-prop-all-elements-equal (all-elements-equal-preimage++ n m f k)

compute-preimage-Fin :
    (n m : ℕ)
  → (f : [ n ] →≤ [ m ])
  → (k : Fin m)
  → le-Fin (1+ m) (inl k) (pr1 f (inr star))
  → leq-Fin (1+ m) (pr1 f (zero-Fin n)) (inl k)
  → has-preimage n m f k
compute-preimage-Fin 0 m f k k<f0 f0≤k
  = ex-falso (asymetric-le-Fin (1+ m) (inl k) k<k)
  where abstract
    k<k : le-Fin (1+ m) (inl k) (inl k)
    k<k = le-leq-trans (1+ m)
      (inl k) (pr1 f (inr star)) (inl k)
      k<f0 f0≤k
compute-preimage-Fin (1+ n) m f k k<fSn f0≤k
  -- ask if f(n) ≤ k
  with le-or-leq (1+ m) (pr1 f (inl (inr star))) (inl k)
... | inl fn≤k = inr star , fn≤k , k<fSn
... | inr k<fn = inl preim , fpreim≤k , k<fSpreim
  where
    -- restriction of f to [ n ] ⊆ [ n+1 ]
    f' : [ n ] →≤ [ m ]
    f' = (λ i → (pr1 f) (inl i)) , λ i j → (pr2 f) (inl i) (inl j)
    preimage-f' : has-preimage n m f' k
    preimage-f' = compute-preimage-Fin n m f' k k<fn f0≤k
    preim : Fin n
    preim = preimage-f' .pr1
    abstract
      fpreim≤k : leq-Fin (1+ m) (pr1 f (inl (inl preim))) (inl k)
      fpreim≤k = preimage-f' .pr2 .pr1
      k<fSpreim
        : le-Fin (1+ m) (inl k) (pr1 f (inl (succ-Fin (1+ n) (inl preim))))
      k<fSpreim
        = preimage-f' .pr2 .pr2

compute-preimage :
    (n m : ℕ)
  → (f : [ n ] →≤ [ m ])
  → (k : Fin m)
  → preimage++ n m f k
compute-preimage n m f k
  = compute-preimage-aux n m f k
      (le-or-leq (1+ m) (pr1 f (inr star)) (inl k))
      (le-or-leq (1+ m) (pr1 f (zero-Fin n)) (inl k))
  where private
    compute-preimage-aux :
      (n m : ℕ)
      → (f : [ n ] →≤ [ m ])
      → (k : Fin m)
      → leq-Fin (1+ m) (pr1 f (inr star)) (inl k)
      + le-Fin (1+ m) (inl k) (pr1 f (inr star))
      → leq-Fin (1+ m) (pr1 f (zero-Fin n)) (inl k)
      + le-Fin (1+ m) (inl k) (pr1 f (zero-Fin n))
      → preimage++ n m f k
    compute-preimage-aux n m f k _            (inr k<f0)
      = inl k<f0
    compute-preimage-aux n m f k (inl fSn≤k)  (inl _)
      = inr (inl fSn≤k)
    compute-preimage-aux n m f k (inr k<fSn)  (inl f0≤k)
      = inr (inr (compute-preimage-Fin n m f k k<fSn f0≤k))

opaque
  dual-aux :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → preimage++ n m f k
    → Fin++ n
  dual-aux n m f k (inl k<f0) = inl
  dual-aux n m f k (inr (inl fSn≤k)) = inr
  dual-aux n m f k (inr (inr (i , _))) = in-Fin i

  dual-aux-inl :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → (k<f0 : le-Fin (1+ m) (inl k) (pr1 f (zero-Fin n)))
    → dual-aux n m f k (inl k<f0) ＝ inl
  dual-aux-inl n m f k k<f0 = refl

  dual-aux-inr :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → (fSn≤k : leq-Fin (1+ m) (pr1 f (inr star)) (inl k))
    → dual-aux n m f k (inr (inl fSn≤k)) ＝ inr
  dual-aux-inr n m f k fSn≤k = refl

  dual-aux-in-fin :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → (π@(i , _) : has-preimage n m f k)
    → dual-aux n m f k (inr (inr π)) ＝ in-Fin i
  dual-aux-in-fin n m f k π = refl

opaque
  dual :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → Fin++ n
  dual n m f k
    = dual-aux n m f k (compute-preimage n m f k)

  compute-dual-in-Fin :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → (i : Fin n)
    → leq-Fin (1+ m) (pr1 f (inl i)) (inl k)
    → le-Fin (1+ m) (inl k) (pr1 f (succ-Fin (1+ n) (inl i)))
    → dual n m f k ＝ in-Fin i
  compute-dual-in-Fin n m f k i fi≤k k<fSi
    with compute-preimage n m f k
  ... | p = dual-aux=in-fin-i
    where
      preimage++-f : preimage++ n m f k
      preimage++-f = inr (inr (i , fi≤k , k<fSi))
      abstract
        p=preim : preimage++-f ＝ p
        p=preim = all-elements-equal-preimage++ n m f k preimage++-f p
        dual-aux=in-fin-i : dual-aux n m f k p ＝ in-Fin i
        dual-aux=in-fin-i = tr (λ x → dual-aux n m f k x ＝ in-Fin i)
          p=preim
          (dual-aux-in-fin n m f k _)

  compute-dual-inl :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → le-Fin (1+ m) (inl k) (pr1 f (zero-Fin n))
    → dual n m f k ＝ inl
  compute-dual-inl n m f k k<f0
    with compute-preimage n m f k
  ... | p = dual-aux=inl
    where
      preimage++-f : preimage++ n m f k
      preimage++-f = inl k<f0
      abstract
        p=preim : preimage++-f ＝ p
        p=preim = all-elements-equal-preimage++ n m f k preimage++-f p
        dual-aux=inl : dual-aux n m f k p ＝ inl
        dual-aux=inl = tr (λ x → dual-aux n m f k x ＝ inl)
          p=preim
          (dual-aux-inl n m f k _)

  compute-dual-inr :
      (n m : ℕ)
    → (f : [ n ] →≤ [ m ])
    → (k : Fin m)
    → leq-Fin (1+ m) (pr1 f (inr star)) (inl k)
    → dual n m f k ＝ inr
  compute-dual-inr n m f k fSn≤k
    with compute-preimage n m f k
  ... | p = dual-aux=inr
    where
      preimage++-f : preimage++ n m f k
      preimage++-f = inr (inl fSn≤k)
      abstract
        p=preim : preimage++-f ＝ p
        p=preim = all-elements-equal-preimage++ n m f k preimage++-f p
        dual-aux=inr : dual-aux n m f k p ＝ inr
        dual-aux=inr = tr (λ x → dual-aux n m f k x ＝ inr)
          p=preim
          (dual-aux-inr n m f k _)

  dual-id :
      (n : ℕ)
    → (k : Fin n)
    → dual n n (id-hom-Poset [ n ]) k ＝ in-Fin k
  dual-id n k =
    compute-dual-in-Fin
      n n (id-hom-Poset [ n ])
      k k
      (refl-leq-Fin n k) (le-succ-Fin n k)

  Fin++-to-Fin-dual-id :
      (n : ℕ)
    → (k : Fin n)
    → (π : is-in-fin (dual n n (id-hom-Poset [ n ]) k))
    → Fin++-to-Fin (dual n n (id-hom-Poset [ n ]) k) π ＝ k
  Fin++-to-Fin-dual-id n k π = Fin++-to-Fin-id (dual-id n k) π

  neg-is-in-fin-dual-const :
      (n m : ℕ)
    → (x : Fin (1+ m))
    → (k : Fin m)
    → let y = dual n m (const-fin-Poset n m x) k in
      (¬ (is-in-fin y))
  neg-is-in-fin-dual-const n m x k π
    with le-or-leq (1+ m) x (inl k)
  ... | inl x≤k = tr is-in-fin (dual-aux-inr n m _ k _) π
  ... | inr k<x = tr is-in-fin (dual-aux-inl n m _ k _) π

abstract
  dual-const-inr :
        (n m : ℕ)
      → (x : Fin (1+ m))
      → (k : Fin m)
      → (leq-Fin (1+ m) x (inl k))
      → dual n m (const-fin-Poset n m x) k ＝ inr
  dual-const-inr n m x k x≤k = compute-dual-inr n m _ k x≤k

  dual-const-inl :
        (n m : ℕ)
      → (x : Fin (1+ m))
      → (k : Fin m)
      → (le-Fin (1+ m) (inl k) x)
      → dual n m (const-fin-Poset n m x) k ＝ inl
  dual-const-inl n m x k k<x = compute-dual-inl n m _ k k<x

  neq-in-Fin-dual-const :
      (n m : ℕ)
    → (x : Fin (1+ m))
    → (k : Fin m)
    → let y = dual n m (const-fin-Poset n m x) k in
      ∀ i → ¬ (y ＝ in-Fin i)
  neq-in-Fin-dual-const n m x k i p
    with le-or-leq (1+ m) x (inl k)
  ... | inl x≤k
      rewrite dual-const-inr n m x k x≤k
      = inr≠in-Fin n i p
  ... | inr k<x
      rewrite dual-const-inl n m x k k<x
      = inl≠in-Fin n i p

  dual-id' :
      (n : ℕ)
    → {k : Fin n}
    → {i : Fin n}
    → dual n n (id-hom-Poset [ n ]) k ＝ in-Fin i
    → k ＝ i
  dual-id' n {k} {i} p
    rewrite (dual-id n k) = is-inj-in-Fin n k i p

  -- composition of dual maps is the dual of compositions

abstract
  dual-comp :
      (n m l : ℕ)
    → (g : [ m ] →≤ [ l ])
    → (f : [ n ] →≤ [ m ])
    → (k : Fin l)
    → (dual n l (comp-hom-Poset [ n ] [ m ] [ l ] g f) k)
      ＝ comp-Kleisli-++ l m n (dual n m f) (dual m l g) k

  dual-comp n m l g f k
    with compute-preimage n l (comp-hom-Poset [ n ] [ m ] [ l ] g f) k
      |  compute-preimage m l g k

  ... | p
      | inl k<g0
    = equational-reasoning
        dual n l gf k
          ＝ inl
            by dual-gf=inl
          ＝ comp-Kleisli-++ l m n (dual n m f) (dual m l g) k
            by ap (eval-Kleisli-++ m n (dual n m f)) (inv dual-g=inl)
    where
      gf : [ n ] →≤ [ l ]
      gf = comp-hom-Poset [ n ] [ m ] [ l ] g f
      0≤f0 : leq-Fin (1+ m) (zero-Fin m) (pr1 f (zero-Fin n))
      0≤f0 = zero-leq-Fin m (pr1 f (zero-Fin n))
      g0≤gf0 : leq-Fin (1+ l) (pr1 g (zero-Fin m)) (pr1 g (pr1 f (zero-Fin n)))
      g0≤gf0 = preserves-order-map-hom-Poset [ m ] [ l ] g (zero-Fin m) (pr1 f (zero-Fin n)) 0≤f0
      k<gf0 : le-Fin (1+ l) (inl k) (pr1 g (pr1 f (zero-Fin n)))
      k<gf0 = le-leq-trans (1+ l) (inl k) _ (pr1 g (pr1 f (zero-Fin n))) k<g0 g0≤gf0
      dual-gf=inl : dual n l gf k ＝ inl
      dual-gf=inl = compute-dual-inl n l gf k k<gf0
      dual-g=inl : dual m l g k ＝ inl
      dual-g=inl = compute-dual-inl m l g k k<g0

  ... | p
      | inr (inl gSm≤k)
    = equational-reasoning
        dual n l gf k
          ＝ inr
            by dual-gf=inr
          ＝ comp-Kleisli-++ l m n (dual n m f) (dual m l g) k
            by ap (eval-Kleisli-++ m n (dual n m f)) (inv dual-g=inr)
    where
      gf : [ n ] →≤ [ l ]
      gf = comp-hom-Poset [ n ] [ m ] [ l ] g f
      fSn≤Sm : leq-Fin (1+ m) (pr1 f (inr star)) (inr star)
      fSn≤Sm = star
      gfSn≤gSm : leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (pr1 g (inr star))
      gfSn≤gSm = preserves-order-map-hom-Poset [ m ] [ l ] g (pr1 f (inr star)) (inr star) fSn≤Sm
      gfSn≤k : leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (inl k)
      gfSn≤k = transitive-leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (pr1 g (inr star)) (inl k) gSm≤k gfSn≤gSm
      dual-gf=inr : dual n l gf k ＝ inr
      dual-gf=inr = compute-dual-inr n l gf k gfSn≤k
      dual-g=inr : dual m l g k ＝ inr
      dual-g=inr = compute-dual-inr m l g k gSm≤k

  ... | p
      | inr (inr (j , gj≤k , k<gSj))
    = equational-reasoning
        dual n l gf k
          ＝ dual n m f j
            by dual-comp-in-fin
          ＝ comp-Kleisli-++ l m n (dual n m f) (dual m l g) k
            by ap (eval-Kleisli-++ m n (dual n m f)) (inv dual-g=in-fin-j)
    where
      gf : [ n ] →≤ [ l ]
      gf = comp-hom-Poset [ n ] [ m ] [ l ] g f
      dual-g=in-fin-j : dual m l g k ＝ in-Fin j
      dual-g=in-fin-j = compute-dual-in-Fin m l g k j gj≤k k<gSj
      dual-comp-in-fin :
        dual n l gf k
        ＝ dual n m f j
      dual-comp-in-fin with compute-preimage n m f j
      ... | inl j<f0
          = equational-reasoning
              dual n l gf k
                ＝ inl
                  by dual-gf=inl
                ＝ dual n m f j
                  by inv dual-f=inl
          where
            gSj≤gf0 : leq-Fin (1+ l) (pr1 g (succ-Fin (1+ m) (inl j))) (pr1 g (pr1 f (zero-Fin n)))
            gSj≤gf0 = preserves-order-map-hom-Poset [ m ] [ l ] g (succ-Fin (1+ m) (inl j)) (pr1 f (zero-Fin n))
              (le-Fin-leq-succ (1+ m) (inl j) (pr1 f (zero-Fin n)) j<f0)
            k<gf0 : le-Fin (1+ l) (inl k) (pr1 g (pr1 f (zero-Fin n)))
            k<gf0 = le-leq-trans (1+ l) (inl k) _ (pr1 g (pr1 f (zero-Fin n))) k<gSj gSj≤gf0
            dual-gf=inl : dual n l gf k ＝ inl
            dual-gf=inl = compute-dual-inl n l gf k k<gf0
            dual-f=inl : dual n m f j ＝ inl
            dual-f=inl = compute-dual-inl n m f j j<f0
      ... | inr (inl fSn≤j)
          = equational-reasoning
              dual n l gf k
                ＝ inr
                  by dual-gf=inr
                ＝ dual n m f j
                  by inv dual-f=inr
          where
            gfSn≤gj : leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (pr1 g (inl j))
            gfSn≤gj = preserves-order-map-hom-Poset [ m ] [ l ] g (pr1 f (inr star)) (inl j) fSn≤j
            gfSn≤k : leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (inl k)
            gfSn≤k = transitive-leq-Fin (1+ l) (pr1 g (pr1 f (inr star))) (pr1 g (inl j)) (inl k) gj≤k gfSn≤gj
            dual-gf=inr : dual n l gf k ＝ inr
            dual-gf=inr = compute-dual-inr n l gf k gfSn≤k
            dual-f=inr : dual n m f j ＝ inr
            dual-f=inr = compute-dual-inr n m f j fSn≤j
      ... | inr (inr (i , fi≤j , j<fSi))
          = equational-reasoning
              dual n l gf k
                ＝ in-Fin i
                  by dual-gf=in-fin-i
                ＝ dual n m f j
                  by inv dual-f=in-fin-i
          where
            Sj≤fSi : leq-Fin (1+ m) (skip-zero-Fin m j) (pr1 f (skip-zero-Fin n i))
            Sj≤fSi = le-Fin-leq-succ (1+ m) (inl j) (pr1 f (skip-zero-Fin n i)) j<fSi
            gSj≤gfSi : leq-Fin (1+ l) (pr1 g (skip-zero-Fin m j)) (pr1 gf (skip-zero-Fin n i))
            gSj≤gfSi = preserves-order-map-hom-Poset [ m ] [ l ] g (skip-zero-Fin m j) (pr1 f (skip-zero-Fin n i)) Sj≤fSi
            k<gfSi : le-Fin (1+ l) (inl k) (pr1 gf (skip-zero-Fin n i))
            k<gfSi = le-leq-trans (1+ l) (inl k) (pr1 g (skip-zero-Fin m j)) (pr1 gf (skip-zero-Fin n i)) k<gSj gSj≤gfSi
            gfi≤gj : leq-Fin (1+ l) (pr1 gf (inl i)) (pr1 g (inl j))
            gfi≤gj = preserves-order-map-hom-Poset [ m ] [ l ] g (pr1 f (inl i)) (inl j) fi≤j
            gfi≤k : leq-Fin (1+ l) (pr1 gf (inl i)) (inl k)
            gfi≤k = transitive-leq-Fin (1+ l) (pr1 gf (inl i)) (pr1 g (inl j)) (inl k) gj≤k gfi≤gj
            dual-gf=in-fin-i : dual n l gf k ＝ in-Fin i
            dual-gf=in-fin-i = compute-dual-in-Fin n l gf k i gfi≤k k<gfSi
            dual-f=in-fin-i : dual n m f j ＝ in-Fin i
            dual-f=in-fin-i = compute-dual-in-Fin n m f j i fi≤j j<fSi

  dual-comp-in-Fin :
      (n m l : ℕ)
    → (g : [ m ] →≤ [ l ])
    → (f : [ n ] →≤ [ m ])
    → (k : Fin l)
    → (i : Fin n)
    → (dual n l (comp-hom-Poset [ n ] [ m ] [ l ] g f) k ＝ in-Fin i)
    → Σ (Fin m) λ j
      → (dual m l g k ＝ in-Fin j)
      × (dual n m f j ＝ in-Fin i)
  dual-comp-in-Fin n m l g f k i p
    rewrite (dual-comp n m l g f k)
    with dual m l g k
  ... | in-Fin j = j , refl , p
