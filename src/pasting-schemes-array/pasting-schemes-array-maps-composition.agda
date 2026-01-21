{-# OPTIONS --flat-split #-}

module pasting-schemes-array.pasting-schemes-array-maps-composition where

open import agda-unimath-deps

open import pasting-schemes-array.pasting-schemes-array
open import pasting-schemes-array.pasting-schemes-array-maps
open import celltt-arrays
open import finite-ords

--composition of morphisms of pasting schemes

infixr 15 _∘PS_

_∘PS_ : {Q R : PS} → (Q →PS R) → {P : PS} → (P →PS Q) → P →PS R
pr1 (_∘PS_ {cons(m , _)} {cons(l , _)} τ {cons(n , _)} σ)
  = comp-hom-Poset [ n ] [ m ] [ l ] (pr1 τ) (pr1 σ)
pr2 (_∘PS_ {cons(m , Q')} {cons(l , R')} τ {cons(n , P')} σ)
  k i p = map-2 ∘PS map-1
  module comp where
    private
      f = pr1 σ
      g = pr1 τ
    abstract
      t : Σ (Fin m) λ j
          → (dual m l g k ＝ in-Fin j)
          × (dual n m f j ＝ in-Fin i)
      t = dual-comp-in-Fin n m l g f k i p
      j : Fin m
      j = pr1 t
      p2 : dual m l g k ＝ in-Fin j
      p2 = pr1 (pr2 t)
      p1 : dual n m f j ＝ in-Fin i
      p1 = pr2 (pr2 t)
    map-1 : P' i →PS Q' j
    map-1 = pr2 σ j i p1
    map-2 : Q' j →PS R' k
    map-2 = pr2 τ k j p2

-- some lemmas about transporting the recursive part of a PS morphism
-- along the index of its source or target

abstract
  tr-map-PS-src :
      (n : ℕ) → (P' : Fin n → PS)
    → (m : ℕ) → (Q' : Fin m → PS)
    → (f : [ n ] →≤ [ m ])
    → (δ :  (k : Fin m)
          → (i : Fin n)
          → (dual n m f k ＝ in-Fin i)
          → P' i →PS Q' k)
    → (k : Fin m)
    → {i1 : Fin n} → (p1 : dual n m f k ＝ in-Fin i1)
    → {i2 : Fin n} → (p2 : dual n m f k ＝ in-Fin i2)
    → (γ : i1 ＝ i2)
    → tr (_→PS Q' k) (ap P' γ) (δ k i1 p1) ＝ δ k i2 p2
  tr-map-PS-src n P' m Q' f δ k {i1} p1 p2 refl = ap (δ k i1) p1=p2
    where
      p1=p2 : p1 ＝ p2
      p1=p2 = center (is-set-Fin++ n _ _ p1 p2)

  tr-map-PS-tgt :
      (n : ℕ) → (P' : Fin n → PS)
    → (m : ℕ) → (Q' : Fin m → PS)
    → (f : [ n ] →≤ [ m ])
    → (δ :  (k : Fin m)
          → (i : Fin n)
          → (dual n m f k ＝ in-Fin i)
          → P' i →PS Q' k)
    → (i : Fin n)
    → {k1 : Fin m} → (p1 : dual n m f k1 ＝ in-Fin i)
    → {k2 : Fin m} → (p2 : dual n m f k2 ＝ in-Fin i)
    → (γ : k1 ＝ k2)
    → tr (P' i →PS_) (ap Q' γ) (δ k1 i p1) ＝ δ k2 i p2
  tr-map-PS-tgt n P' m Q' f δ i {k1} p1 p2 refl = ap (δ k1 i) p1=p2
    where
      p1=p2 : p1 ＝ p2
      p1=p2 = center (is-set-Fin++ n _ _ p1 p2)

  tr-map-PS-src-tgt :
      (n : ℕ) → (P' : Fin n → PS)
    → (m : ℕ) → (Q' : Fin m → PS)
    → (f : [ n ] →≤ [ m ])
    → (δ :  (k : Fin m)
          → (i : Fin n)
          → (dual n m f k ＝ in-Fin i)
          → P' i →PS Q' k)
    → {i1 : Fin n} → {k1 : Fin m} → (p1 : dual n m f k1 ＝ in-Fin i1)
    → {i2 : Fin n} → {k2 : Fin m} → (p2 : dual n m f k2 ＝ in-Fin i2)
    → (α : i1 ＝ i2) → (β : k1 ＝ k2)
    → binary-tr (_→PS_) (ap P' α) (ap Q' β) (δ k1 i1 p1) ＝ δ k2 i2 p2
  tr-map-PS-src-tgt n P' m Q' f δ {i1} {k1} p1 p2 refl refl = ap (δ k1 i1) p1=p2
    where
      p1=p2 : p1 ＝ p2
      p1=p2 = center (is-set-Fin++ n _ _ p1 p2)

-- a lemma about transporting along the middle object
-- when composing two morphisms

abstract
  comp-tr-midway :
      {Q Q' R : PS}
    → (τ : Q →PS R)
    → {P : PS}
    → (σ : P →PS Q)
    → (p : Q ＝ Q')
    → (tr (λ X → X →PS R) p τ)
      ∘PS (tr (λ X → P →PS X) p σ)
      ＝ τ ∘PS σ
  comp-tr-midway τ σ refl = refl

-- a lemma about transporting along the two middle objects
-- of a triple composition

abstract
  comp-binary-tr-midway :
      {P Q Q' R R' S : PS}
    → (γ : R →PS S)
    → (β : Q →PS R)
    → (α : P →PS Q)
    → (p : Q ＝ Q')
    → (q : R ＝ R')
    → ((tr (_→PS S) q γ)
      ∘PS (binary-tr (_→PS_) p q β))
      ∘PS (tr (P →PS_) p α)
      ＝ (γ ∘PS β) ∘PS α
  comp-binary-tr-midway γ β α refl refl = refl

-- left unitality

private
  id→PS-left-aux : {P Q : PS} → (σ : P →PS Q) → (id→PS Q) ∘PS σ ＝ σ
  id→PS-left-aux {cons(n , P')} {cons(m , Q')} (f , δ)
    = eq-pair-Σ
        refl
        ( eq-htpy λ k
        → eq-htpy λ i
        → eq-htpy λ p
        → ho-δ k i p )

    where
      P = cons(n , P')
      Q = cons(m , Q')
      σ : P →PS Q
      σ = (f , δ)
      id[m] = id-hom-Poset [ m ]
      id∘σ = (id→PS Q) ∘PS σ
      dual-id∘σ = dual n m (pr1 id∘σ)

      module _
          (k : Fin m)
          (i : Fin n)
          (p : dual-id∘σ k ＝ in-Fin i)
        where
        open comp m Q' m Q' (id→PS (cons (m , Q'))) n P' σ k i p

        ho-δ : pr2 id∘σ k i p ＝ δ k i p
        t' = dual-comp-in-Fin n m m id[m] f k i p

        abstract
          j' : Fin m
          j' = pr1 t'
          p-id[m] : dual m m id[m] k ＝ in-Fin j'
          p-id[m] = pr1 (pr2 t')
          j=j' : j ＝ j'
          j=j' = is-inj-in-Fin m j j' (inv p2 ∙ p-id[m])
          j'=k : j' ＝ k
          j'=k = inv (dual-id' m p-id[m])
          j=k : j ＝ k
          j=k = j=j' ∙ j'=k
          pf : dual n m f j' ＝ in-Fin i
          pf = pr2 (pr2 t')
          pair= :
            Id {A = Σ (Fin m) λ u → dual-id∘σ u ＝ in-Fin i}
              (j , p1) (k , p)
          pair= = eq-pair-Σ j=k (center (is-set-Fin++ n _ _ _ _))
        abstract
          Q'k=Q'j : Q' k ＝ Q' j
          Q'k=Q'j = ap (Q' ∘ pr1) (inv pair=)
          tr-δ : δ j i p1 ＝ tr (λ X → P' i →PS X) Q'k=Q'j (δ k i p)
          tr-δ
            rewrite substitution-law-tr (P' i →PS_) (Q' ∘ pr1) (inv pair=) {δ k i p}
            rewrite apd (λ{ (u , γ) → δ u i γ }) (inv pair=)
            = refl
          tr-id :
            tr (λ x → Q' x →PS Q' k) (dual-id' m p2) (id→PS (Q' k))
            ＝ tr (λ X → X →PS Q' k) Q'k=Q'j (id→PS (Q' k))
          tr-id
            rewrite inv (substitution-law-tr (_→PS Q' k) Q' (dual-id' m p2) {(id→PS (Q' k))})
            rewrite center (is-set-PS (Q' k) (Q' j) (ap Q' (dual-id' m p2)) (ap (λ a → Q' (pr1 a)) (inv pair=)))
            = refl
        ho-δ
          rewrite tr-δ
          rewrite tr-id
          rewrite comp-tr-midway (id→PS (Q' k)) (δ k i p) Q'k=Q'j
          = id→PS-left-aux (δ k i p)

-- right unitality

private
  id→PS-right-aux : {P Q : PS} → (σ : P →PS Q) → σ ∘PS (id→PS P) ＝ σ
  id→PS-right-aux {cons(n , P')} {cons(m , Q')} (f , δ)
    = eq-pair-Σ
        refl
        ( eq-htpy λ k
        → eq-htpy λ i
        → eq-htpy λ p
        → ho-δ k i p )

    where
      P = cons(n , P')
      Q = cons(m , Q')
      σ : P →PS Q
      σ = (f , δ)
      id[n] = id-hom-Poset [ n ]
      σ∘id = σ ∘PS (id→PS P)
      dual-σ∘id = dual n m (pr1 σ∘id)

      module _
          (k : Fin m)
          (i : Fin n)
          (p : dual-σ∘id k ＝ in-Fin i)
        where
        open comp n P' m Q' σ n P' (id→PS (cons (n , P'))) k i p

        ho-δ :
          δ k j p2
          ∘PS
          tr (λ u → P' u →PS P' j) (dual-id' n p1) (id→PS (P' j))
          ＝ δ k i p
        t' = dual-comp-in-Fin n n m f id[n] k i p

        abstract
          j' : Fin n
          j' = pr1 t'
          pf : dual n m f k ＝ in-Fin j'
          pf = pr1 (pr2 t')
          p-id[n] : dual n n id[n] j' ＝ in-Fin i
          p-id[n] = pr2 (pr2 t')
          j'=i : j' ＝ i
          j'=i = dual-id' n p-id[n]
          j=j' : j ＝ j'
          j=j' = is-inj-in-Fin n j j' (inv p2 ∙ pf)
          j=i : j ＝ i
          j=i = j=j' ∙ j'=i
          pair= :
            Id {A = Σ (Fin n) λ u → dual-σ∘id k ＝ in-Fin u}
              (j , p2) (i , p)
          pair= = eq-pair-Σ j=i ((center (is-set-Fin++ n _ _ _ _)))
        abstract
          P'i=P'j : P' i ＝ P' j
          P'i=P'j = ap (P' ∘ pr1) (inv pair=)
          tr-δ : δ k j p2 ＝ tr (λ X → X →PS Q' k) P'i=P'j (δ k i p)
          tr-δ
            rewrite substitution-law-tr (_→PS Q' k) (P' ∘ pr1) (inv pair=) {δ k i p}
            rewrite apd (λ{ (u , γ) → δ k u γ }) (inv pair=)
            = refl
          tr-id :
            tr (λ u → P' u →PS P' j) (dual-id' n p1) (id→PS (P' j))
            ＝ tr (λ X → X →PS P' j) (inv P'i=P'j) (id→PS (P' j))
          tr-id
            rewrite inv (substitution-law-tr (_→PS P' j) P' (dual-id' n p1) {(id→PS (P' j))})
            rewrite center (is-set-PS (P' j) (P' i) (ap P' (dual-id' n p1)) (inv (ap (λ a → P' (pr1 a)) (inv pair=))))
            = refl
        lem :
          ∀ {S S' T}
          → (α : S ＝ S')
          → (φ : S →PS T)
          → (tr (_→PS T) α φ) ∘PS (tr (_→PS S') (inv α) (id→PS S')) ＝ φ ∘PS (id→PS S)
        lem refl φ = refl
        ho-δ
          rewrite tr-δ
          rewrite tr-id
          rewrite (lem P'i=P'j (δ k i p))
          = id→PS-right-aux (δ k i p)

-- associativity

private
  comp-assoc-aux :
    ∀ {P Q R S}
    → (γ : R →PS S)
    → (β : Q →PS R)
    → (α : P →PS Q)
    → (γ ∘PS β) ∘PS α
      ＝ γ ∘PS (β ∘PS α)
  comp-assoc-aux
    {cons(nP , P')}
    {cons(nQ , Q')}
    {cons(nR , R')}
    {cons(nS , S')}
    (γ1 , γ2)
    (β1 , β2)
    (α1 , α2)
    = eq-pair-Σ
        refl
        ( eq-htpy λ k
        → eq-htpy λ i
        → eq-htpy λ p
        → path k i p )
    where

      P = cons(nP , P')
      Q = cons(nQ , Q')
      R = cons(nR , R')
      S = cons(nS , S')
      α : P →PS Q
      α = (α1 , α2)
      β : Q →PS R
      β = (β1 , β2)
      γ : R →PS S
      γ = (γ1 , γ2)
      dualα = dual nP nQ α1
      dualβ = dual nQ nR β1
      dualγ = dual nR nS γ1
      βα = β ∘PS α
      γβ = γ ∘PS β
      βα1 = pr1 βα
      γβ1 = pr1 γβ
      dualβα = dual nP nR βα1
      dualγβ = dual nQ nS γβ1
      γβα1 = (
        comp-hom-Poset [ nP ] [ nQ ] [ nS ]
          (comp-hom-Poset [ nQ ] [ nR ] [ nS ] γ1 β1)
          α1
        )
      dualγβα = dual nP nS γβα1

      module comp-βα = comp nQ Q' nR R' β nP P' α
      module comp-γβ = comp nR R' nS S' γ nQ Q' β
      module comp-γ-βα = comp nR R' nS S' γ nP P' βα
      module comp-γβ-α = comp nQ Q' nS S' γβ nP P' α

      module _
        (l : Fin nS)
        (i : Fin nP)
        (p : dualγβα l ＝ in-Fin i)
        where

        --   α   β   γ
        -- P → Q → R → S
        -- i - j - k - l

        k1 = comp-γ-βα.j l i p
        dualγl=k1 : dualγ l ＝ in-Fin k1
        dualγl=k1 = comp-γ-βα.p2 l i p
        dualβαk1=i : dualβα k1 ＝ in-Fin i
        dualβαk1=i = comp-γ-βα.p1 l i p

        j1 = comp-βα.j k1 i dualβαk1=i
        dualβk1=j1 : dualβ k1 ＝ in-Fin j1
        dualβk1=j1 = comp-βα.p2 k1 i dualβαk1=i
        dualαj1=i : dualα j1 ＝ in-Fin i
        dualαj1=i = comp-βα.p1 k1 i dualβαk1=i

        j2 = comp-γβ-α.j l i p
        dualγβl=j2 : dualγβ l ＝ in-Fin j2
        dualγβl=j2 = comp-γβ-α.p2 l i p
        dualαj2=i : dualα j2 ＝ in-Fin i
        dualαj2=i = comp-γβ-α.p1 l i p

        k2 = comp-γβ.j l j2 dualγβl=j2
        dualγl=k2 : dualγ l ＝ in-Fin k2
        dualγl=k2 = comp-γβ.p2 l j2 dualγβl=j2
        dualβk2=j2 : dualβ k2 ＝ in-Fin j2
        dualβk2=j2 = comp-γβ.p1 l j2 dualγβl=j2

        -- map-1 : P' i →PS Q' j
        -- map-1 = pr2 σ j i p1
        -- map-2 : Q' j →PS R' k
        -- map-2 = pr2 τ k j p2

        γ2-map1 = γ2 l k1 dualγl=k1   -- R' k1 → S' l
        β2-map1 = β2 k1 j1 dualβk1=j1 -- Q' j1 → R' k1
        α2-map1 = α2 j1 i dualαj1=i   -- P' i  → Q' j1

        γ2-map2 = γ2 l k2 dualγl=k2    -- R' k2 → S' l
        β2-map2 = β2 k2 j2 dualβk2=j2  -- Q' j2 → R' k2
        α2-map2 = α2 j2 i dualαj2=i    -- P' i  → Q' j2

        γ-βα-map1 = pr2 βα k1 i dualβαk1=i  -- P' i  → R' k1
        γβ-α-map2 = pr2 γβ l j2 dualγβl=j2  -- Q' j2 → R' l

        -- (γ2-map2 ∘PS β2-map2) = γβ-α-map2
        -- γ-βα-map1 = (β2-map1 ∘PS α2-map1)

        abstract
          k1=k2 : k1 ＝ k2
          k1=k2 = is-inj-in-Fin nR k1 k2 (inv dualγl=k1 ∙ dualγl=k2)
          j1=j2 : j1 ＝ j2
          j1=j2 = is-inj-in-Fin nQ j1 j2
            (inv dualβk1=j1 ∙ ap dualβ k1=k2 ∙ dualβk2=j2)

        Rk1=Rk2 : R' k1 ＝ R' k2
        Rk1=Rk2 = ap R' k1=k2
        Qj1=Qj2 : Q' j1 ＝ Q' j2
        Qj1=Qj2 = ap Q' j1=j2

        abstract
          γ2-map-tr : γ2-map2 ＝ tr (_→PS S' l) Rk1=Rk2 γ2-map1
          γ2-map-tr = inv
            (tr-map-PS-src nR R' nS S' γ1 γ2 l dualγl=k1 dualγl=k2 k1=k2)
          β2-map-tr : β2-map2 ＝ binary-tr (_→PS_) Qj1=Qj2 Rk1=Rk2 β2-map1
          β2-map-tr = inv
            (tr-map-PS-src-tgt nQ Q' nR R' β1 β2
              dualβk1=j1 dualβk2=j2 j1=j2 k1=k2)
          α2-map-tr : α2-map2 ＝ tr (P' i →PS_) Qj1=Qj2 α2-map1
          α2-map-tr = inv
            (tr-map-PS-tgt nP P' nQ Q' α1 α2 i dualαj1=i dualαj2=i j1=j2)

        path :
          (γ2-map2 ∘PS β2-map2) ∘PS α2-map2
          ＝
          γ2-map1 ∘PS (β2-map1 ∘PS α2-map1)
        path
          rewrite α2-map-tr
          rewrite β2-map-tr
          rewrite γ2-map-tr
          rewrite comp-binary-tr-midway
            γ2-map1 β2-map1 α2-map1 Qj1=Qj2 Rk1=Rk2
          = comp-assoc-aux γ2-map1 β2-map1 α2-map1

-- defining abstract version of those lemmas to ensures
-- they never unfold

abstract
  id→PS-left : {P Q : PS} → (σ : P →PS Q) → (id→PS Q) ∘PS σ ＝ σ
  id→PS-left = id→PS-left-aux

  id→PS-right : {P Q : PS} → (σ : P →PS Q) → σ ∘PS (id→PS P) ＝ σ
  id→PS-right = id→PS-right-aux

  PS-comp-assoc : ∀ {P Q R S}
    → (γ : R →PS S)
    → (β : Q →PS R)
    → (α : P →PS Q)
    → (γ ∘PS β) ∘PS α
      ＝ γ ∘PS (β ∘PS α)
  PS-comp-assoc = comp-assoc-aux
