{-# OPTIONS --without-K #-}

module utilities where

open import agda-unimath-deps

infixr 0 _<|_
_<|_ :
  {l1 l2 : Level}
  → {A : UU l1}
  → {B : UU l2}
  → (A → B)
  → A
  → B
f <| x = f x

infixr 0 _|>_
_|>_ :
  {l1 l2 : Level}
  → {A : UU l1}
  → {B : UU l2}
  → A
  → (A → B)
  → B
x |> f = f x

case_of_ :
  ∀ {l1 l2} {A : UU l1} {B : A → UU l2}
  → (x : A)
  → ((x : A) → B x)
  → B x
case x of f = f x

case-eq_of_ :
  ∀ {l1 l2} {A : UU l1} {B : A → UU l2}
  → (x : A)
  → ((y : A) → (x ＝ y) → B y)
  → B x
case-eq x of f = f x refl

oftype_case-eq_of_ :
  ∀ {l1 l2} {A : UU l1} (B : A → UU l2)
  → (x : A)
  → ((y : A) → (x ＝ y) → B y)
  → B x
oftype B case-eq x of f = f x refl

Id-total-Id :
    {l : Level}
  → {A : UU l}
  → {a : A}
  → (x y : Σ A (Id a))
  → x ＝ y
Id-total-Id (_ , refl) (_ , refl) = refl

pattern 1+ n = succ n
pattern 2+ n = 1+ (1+ n)
pattern 3+ n = 1+ (2+ n)
