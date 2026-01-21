{-# OPTIONS --cohesion --flat-split --without-K #-}

module flat-modality where

open import modal-type-theory.action-on-homotopies-flat-modality public
open import modal-type-theory.action-on-identifications-crisp-functions public
open import modal-type-theory.action-on-identifications-flat-modality public
open import modal-type-theory.crisp-cartesian-product-types public
open import modal-type-theory.crisp-coproduct-types public
open import modal-type-theory.crisp-dependent-function-types public
open import modal-type-theory.crisp-dependent-pair-types public
open import modal-type-theory.crisp-function-types public
open import modal-type-theory.crisp-identity-types public
open import modal-type-theory.crisp-pullbacks public
open import modal-type-theory.crisp-types public
open import modal-type-theory.dependent-universal-property-flat-discrete-crisp-types public
open import modal-type-theory.flat-discrete-crisp-types public
open import modal-type-theory.flat-modality public
open import modal-type-theory.functoriality-flat-modality public
open import modal-type-theory.transport-along-crisp-identifications public
open import modal-type-theory.universal-property-flat-discrete-crisp-types public

open import agda-unimath-deps

infixr 15 _∘♭_
_∘♭_ : {@♭ A B C : UU} → ♭(B → C) → ♭(A → B) → ♭(A → C)
(intro-flat g) ∘♭ (intro-flat f) = intro-flat (g ∘ f)

crisp-ap-binary :
  {@♭ l1 l2 : Level} {l3 : Level} {@♭ A : UU l1} {@♭ B : UU l2} {C : UU l3}
  (f : @♭ A → @♭ B → C) {@♭ x x' : A} {@♭ y y' : B}
  → @♭ (x ＝ x') → @♭ (y ＝ y') → f x y ＝ f x' y'
crisp-ap-binary f refl refl = refl

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where
  open import foundation.dependent-pair-types
  open import foundation-core.sections
  open import foundation-core.retractions

  private
    map-distributive-flat-Σ' = map-distributive-flat-Σ {B = B}
    map-inv-distributive-flat-Σ' = map-inv-distributive-flat-Σ {B = B}

  retraction-inv-distributive-flat-Σ : retraction map-inv-distributive-flat-Σ'
  retraction-inv-distributive-flat-Σ = map-distributive-flat-Σ , is-retraction-map-distributive-flat-Σ

  section-inv-distributive-flat-Σ : section map-inv-distributive-flat-Σ'
  section-inv-distributive-flat-Σ = map-distributive-flat-Σ , is-section-map-distributive-flat-Σ

  is-equiv-map-inv-distributive-flat-Σ : is-equiv map-inv-distributive-flat-Σ
  is-equiv-map-inv-distributive-flat-Σ = section-inv-distributive-flat-Σ , retraction-inv-distributive-flat-Σ

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where
  open import foundation.dependent-pair-types
  open import foundation-core.sections
  open import foundation-core.retractions

  private
    map-distributive-flat-product' = map-distributive-flat-product {A = A} {B = B}
    map-inv-distributive-flat-product' = map-inv-distributive-flat-product {A = A} {B = B}

  retraction-inv-distributive-flat-product : retraction map-inv-distributive-flat-product'
  retraction-inv-distributive-flat-product = map-distributive-flat-product , is-retraction-map-distributive-flat-product

  section-inv-distributive-flat-product : section map-inv-distributive-flat-product'
  section-inv-distributive-flat-product = map-distributive-flat-product , is-section-map-distributive-flat-product

  is-equiv-map-inv-distributive-flat-product : is-equiv map-inv-distributive-flat-product
  is-equiv-map-inv-distributive-flat-product = section-inv-distributive-flat-product , retraction-inv-distributive-flat-product

-- Axioms defined in Real Cohesive HoTT (Shulman)

-- Axiom C0, Cohesion

Axiom-C0 :
  ∀ {@♭ l1 l2} {@♭ I : UU l1}
  → (@♭ R : I → UU l2)
  → UUω
Axiom-C0 R =
    {@♭ l : Level}
  → (@♭ A : UU l)
  → (is-flat-discrete-crisp A)
  ≃ (∀ i → is-equiv (const (R i) {A}))
