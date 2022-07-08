---
title: Surjective maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.surjective-maps where

open import foundation.constant-maps using (const)
open import foundation.contractible-maps using
  ( is-equiv-is-contr-map)
open import foundation.contractible-types using (is-equiv-diagonal-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using
  ( _↪_; map-emb; is-emb)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; is-equiv-comp'; _≃_; map-equiv; _∘e_; inv-equiv)
open import foundation.fibers-of-maps using
  ( fib; is-equiv-map-reduce-Π-fib; reduce-Π-fib)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( is-equiv-map-Π; equiv-map-Π)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (refl; _∙_; inv; equiv-tr)
open import foundation.injective-maps using (is-injective-is-emb)
open import foundation.propositional-maps using
  ( is-prop-map-emb; is-prop-map-is-emb; fib-emb-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop; trunc-Prop; is-prop-type-trunc-Prop;
    is-propositional-truncation-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-proof-irrelevant-is-prop)
open import foundation.sections using (sec)
open import foundation.slice using
  ( hom-slice; map-hom-slice; equiv-hom-slice-fiberwise-hom;
    equiv-fiberwise-hom-hom-slice)
open import foundation.universal-property-propositional-truncation using
  ( dependent-universal-property-propositional-truncation)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A map `f : A → B` is surjective if all of its fibers are inhabited.

## Definition

```agda

is-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-surjective {B = B} f = (y : B) → type-trunc-Prop (fib f y)


_↠_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠ B = Σ (A → B) is-surjective

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (f : A ↠ B)
  where

  map-surjection : A → B
  map-surjection = pr1 f

  is-surjective-map-surjection : is-surjective map-surjection
  is-surjective-map-surjection = pr2 f
```

## Properties

### Any map that has a section is surjective

```agda
abstract
  is-surjective-has-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    sec f → is-surjective f
  is-surjective-has-section (pair g G) b = unit-trunc-Prop (pair (g b) (G b))
```

### Any equivalence is surjective

```agda
abstract
  is-surjective-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-surjective f
  is-surjective-is-equiv H = is-surjective-has-section (pr1 H)
```

### The dependent universal property of surjective maps

```
dependent-universal-property-surj :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  UU ((lsuc l) ⊔ l1 ⊔ l2)
dependent-universal-property-surj l {B = B} f =
  (P : B → UU-Prop l) →
    is-equiv (λ (h : (b : B) → type-Prop (P b)) x → h (f x))

abstract
  is-surjective-dependent-universal-property-surj :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ({l : Level} → dependent-universal-property-surj l f) →
    is-surjective f
  is-surjective-dependent-universal-property-surj f dup-surj-f =
    map-inv-is-equiv
      ( dup-surj-f (λ b → trunc-Prop (fib f b)))
      ( λ x → unit-trunc-Prop (pair x refl))

abstract
  square-dependent-universal-property-surj :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    (P : B → UU-Prop l3) →
    ( λ (h : (y : B) → type-Prop (P y)) x → h (f x)) ~
    ( ( λ h x → h (f x) (pair x refl)) ∘
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))))
  square-dependent-universal-property-surj f P = refl-htpy

  dependent-universal-property-surj-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective f →
    ({l : Level} → dependent-universal-property-surj l f)
  dependent-universal-property-surj-is-surjective f is-surj-f P =
    is-equiv-comp'
      ( λ h x → h (f x) (pair x refl))
      ( ( λ h y → (h y) ∘ unit-trunc-Prop) ∘
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y)))
      ( is-equiv-comp'
        ( λ h y → (h y) ∘ unit-trunc-Prop)
        ( λ h y → const (type-trunc-Prop (fib f y)) (type-Prop (P y)) (h y))
        ( is-equiv-map-Π
          ( λ y p z → p)
          ( λ y →
            is-equiv-diagonal-is-contr
              ( is-proof-irrelevant-is-prop
                ( is-prop-type-trunc-Prop)
                ( is-surj-f y))
              ( type-Prop (P y))))
        ( is-equiv-map-Π
          ( λ b g → g ∘ unit-trunc-Prop)
          ( λ b → is-propositional-truncation-trunc-Prop (fib f b) (P b))))
      ( is-equiv-map-reduce-Π-fib f ( λ y z → type-Prop (P y)))

equiv-dependent-universal-property-surj-is-surjective :
  {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-surjective f → (C : B → UU-Prop l) →
  ((b : B) → type-Prop (C b)) ≃ ((a : A) → type-Prop (C (f a)))
pr1 (equiv-dependent-universal-property-surj-is-surjective f H C) h x = h (f x)
pr2 (equiv-dependent-universal-property-surj-is-surjective f H C) =
  dependent-universal-property-surj-is-surjective f H C
```

### A map into a proposition is a propositional truncation if and only if it is surjective

```agda
abstract
  is-surjective-is-propositional-truncation :
    {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    is-surjective f
  is-surjective-is-propositional-truncation f duppt-f =
    is-surjective-dependent-universal-property-surj f duppt-f

abstract
  is-propsitional-truncation-is-surjective :
    {l1 l2 : Level} {A : UU l1} {P : UU-Prop l2} (f : A → type-Prop P) →
    is-surjective f →
    {l : Level} → dependent-universal-property-propositional-truncation l P f
  is-propsitional-truncation-is-surjective f is-surj-f =
    dependent-universal-property-surj-is-surjective f is-surj-f
```

### A map that is both surjective and an embedding is an equivalence

```agda
abstract
  is-equiv-is-emb-is-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-surjective f → is-emb f → is-equiv f
  is-equiv-is-emb-is-surjective {f = f} H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb K y)
          ( apply-universal-property-trunc-Prop
            ( H y)
            ( fib-emb-Prop (pair f K) y)
            ( id)))
```

### The composite of surjective maps is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-surjective-comp :
      is-surjective g → is-surjective h → is-surjective f
    is-surjective-comp Sg Sh x =
      apply-universal-property-trunc-Prop
        ( Sg x)
        ( trunc-Prop (fib f x))
        ( λ { (pair b refl) →
              apply-universal-property-trunc-Prop
                ( Sh b)
                ( trunc-Prop (fib f (g b)))
                ( λ { (pair a refl) →
                  unit-trunc-Prop (pair a (H a))})})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  abstract
    is-surjective-comp' :
      {h : A → B} → is-surjective g → is-surjective h → is-surjective (g ∘ h)
    is-surjective-comp' {h} =
      is-surjective-comp (g ∘ h) g h refl-htpy
```

### If a composite is surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-surjective-left-factor :
      is-surjective f → is-surjective g
    is-surjective-left-factor Sf x =
      apply-universal-property-trunc-Prop
        ( Sf x)
        ( trunc-Prop (fib g x))
        ( λ { (pair a refl) →
              unit-trunc-Prop (pair (h a) (inv (H a)))})

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {g : B → X}
  where

  abstract
    is-surjective-left-factor' :
      (h : A → B) → is-surjective (g ∘ h) → is-surjective g
    is-surjective-left-factor' h =
      is-surjective-left-factor (g ∘ h) g h refl-htpy
```
