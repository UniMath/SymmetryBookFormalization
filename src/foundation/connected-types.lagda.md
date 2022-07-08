---
title: Connected types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.connected-types where

open import foundation.contractible-types using
  ( is-contr-Prop; center; eq-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; _∘e_; map-inv-equiv)
open import foundation.fiber-inclusions using (fiber-inclusion)
open import foundation.fibers-of-maps using (fib)
open import foundation.identity-types using (ap; refl)
open import foundation.mere-equality using (mere-eq; mere-eq-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; trunc-Prop; unit-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using (UU-Prop; is-prop; type-Prop)
open import foundation.set-truncations using
  ( type-trunc-Set; apply-universal-property-trunc-Set'; unit-trunc-Set;
    apply-effectiveness-unit-trunc-Set; trunc-Set;
    apply-dependent-universal-property-trunc-Set';
    apply-effectiveness-unit-trunc-Set')
open import foundation.sets using (set-Prop; Id-Prop)
open import foundation.surjective-maps using
  ( is-surjective; equiv-dependent-universal-property-surj-is-surjective)
open import foundation.unit-type using (star; unit; pt)
open import foundation.universal-property-unit-type using
  ( equiv-universal-property-unit)
open import foundation.universe-levels using (Level; UU)
```

## Idea

A type is said to be connected if its type of connected components, i.e., its set truncation, is contractible.

```agda
is-path-connected-Prop : {l : Level} → UU l → UU-Prop l
is-path-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-path-connected : {l : Level} → UU l → UU l
is-path-connected A = type-Prop (is-path-connected-Prop A)

abstract
  is-inhabited-is-path-connected :
    {l : Level} {A : UU l} → is-path-connected A → type-trunc-Prop A
  is-inhabited-is-path-connected {l} {A} C =
    apply-universal-property-trunc-Set'
      ( center C)
      ( set-Prop (trunc-Prop A))
      ( unit-trunc-Prop)

abstract
  mere-eq-is-path-connected :
    {l : Level} {A : UU l} → is-path-connected A → (x y : A) → mere-eq x y
  mere-eq-is-path-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)

abstract
  is-path-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-path-connected A
  is-path-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

is-path-connected-is-surjective-pt :
  {l1 : Level} {A : UU l1} (a : A) →
  is-surjective (pt a) → is-path-connected A
is-path-connected-is-surjective-pt a H =
  is-path-connected-mere-eq a
    ( λ x →
      apply-universal-property-trunc-Prop
        ( H x)
        ( mere-eq-Prop a x)
        ( λ u → unit-trunc-Prop (pr2 u)))

is-surjective-pt-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) →
  is-path-connected A → is-surjective (pt a)
is-surjective-pt-is-path-connected a H x =
  apply-universal-property-trunc-Prop
    ( mere-eq-is-path-connected H a x)
    ( trunc-Prop (fib (pt a) x))
    ( λ {refl → unit-trunc-Prop (pair star refl)})

equiv-dependent-universal-property-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-path-connected A →
  ( {l : Level} (P : A → UU-Prop l) →
    ((x : A) → type-Prop (P x)) ≃ type-Prop (P a))
equiv-dependent-universal-property-is-path-connected a H P =
  ( equiv-universal-property-unit (type-Prop (P a))) ∘e
  ( equiv-dependent-universal-property-surj-is-surjective
    ( pt a)
    ( is-surjective-pt-is-path-connected a H)
    ( P))

apply-dependent-universal-property-is-path-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-path-connected A →
  {l : Level} (P : A → UU-Prop l) → type-Prop (P a) → (x : A) → type-Prop (P x)
apply-dependent-universal-property-is-path-connected a H P =
  map-inv-equiv (equiv-dependent-universal-property-is-path-connected a H P)

abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-path-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (pair x b) =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-path-connected C a x)
      ( trunc-Prop (fib (fiber-inclusion B a) (pair x b)))
      ( λ { refl → unit-trunc-Prop (pair b refl)})

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x =
    apply-universal-property-trunc-Prop
      ( H (λ x → unit) (pair x star))
      ( mere-eq-Prop a x)
      ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

abstract
  is-path-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-path-connected A
  is-path-connected-is-surjective-fiber-inclusion a H =
    is-path-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)
```
