---
title: Inequality on types equipped with a counting
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.inequality-types-with-counting where

open import elementary-number-theory.inequality-standard-finite-types using
  ( leq-Fin; refl-leq-Fin; antisymmetric-leq-Fin; transitive-leq-Fin;
    concatenate-eq-leq-eq-Fin)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( map-inv-equiv; isretr-map-inv-equiv)
open import foundation.identity-types using (Id; refl; inv)
open import foundation.injective-maps using (is-injective-map-inv-equiv)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.counting using
  ( count; map-inv-equiv-count; number-of-elements-count; map-equiv-count;
    equiv-count)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

If a type comes equipped with a counting of its elements, then it inherits the inequality relations from the standard finite types.

## Definition

```agda
leq-count :
  {l : Level} {X : UU l} → count X → X → X → UU lzero
leq-count e x y =
  leq-Fin
    ( number-of-elements-count e)
    ( map-inv-equiv-count e x)
    ( map-inv-equiv-count e y)
```

## Properties

```agda
refl-leq-count :
  {l : Level} {X : UU l} (e : count X) (x : X) → leq-count e x x
refl-leq-count e x =
  refl-leq-Fin (number-of-elements-count e) (map-inv-equiv-count e x)

antisymmetric-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y : X} →
  leq-count e x y → leq-count e y x → Id x y
antisymmetric-leq-count e H K =
  is-injective-map-inv-equiv
    ( equiv-count e)
    ( antisymmetric-leq-Fin (number-of-elements-count e) _ _ H K)

transitive-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y z : X} →
  leq-count e y z → leq-count e x y → leq-count e x z
transitive-leq-count (pair k e) {x} {y} {z} =
  transitive-leq-Fin k
    ( map-inv-equiv e x)
    ( map-inv-equiv e y)
    ( map-inv-equiv-count (pair k e) z)

preserves-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-Fin (number-of-elements-count e) x y →
  leq-count e (map-equiv-count e x) (map-equiv-count e y)
preserves-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

reflects-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-count e (map-equiv-count e x) (map-equiv-count e y) →
  leq-Fin (number-of-elements-count e) x y
reflects-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( inv (isretr-map-inv-equiv (equiv-count e) x))
    ( H)
    ( isretr-map-inv-equiv (equiv-count e) y)

transpose-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X) →
  {x : Fin (number-of-elements-count e)} {y : X} →
  leq-Fin
    ( number-of-elements-count e) x (map-inv-equiv-count e y) →
  leq-count e (map-equiv-count e x) y
transpose-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( refl)

transpose-leq-equiv-count' :
  {l : Level} {X : UU l} (e : count X) →
  {x : X} {y : Fin (number-of-elements-count e)} →
  leq-Fin (number-of-elements-count e) (map-inv-equiv-count e x) y →
  leq-count e x (map-equiv-count e y)
transpose-leq-equiv-count' e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( refl)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))
```
