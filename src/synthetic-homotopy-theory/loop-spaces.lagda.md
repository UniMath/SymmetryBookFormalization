# Loop spaces

```agda
module synthetic-homotopy-theory.loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.pointed-equivalences
open import structured-types.pointed-types
open import structured-types.wild-quasigroups
```

</details>

## Idea

The
{{#concept "loop space" Disambiguation="of a pointed type" WD="loop space" WDID=Q2066070 Agda=Ω}}
of a [pointed type](structured-types.pointed-types.md) `A` is the pointed type
of self-[identifications](foundation-core.identity-types.md) of the base point
of `A`. The loop space comes equipped with a group-like structure induced by the
groupoidal-like structure on identifications.

## Table of files directly related to loop spaces

{{#include tables/loop-spaces-concepts.md}}

## Definitions

### The loop space of a pointed type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Ω : UU l
  type-Ω = (point-Pointed-Type A ＝ point-Pointed-Type A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = pair type-Ω refl-Ω
```

### The magma of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  mul-Ω : type-Ω A → type-Ω A → type-Ω A
  mul-Ω x y = x ∙ y

  Ω-Magma : Magma l
  pr1 Ω-Magma = type-Ω A
  pr2 Ω-Magma = mul-Ω
```

### The H-space of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  left-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A (refl-Ω A) x ＝ x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω : (x : type-Ω A) → mul-Ω A x (refl-Ω A) ＝ x
  right-unit-law-mul-Ω x = right-unit

  coherence-unit-laws-mul-Ω :
    left-unit-law-mul-Ω refl ＝ right-unit-law-mul-Ω refl
  coherence-unit-laws-mul-Ω = refl

  Ω-H-Space : H-Space l
  pr1 Ω-H-Space = Ω A
  pr1 (pr2 Ω-H-Space) = mul-Ω A
  pr1 (pr2 (pr2 Ω-H-Space)) = left-unit-law-mul-Ω
  pr1 (pr2 (pr2 (pr2 Ω-H-Space))) = right-unit-law-mul-Ω
  pr2 (pr2 (pr2 (pr2 Ω-H-Space))) = coherence-unit-laws-mul-Ω
```

### The wild quasigroup of loops on a pointed space

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  inv-Ω : type-Ω A → type-Ω A
  inv-Ω = inv

  left-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A (inv-Ω x) x) (refl-Ω A)
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω A) → Id (mul-Ω A x (inv-Ω x)) (refl-Ω A)
  right-inverse-law-mul-Ω x = right-inv x

  Ω-Wild-Quasigroup : Wild-Quasigroup l
  pr1 Ω-Wild-Quasigroup = Ω-Magma A
  pr2 Ω-Wild-Quasigroup = is-binary-equiv-concat
```

### Associativity of concatenation on loop spaces

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  associative-mul-Ω :
    (x y z : type-Ω A) →
    Id (mul-Ω A (mul-Ω A x y) z) (mul-Ω A x (mul-Ω A y z))
  associative-mul-Ω x y z = assoc x y z
```

We compute transport of `type-Ω`.

```agda
module _
  {l1 : Level} {A : UU l1} {x y : A}
  where

  equiv-tr-Ω : Id x y → Ω (pair A x) ≃∗ Ω (pair A y)
  equiv-tr-Ω refl = pair id-equiv refl

  equiv-tr-type-Ω : Id x y → type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (equiv-tr-Ω p)

  tr-type-Ω : Id x y → type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  is-equiv-tr-type-Ω : (p : Id x y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : Id x y) → Id (tr-type-Ω p refl) refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : Id x y) (u v : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (mul-Ω (pair A x) u v))
      ( mul-Ω (pair A y) (tr-type-Ω p u) (tr-type-Ω p v))
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : Id x y) (u : type-Ω (pair A x)) →
    Id
      ( tr-type-Ω p (inv-Ω (pair A x) u))
      ( inv-Ω (pair A y) (tr-type-Ω p u))
  preserves-inv-tr-Ω refl u = refl

  eq-tr-type-Ω :
    (p : Id x y) (q : type-Ω (pair A x)) →
    Id (tr-type-Ω p q) (inv p ∙ (q ∙ p))
  eq-tr-type-Ω refl q = inv right-unit
```

## Properties

### Every pointed identity type is equivalent to a loop space

```agda
module _
  {l : Level} (A : Pointed-Type l) {x : type-Pointed-Type A}
  (p : point-Pointed-Type A ＝ x)
  where

  pointed-equiv-loop-pointed-identity :
    ( pair (point-Pointed-Type A ＝ x) p) ≃∗ Ω A
  pr1 pointed-equiv-loop-pointed-identity =
    equiv-concat' (point-Pointed-Type A) (inv p)
  pr2 pointed-equiv-loop-pointed-identity =
    right-inv p
```

### The loop space as a pullback

The loop space of `A` is the pullback

```text
  Ω A ------> *
   | ⌟        |
   |          |
   ∨          ∨
   * -------> A
```

in the category of pointed types. Equivalently, it is the pullback of types

```text
  Ω A ------> *
   | ⌟        |
   |          | a
   ∨          ∨
   * -------> A
        a
```

where `a` is the base point of `A`.

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  cone-type-Ω :
    cone (point-point-Pointed-Type A) (point-point-Pointed-Type A) (type-Ω A)
  cone-type-Ω = cone-Id (point-Pointed-Type A) (point-Pointed-Type A)

  is-pullback-type-Ω :
    is-pullback
      ( point-point-Pointed-Type A)
      ( point-point-Pointed-Type A)
      ( cone-type-Ω)
  is-pullback-type-Ω =
    is-pullback-Id (point-Pointed-Type A) (point-Pointed-Type A)
```
