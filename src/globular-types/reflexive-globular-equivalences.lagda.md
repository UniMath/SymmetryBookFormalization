# Reflexive globular equivalences

```agda
{-# OPTIONS --guardedness #-}

module globular-types.reflexive-globular-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-equivalences
open import globular-types.globular-maps
open import globular-types.reflexive-globular-maps
open import globular-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "reflexive globular equivalence" Agda=reflexive-globular-equiv}}
`e` between
[reflexive-globular types](globular-types.reflexive-globular-types.md) `A` and
`B` is a [globular equivalence](globular-types.globular-equivalences.md) that
preserves reflexivity.

## Definitions

### The predicate on globular equivalences of preserving reflexivity

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Globular-Type l1 l2)
  (H : Reflexive-Globular-Type l3 l4)
  where

  preserves-refl-globular-equiv :
    globular-equiv
      ( globular-type-Reflexive-Globular-Type G)
      ( globular-type-Reflexive-Globular-Type H) →
    UU (l1 ⊔ l2 ⊔ l4)
  preserves-refl-globular-equiv e =
    preserves-refl-globular-map G H (globular-map-globular-equiv e)
```

### Equivalences between globular types

```agda
record
  reflexive-globular-equiv
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-equiv-reflexive-globular-equiv :
      globular-equiv
        ( globular-type-Reflexive-Globular-Type G)
        ( globular-type-Reflexive-Globular-Type H)

  0-cell-equiv-reflexive-globular-equiv :
    0-cell-Reflexive-Globular-Type G ≃ 0-cell-Reflexive-Globular-Type H
  0-cell-equiv-reflexive-globular-equiv =
    0-cell-globular-equiv globular-equiv-reflexive-globular-equiv

  0-cell-reflexive-globular-equiv :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-reflexive-globular-equiv =
    0-cell-map-globular-equiv globular-equiv-reflexive-globular-equiv

  1-cell-equiv-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y ≃
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-reflexive-globular-equiv x)
      ( 0-cell-reflexive-globular-equiv y)
  1-cell-equiv-reflexive-globular-equiv =
    1-cell-equiv-globular-equiv globular-equiv-reflexive-globular-equiv

  1-cell-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y →
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-reflexive-globular-equiv x)
      ( 0-cell-reflexive-globular-equiv y)
  1-cell-reflexive-globular-equiv =
    1-cell-map-globular-equiv globular-equiv-reflexive-globular-equiv

  1-cell-globular-equiv-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-equiv
      ( 1-cell-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-globular-type-Reflexive-Globular-Type H
        ( 0-cell-reflexive-globular-equiv x)
        ( 0-cell-reflexive-globular-equiv y))
  1-cell-globular-equiv-reflexive-globular-equiv =
    1-cell-globular-equiv-globular-equiv
      globular-equiv-reflexive-globular-equiv

  2-cell-equiv-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G}
    {f g : 1-cell-Reflexive-Globular-Type G x y} →
    2-cell-Reflexive-Globular-Type G f g ≃
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-reflexive-globular-equiv f)
      ( 1-cell-reflexive-globular-equiv g)
  2-cell-equiv-reflexive-globular-equiv =
    2-cell-equiv-globular-equiv globular-equiv-reflexive-globular-equiv

  2-cell-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G}
    {f g : 1-cell-Reflexive-Globular-Type G x y} →
    2-cell-Reflexive-Globular-Type G f g →
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-reflexive-globular-equiv f)
      ( 1-cell-reflexive-globular-equiv g)
  2-cell-reflexive-globular-equiv =
    2-cell-globular-equiv globular-equiv-reflexive-globular-equiv

  3-cell-equiv-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G}
    {f g : 1-cell-Reflexive-Globular-Type G x y} →
    {s t : 2-cell-Reflexive-Globular-Type G f g} →
    3-cell-Reflexive-Globular-Type G s t ≃
    3-cell-Reflexive-Globular-Type H
      ( 2-cell-reflexive-globular-equiv s)
      ( 2-cell-reflexive-globular-equiv t)
  3-cell-equiv-reflexive-globular-equiv =
    3-cell-equiv-globular-equiv globular-equiv-reflexive-globular-equiv

  globular-map-reflexive-globular-equiv :
    globular-map
      ( globular-type-Reflexive-Globular-Type G)
      ( globular-type-Reflexive-Globular-Type H)
  globular-map-reflexive-globular-equiv =
    globular-map-globular-equiv globular-equiv-reflexive-globular-equiv

  field
    preserves-refl-reflexive-globular-equiv :
      preserves-refl-globular-equiv G H globular-equiv-reflexive-globular-equiv

  preserves-refl-1-cell-reflexive-globular-equiv :
    (x : 0-cell-Reflexive-Globular-Type G) →
    1-cell-reflexive-globular-equiv
      ( refl-1-cell-Reflexive-Globular-Type G {x}) ＝
    refl-1-cell-Reflexive-Globular-Type H
  preserves-refl-1-cell-reflexive-globular-equiv =
    preserves-refl-1-cell-preserves-refl-globular-map
      preserves-refl-reflexive-globular-equiv

  preserves-refl-1-cell-globular-equiv-reflexive-globular-equiv :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    preserves-refl-globular-equiv
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
      ( 1-cell-globular-equiv-reflexive-globular-equiv)
  preserves-refl-1-cell-globular-equiv-reflexive-globular-equiv =
    preserves-refl-1-cell-globular-map-preserves-refl-globular-map
      preserves-refl-reflexive-globular-equiv

  1-cell-reflexive-globular-equiv-reflexive-globular-equiv :
    (x y : 0-cell-Reflexive-Globular-Type G) →
    reflexive-globular-equiv
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
  globular-equiv-reflexive-globular-equiv
    ( 1-cell-reflexive-globular-equiv-reflexive-globular-equiv x y) =
    1-cell-globular-equiv-reflexive-globular-equiv
  preserves-refl-reflexive-globular-equiv
    ( 1-cell-reflexive-globular-equiv-reflexive-globular-equiv x y) =
    preserves-refl-1-cell-globular-equiv-reflexive-globular-equiv

open reflexive-globular-equiv public
```

### The identity equivalence on a reflexive globular type

```agda
preserves-refl-id-globular-equiv :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  preserves-refl-globular-equiv
    ( G)
    ( G)
    ( id-globular-equiv (globular-type-Reflexive-Globular-Type G))
preserves-refl-1-cell-preserves-refl-globular-map
  ( preserves-refl-id-globular-equiv G)
  ( x) =
  refl
preserves-refl-1-cell-globular-map-preserves-refl-globular-map
  ( preserves-refl-id-globular-equiv G) =
  preserves-refl-id-globular-equiv
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G _ _)

id-reflexive-globular-equiv :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  reflexive-globular-equiv G G
globular-equiv-reflexive-globular-equiv (id-reflexive-globular-equiv G) =
  id-globular-equiv (globular-type-Reflexive-Globular-Type G)
preserves-refl-reflexive-globular-equiv (id-reflexive-globular-equiv G) =
  preserves-refl-id-globular-equiv G
```

### Composition of equivalences of reflexive globular types

```agda
globular-equiv-comp-reflexive-globular-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2}
  {H : Reflexive-Globular-Type l3 l4}
  {K : Reflexive-Globular-Type l5 l6} →
  (f : reflexive-globular-equiv H K)
  (e : reflexive-globular-equiv G H) →
  globular-equiv
    ( globular-type-Reflexive-Globular-Type G)
    ( globular-type-Reflexive-Globular-Type K)
globular-equiv-comp-reflexive-globular-equiv f e =
  comp-globular-equiv
    ( globular-equiv-reflexive-globular-equiv f)
    ( globular-equiv-reflexive-globular-equiv e)

preserves-refl-comp-reflexive-globular-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2}
  {H : Reflexive-Globular-Type l3 l4}
  {K : Reflexive-Globular-Type l5 l6} →
  (g : reflexive-globular-equiv H K)
  (f : reflexive-globular-equiv G H) →
  preserves-refl-globular-equiv G K
    ( globular-equiv-comp-reflexive-globular-equiv g f)
preserves-refl-1-cell-preserves-refl-globular-map
  ( preserves-refl-comp-reflexive-globular-equiv g f) x =
  ( ap
    ( 1-cell-reflexive-globular-equiv g)
    ( preserves-refl-1-cell-reflexive-globular-equiv f _)) ∙
  ( preserves-refl-1-cell-reflexive-globular-equiv g _)
preserves-refl-1-cell-globular-map-preserves-refl-globular-map
  ( preserves-refl-comp-reflexive-globular-equiv g f) =
  preserves-refl-comp-reflexive-globular-equiv
    ( 1-cell-reflexive-globular-equiv-reflexive-globular-equiv g _ _)
    ( 1-cell-reflexive-globular-equiv-reflexive-globular-equiv f _ _)

comp-reflexive-globular-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2}
  {H : Reflexive-Globular-Type l3 l4}
  {K : Reflexive-Globular-Type l5 l6} →
  reflexive-globular-equiv H K →
  reflexive-globular-equiv G H →
  reflexive-globular-equiv G K
globular-equiv-reflexive-globular-equiv
  ( comp-reflexive-globular-equiv g f) =
  globular-equiv-comp-reflexive-globular-equiv g f
preserves-refl-reflexive-globular-equiv (comp-reflexive-globular-equiv g f) =
  preserves-refl-comp-reflexive-globular-equiv g f
```
