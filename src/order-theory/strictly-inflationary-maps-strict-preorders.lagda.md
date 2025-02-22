# Strictly inflationary maps on a strictly preordered type

```agda
module order-theory.strictly-inflationary-maps-strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-order-preserving-maps
open import order-theory.strict-preorders
```

</details>

## Idea

A map $f : P → P$ on a [strict preorder](order-theory.strict-preorders.md) $P$
is said to be a
{{#concept "strictly inflationary map" Disambiguation="strict preorder" Agda=strictly-inflationary-map-Strict-Preorder}}
if the inequality

$$
  x < f(x)
$$

holds for any element $x : P$. If $f$ is also
[order preserving](order-theory.strict-order-preserving-maps.md) we say that $f$
is a
{{#concept "strictly inflationary morphism" Disambiguation="strict preorder" Agda=inflationary-hom-Strict-Preorder}}.

## Definitions

### The predicate of being a strictly inflationary map

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  (f : type-Strict-Preorder P → type-Strict-Preorder P)
  where

  is-strictly-inflationary-map-prop-Strict-Preorder :
    Prop (l1 ⊔ l2)
  is-strictly-inflationary-map-prop-Strict-Preorder =
    Π-Prop
      ( type-Strict-Preorder P)
      ( λ x → le-prop-Strict-Preorder P x (f x))

  is-strictly-inflationary-map-Strict-Preorder :
    UU (l1 ⊔ l2)
  is-strictly-inflationary-map-Strict-Preorder =
    type-Prop is-strictly-inflationary-map-prop-Strict-Preorder

  is-prop-is-strictly-inflationary-map-Strict-Preorder :
    is-prop is-strictly-inflationary-map-Strict-Preorder
  is-prop-is-strictly-inflationary-map-Strict-Preorder =
    is-prop-type-Prop is-strictly-inflationary-map-prop-Strict-Preorder
```

### The type of inflationary maps on a strict preorder

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  strictly-inflationary-map-Strict-Preorder :
    UU (l1 ⊔ l2)
  strictly-inflationary-map-Strict-Preorder =
    type-subtype (is-strictly-inflationary-map-prop-Strict-Preorder P)

module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  (f : strictly-inflationary-map-Strict-Preorder P)
  where

  map-strictly-inflationary-map-Strict-Preorder :
    type-Strict-Preorder P → type-Strict-Preorder P
  map-strictly-inflationary-map-Strict-Preorder =
    pr1 f

  is-strictly-inflationary-strictly-inflationary-map-Strict-Preorder :
    is-strictly-inflationary-map-Strict-Preorder P
      ( map-strictly-inflationary-map-Strict-Preorder)
  is-strictly-inflationary-strictly-inflationary-map-Strict-Preorder =
    pr2 f
```

### The predicate on order preserving maps of being inflationary

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  (f : hom-Strict-Preorder P P)
  where

  is-inflationary-prop-hom-Strict-Preorder :
    Prop (l1 ⊔ l2)
  is-inflationary-prop-hom-Strict-Preorder =
    is-strictly-inflationary-map-prop-Strict-Preorder P
      ( map-hom-Strict-Preorder P P f)

  is-inflationary-hom-Strict-Preorder :
    UU (l1 ⊔ l2)
  is-inflationary-hom-Strict-Preorder =
    is-strictly-inflationary-map-Strict-Preorder P
      ( map-hom-Strict-Preorder P P f)

  is-prop-is-inflationary-hom-Strict-Preorder :
    is-prop is-inflationary-hom-Strict-Preorder
  is-prop-is-inflationary-hom-Strict-Preorder =
    is-prop-is-strictly-inflationary-map-Strict-Preorder P
      ( map-hom-Strict-Preorder P P f)
```

### The type of inflationary morphisms on a strict preorder

```agda
module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  where

  inflationary-hom-Strict-Preorder :
    UU (l1 ⊔ l2)
  inflationary-hom-Strict-Preorder =
    type-subtype (is-inflationary-prop-hom-Strict-Preorder P)

module _
  {l1 l2 : Level} (P : Strict-Preorder l1 l2)
  (f : inflationary-hom-Strict-Preorder P)
  where

  hom-inflationary-hom-Strict-Preorder :
    hom-Strict-Preorder P P
  hom-inflationary-hom-Strict-Preorder =
    pr1 f

  map-inflationary-hom-Strict-Preorder :
    type-Strict-Preorder P → type-Strict-Preorder P
  map-inflationary-hom-Strict-Preorder =
    map-hom-Strict-Preorder P P
      ( hom-inflationary-hom-Strict-Preorder)

  preserves-order-inflationary-hom-Strict-Preorder :
    preserves-strict-order-map-Strict-Preorder P P
      ( map-inflationary-hom-Strict-Preorder)
  preserves-order-inflationary-hom-Strict-Preorder =
    preserves-strict-order-hom-Strict-Preorder P P
      ( hom-inflationary-hom-Strict-Preorder)

  is-inflationary-inflationary-hom-Strict-Preorder :
    is-strictly-inflationary-map-Strict-Preorder P
      ( map-inflationary-hom-Strict-Preorder)
  is-inflationary-inflationary-hom-Strict-Preorder =
    pr2 f

  inflationary-map-inflationary-hom-Strict-Preorder :
    strictly-inflationary-map-Strict-Preorder P
  pr1 inflationary-map-inflationary-hom-Strict-Preorder =
    map-inflationary-hom-Strict-Preorder
  pr2 inflationary-map-inflationary-hom-Strict-Preorder =
    is-inflationary-inflationary-hom-Strict-Preorder
```
