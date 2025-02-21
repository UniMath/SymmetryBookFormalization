# Similarity of elements in large preorders

```agda
module order-theory.similarity-of-elements-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

Two elements `x` and `y` of a [large preorder](order-theory.large-preorders.md)
`P` are said to be
{{#concept "similar" Disambiguation="elements of a large preorder" Agda=sim-Large-Preorder}}
if both `x ≤ y` and `y ≤ x` hold.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a large preorder `P`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  sim-prop-Large-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Preorder P l1) (y : type-Large-Preorder P l2) →
    Prop (β l1 l2 ⊔ β l2 l1)
  sim-prop-Large-Preorder x y =
    product-Prop
      ( leq-prop-Large-Preorder P x y)
      ( leq-prop-Large-Preorder P y x)

  sim-Large-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Preorder P l1) (y : type-Large-Preorder P l2) →
    UU (β l1 l2 ⊔ β l2 l1)
  sim-Large-Preorder x y = type-Prop (sim-prop-Large-Preorder x y)

  is-prop-sim-Large-Preorder :
    {l1 l2 : Level}
    (x : type-Large-Preorder P l1) (y : type-Large-Preorder P l2) →
    is-prop (sim-Large-Preorder x y)
  is-prop-sim-Large-Preorder x y =
    is-prop-type-Prop (sim-prop-Large-Preorder x y)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  refl-sim-Large-Preorder :
    is-reflexive-Large-Relation (type-Large-Preorder P) (sim-Large-Preorder P)
  pr1 (refl-sim-Large-Preorder x) = refl-leq-Large-Preorder P x
  pr2 (refl-sim-Large-Preorder x) = refl-leq-Large-Preorder P x
```

### The similarity relation is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  transitive-sim-Large-Preorder :
    is-transitive-Large-Relation (type-Large-Preorder P) (sim-Large-Preorder P)
  pr1 (transitive-sim-Large-Preorder x y z H K) =
    transitive-leq-Large-Preorder P x y z (pr1 H) (pr1 K)
  pr2 (transitive-sim-Large-Preorder x y z H K) =
    transitive-leq-Large-Preorder P z y x (pr2 K) (pr2 H)
```

### The similarity relation is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  symmetric-sim-Large-Preorder :
    is-symmetric-Large-Relation (type-Large-Preorder P) (sim-Large-Preorder P)
  pr1 (symmetric-sim-Large-Preorder _ _ H) = pr2 H
  pr2 (symmetric-sim-Large-Preorder _ _ H) = pr1 H
```

### Equal elements are similar

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  sim-eq-Large-Preorder :
    {l : Level} {x y : type-Large-Preorder P l} →
    x ＝ y → sim-Large-Preorder P x y
  sim-eq-Large-Preorder refl = refl-sim-Large-Preorder P _
```
