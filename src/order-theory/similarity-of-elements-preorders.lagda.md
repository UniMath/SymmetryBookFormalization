# Similarity of elements in preorders

```agda
module order-theory.similarity-of-elements-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.reflexive-relations
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

Two elements `x` and `y` of a [preorder](order-theory.preorders.md) `P` are said
to be
{{#concept "similar" Disambiguation="elements of a preorder" Agda=sim-Preorder}}
if both `x ≤ y` and `y ≤ x` hold.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a preorder `P`.

## Definitions

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  sim-prop-Preorder : (x y : type-Preorder P) → Prop l2
  sim-prop-Preorder x y =
    product-Prop (leq-prop-Preorder P x y) (leq-prop-Preorder P y x)

  sim-Preorder :
    (x y : type-Preorder P) → UU l2
  sim-Preorder x y = type-Prop (sim-prop-Preorder x y)

  is-prop-sim-Preorder :
    (x y : type-Preorder P) → is-prop (sim-Preorder x y)
  is-prop-sim-Preorder x y =
    is-prop-type-Prop (sim-prop-Preorder x y)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  refl-sim-Preorder :
    is-reflexive-Relation-Prop (sim-prop-Preorder P)
  refl-sim-Preorder x = refl-leq-Preorder P x , refl-leq-Preorder P x
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  transitive-sim-Preorder :
    is-transitive-Relation-Prop (sim-prop-Preorder P)
  transitive-sim-Preorder x y z H K =
    ( transitive-leq-Preorder P x y z (pr1 H) (pr1 K) ,
      transitive-leq-Preorder P z y x (pr2 K) (pr2 H))
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  symmetric-sim-Preorder : is-symmetric-Relation-Prop (sim-prop-Preorder P)
  symmetric-sim-Preorder _ _ H = (pr2 H , pr1 H)
```

### Equal elements are similar

```agda
module _
  {l1 l2 : Level} (P : Preorder l1 l2)
  where

  sim-eq-Preorder : {x y : type-Preorder P} → x ＝ y → sim-Preorder P x y
  sim-eq-Preorder {x} refl = refl-sim-Preorder P x
```
