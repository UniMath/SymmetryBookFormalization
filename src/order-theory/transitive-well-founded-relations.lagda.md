# Transitive well-founded relations

```agda
module order-theory.transitive-well-founded-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.well-founded-relations
```

</details>

## Idea

A
{{#concept "transitive well-founded relation" Agda=Transitive-Well-Founded-Relation}}
is a [transitive](foundation.binary-relations.md)
[well-founded relation](order-theory.well-founded-relations.md).

## Definitions

### The predicate of being a transitive well-founded relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Relation l2 X)
  where

  is-transitive-well-founded-relation-Relation : UU (l1 ⊔ l2)
  is-transitive-well-founded-relation-Relation =
    is-well-founded-Relation R × is-transitive R
```

### Transitive well-founded relations

```agda
Transitive-Well-Founded-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Transitive-Well-Founded-Relation l2 X =
  Σ (Relation l2 X) is-transitive-well-founded-relation-Relation

module _
  {l1 l2 : Level} {X : UU l1} (R : Transitive-Well-Founded-Relation l2 X)
  where

  le-Transitive-Well-Founded-Relation : Relation l2 X
  le-Transitive-Well-Founded-Relation = pr1 R

  is-transitive-well-founded-relation-Transitive-Well-Founded-Relation :
    is-transitive-well-founded-relation-Relation
      le-Transitive-Well-Founded-Relation
  is-transitive-well-founded-relation-Transitive-Well-Founded-Relation = pr2 R

  is-well-founded-relation-le-Transitive-Well-Founded-Relation :
    is-well-founded-Relation le-Transitive-Well-Founded-Relation
  is-well-founded-relation-le-Transitive-Well-Founded-Relation =
    pr1 is-transitive-well-founded-relation-Transitive-Well-Founded-Relation

  transitive-le-Transitive-Well-Founded-Relation :
    is-transitive le-Transitive-Well-Founded-Relation
  transitive-le-Transitive-Well-Founded-Relation =
    pr2 is-transitive-well-founded-relation-Transitive-Well-Founded-Relation

  well-founded-relation-Transitive-Well-Founded-Relation :
    Well-Founded-Relation l2 X
  pr1 well-founded-relation-Transitive-Well-Founded-Relation =
    le-Transitive-Well-Founded-Relation
  pr2 well-founded-relation-Transitive-Well-Founded-Relation =
    is-well-founded-relation-le-Transitive-Well-Founded-Relation

  is-asymmetric-le-Transitive-Well-Founded-Relation :
    is-asymmetric le-Transitive-Well-Founded-Relation
  is-asymmetric-le-Transitive-Well-Founded-Relation =
    is-asymmetric-le-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation)

  is-irreflexive-le-Transitive-Well-Founded-Relation :
    is-irreflexive le-Transitive-Well-Founded-Relation
  is-irreflexive-le-Transitive-Well-Founded-Relation =
    is-irreflexive-le-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation)
```

### The associated reflexive relation of a transitive well-founded relation

Given a transitive well-founded relation $∈$ there is an associated reflexive
relation given by

$$
  (x ≤ y) := (u : X) → (u ∈ x) → (u ∈ y).
$$

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Transitive-Well-Founded-Relation l2 X)
  where

  leq-Transitive-Well-Founded-Relation :
    Relation (l1 ⊔ l2) X
  leq-Transitive-Well-Founded-Relation =
    leq-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation R)

  refl-leq-Transitive-Well-Founded-Relation :
    is-reflexive leq-Transitive-Well-Founded-Relation
  refl-leq-Transitive-Well-Founded-Relation =
    refl-leq-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation R)

  leq-eq-Transitive-Well-Founded-Relation :
    {x y : X} → x ＝ y → leq-Transitive-Well-Founded-Relation x y
  leq-eq-Transitive-Well-Founded-Relation =
    leq-eq-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation R)

  transitive-leq-Transitive-Well-Founded-Relation :
    is-transitive leq-Transitive-Well-Founded-Relation
  transitive-leq-Transitive-Well-Founded-Relation =
    transitive-leq-Well-Founded-Relation
      ( well-founded-relation-Transitive-Well-Founded-Relation R)
```

## Properties

### Less than implies less than or equal for a transitive well-founded relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Transitive-Well-Founded-Relation l2 X)
  where

  leq-le-Transitive-Well-Founded-Relation :
    {x y : X} →
    le-Transitive-Well-Founded-Relation R x y →
    leq-Transitive-Well-Founded-Relation R x y
  leq-le-Transitive-Well-Founded-Relation {x} {y} p u q =
    transitive-le-Transitive-Well-Founded-Relation R u x y p q
```
