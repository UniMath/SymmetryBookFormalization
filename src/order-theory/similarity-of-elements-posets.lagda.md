# Similarity of elements in posets

```agda
module order-theory.similarity-of-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.similarity-of-elements-preorders
```

</details>

## Idea

Two elements `x` and `y` of a [poset](order-theory.posets.md) `P` are said to be
{{#concept "similar" Disambiguation="elements in a poset" Agda=sim-Poset}} if
both `x ≤ y` and `y ≤ x` hold. In informal writing we will use the notation
`x ≈ y` to assert that `x` and `y` are similar elements in a poset `P`.

## Definitions

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sim-prop-Poset : (x y : type-Poset P) → Prop l2
  sim-prop-Poset = sim-prop-Preorder (preorder-Poset P)

  sim-Poset : (x y : type-Poset P) → UU l2
  sim-Poset = sim-Preorder (preorder-Poset P)

  is-prop-sim-Poset : (x y : type-Poset P) → is-prop (sim-Poset x y)
  is-prop-sim-Poset = is-prop-sim-Preorder (preorder-Poset P)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  refl-sim-Poset : is-reflexive-Relation-Prop (sim-prop-Poset P)
  refl-sim-Poset = refl-sim-Preorder (preorder-Poset P)
```

### The similarity relation is transitive

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  transitive-sim-Poset : is-transitive-Relation-Prop (sim-prop-Poset P)
  transitive-sim-Poset = transitive-sim-Preorder (preorder-Poset P)
```

### The similarity relation is symmetric

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  symmetric-sim-Poset : is-symmetric-Relation-Prop (sim-prop-Poset P)
  symmetric-sim-Poset = symmetric-sim-Preorder (preorder-Poset P)
```

### Any element in a poset is similar to at most one element

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  all-elements-equal-total-sim-Poset :
    (x : type-Poset P) → all-elements-equal (Σ (type-Poset P) (sim-Poset P x))
  all-elements-equal-total-sim-Poset x (y , H) (z , K) =
    eq-type-subtype
      ( sim-prop-Poset P x)
      ( antisymmetric-leq-Poset P
        ( y)
        ( z)
        ( transitive-leq-Poset P y x z (pr1 K) (pr2 H))
        ( transitive-leq-Poset P z x y (pr1 H) (pr2 K)))

  is-prop-total-sim-Poset :
    (x : type-Poset P) → is-prop (Σ (type-Poset P) (sim-Poset P x))
  is-prop-total-sim-Poset x =
    is-prop-all-elements-equal
      ( all-elements-equal-total-sim-Poset x)

  is-torsorial-sim-Poset :
    (x : type-Poset P) → is-torsorial (sim-Poset P x)
  is-torsorial-sim-Poset x =
    is-proof-irrelevant-is-prop
      ( is-prop-total-sim-Poset x)
      ( x , refl-sim-Poset P x)
```

### Similarity characterizes the identity type of elements in a poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sim-eq-Poset : {x y : type-Poset P} → x ＝ y → sim-Poset P x y
  sim-eq-Poset = sim-eq-Preorder (preorder-Poset P)

  is-equiv-sim-eq-Poset :
    (x y : type-Poset P) → is-equiv (sim-eq-Poset {x} {y})
  is-equiv-sim-eq-Poset x =
    fundamental-theorem-id
      ( is-torsorial-sim-Poset P x)
      ( λ y → sim-eq-Poset {x} {y})

  extensionality-Poset : (x y : type-Poset P) → (x ＝ y) ≃ sim-Poset P x y
  extensionality-Poset x y = (sim-eq-Poset , is-equiv-sim-eq-Poset x y)

  eq-sim-Poset : (x y : type-Poset P) → sim-Poset P x y → x ＝ y
  eq-sim-Poset x y = map-inv-is-equiv (is-equiv-sim-eq-Poset x y)
```
