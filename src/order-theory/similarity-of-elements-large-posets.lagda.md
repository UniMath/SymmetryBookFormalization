# Similarity of elements in large posets

```agda
module order-theory.similarity-of-elements-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.similarity-of-elements-large-preorders
```

</details>

## Idea

Two elements `x` and `y` of a [large poset](order-theory.large-posets.md) `P`
are said to be
{{#concept "similar" Disambiguation="elements of a large poset" Agda=sim-Large-Poset}}
if both `x ≤ y` and `y ≤ x` hold. Note that the similarity relation is defined
across universe levels, and that only similar elements of the same universe
level are equal.

In informal writing we will use the notation `x ≈ y` to assert that `x` and `y`
are similar elements in a poset `P`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  sim-prop-Large-Poset :
    {l1 l2 : Level}
    (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    Prop (β l1 l2 ⊔ β l2 l1)
  sim-prop-Large-Poset = sim-prop-Large-Preorder (large-preorder-Large-Poset P)

  sim-Large-Poset :
    {l1 l2 : Level}
    (x : type-Large-Poset P l1)
    (y : type-Large-Poset P l2) →
    UU (β l1 l2 ⊔ β l2 l1)
  sim-Large-Poset = sim-Large-Preorder (large-preorder-Large-Poset P)

  is-prop-sim-Large-Poset :
    {l1 l2 : Level}
    (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    is-prop (sim-Large-Poset x y)
  is-prop-sim-Large-Poset =
    is-prop-sim-Large-Preorder (large-preorder-Large-Poset P)
```

## Properties

### The similarity relation is reflexive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  refl-sim-Large-Poset :
    is-reflexive-Large-Relation (type-Large-Poset P) (sim-Large-Poset P)
  refl-sim-Large-Poset = refl-sim-Large-Preorder (large-preorder-Large-Poset P)
```

### The similarity relation is transitive

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  transitive-sim-Large-Poset :
    is-transitive-Large-Relation (type-Large-Poset P) (sim-Large-Poset P)
  transitive-sim-Large-Poset =
    transitive-sim-Large-Preorder (large-preorder-Large-Poset P)
```

### The similarity relation is symmetric

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  symmetric-sim-Large-Poset :
    is-symmetric-Large-Relation (type-Large-Poset P) (sim-Large-Poset P)
  symmetric-sim-Large-Poset =
    symmetric-sim-Large-Preorder (large-preorder-Large-Poset P)
```

### For any universe level `l`, any element `x` is similar to at most one element of universe level `l`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  all-elements-equal-total-sim-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) →
    all-elements-equal (Σ (type-Large-Poset P l2) (sim-Large-Poset P x))
  all-elements-equal-total-sim-Large-Poset x (y , H) (z , K) =
    eq-type-subtype
      ( sim-prop-Large-Poset P x)
      ( antisymmetric-leq-Large-Poset P
        ( y)
        ( z)
        ( transitive-leq-Large-Poset P _ _ _ (pr1 K) (pr2 H))
        ( transitive-leq-Large-Poset P _ _ _ (pr1 H) (pr2 K)))

  is-prop-total-sim-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) →
    is-prop (Σ (type-Large-Poset P l2) (sim-Large-Poset P x))
  is-prop-total-sim-Large-Poset x =
    is-prop-all-elements-equal
      ( all-elements-equal-total-sim-Large-Poset x)

  is-torsorial-sim-Large-Poset :
    {l1 : Level} (x : type-Large-Poset P l1) →
    is-torsorial (sim-Large-Poset P x)
  is-torsorial-sim-Large-Poset x =
    is-proof-irrelevant-is-prop
      ( is-prop-total-sim-Large-Poset x)
      ( x , refl-sim-Large-Poset P x)
```

### Similarity characterizes the identity type of elements in a large poset of the same universe level

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  where

  sim-eq-Large-Poset :
    {l1 : Level} {x y : type-Large-Poset P l1} →
    x ＝ y → sim-Large-Poset P x y
  sim-eq-Large-Poset refl = refl-sim-Large-Poset P _

  is-equiv-sim-eq-Large-Poset :
    {l1 : Level} (x y : type-Large-Poset P l1) →
    is-equiv (sim-eq-Large-Poset {l1} {x} {y})
  is-equiv-sim-eq-Large-Poset x =
    fundamental-theorem-id
      ( is-torsorial-sim-Large-Poset P x)
      ( λ y → sim-eq-Large-Poset {_} {x} {y})

  extensionality-Large-Poset :
    {l1 : Level} (x y : type-Large-Poset P l1) →
    (x ＝ y) ≃ sim-Large-Poset P x y
  pr1 (extensionality-Large-Poset x y) = sim-eq-Large-Poset
  pr2 (extensionality-Large-Poset x y) = is-equiv-sim-eq-Large-Poset x y

  eq-sim-Large-Poset :
    {l1 : Level} (x y : type-Large-Poset P l1) →
    sim-Large-Poset P x y → x ＝ y
  eq-sim-Large-Poset x y = map-inv-is-equiv (is-equiv-sim-eq-Large-Poset x y)
```
