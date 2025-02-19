# The poset of left ideals of a semiring

```agda
module ring-theory.poset-of-left-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.similarity-of-elements-large-posets

open import ring-theory.left-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

The [left ideals](ring-theory.left-ideals-semirings.md) of a
[semiring](ring-theory.semirings.md) form a
[large poset](order-theory.large-posets.md) ordered by inclusion.

## Definition

### The inclusion relation on left ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-left-ideal-Semiring :
    {l2 l3 : Level} →
    left-ideal-Semiring l2 R → left-ideal-Semiring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-left-ideal-Semiring I J =
    leq-prop-subtype
      ( subset-left-ideal-Semiring R I)
      ( subset-left-ideal-Semiring R J)

  leq-left-ideal-Semiring :
    {l2 l3 : Level} →
    left-ideal-Semiring l2 R → left-ideal-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-left-ideal-Semiring I J =
    subset-left-ideal-Semiring R I ⊆ subset-left-ideal-Semiring R J

  is-prop-leq-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R) →
    is-prop (leq-left-ideal-Semiring I J)
  is-prop-leq-left-ideal-Semiring I J =
    is-prop-leq-subtype
      ( subset-left-ideal-Semiring R I)
      ( subset-left-ideal-Semiring R J)

  refl-leq-left-ideal-Semiring :
    {l2 : Level} → is-reflexive (leq-left-ideal-Semiring {l2})
  refl-leq-left-ideal-Semiring I =
    refl-leq-subtype (subset-left-ideal-Semiring R I)

  transitive-leq-left-ideal-Semiring :
    {l2 l3 l4 : Level}
    (I : left-ideal-Semiring l2 R)
    (J : left-ideal-Semiring l3 R)
    (K : left-ideal-Semiring l4 R) →
    leq-left-ideal-Semiring J K →
    leq-left-ideal-Semiring I J →
    leq-left-ideal-Semiring I K
  transitive-leq-left-ideal-Semiring I J K =
    transitive-leq-subtype
      ( subset-left-ideal-Semiring R I)
      ( subset-left-ideal-Semiring R J)
      ( subset-left-ideal-Semiring R K)

  antisymmetric-leq-left-ideal-Semiring :
    {l2 : Level} → is-antisymmetric (leq-left-ideal-Semiring {l2})
  antisymmetric-leq-left-ideal-Semiring I J U V =
    eq-has-same-elements-left-ideal-Semiring R I J (λ x → U x , V x)
```

### The large poset of left ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  left-ideal-Semiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder left-ideal-Semiring-Large-Preorder l =
    left-ideal-Semiring l R
  leq-prop-Large-Preorder left-ideal-Semiring-Large-Preorder =
    leq-prop-left-ideal-Semiring R
  refl-leq-Large-Preorder left-ideal-Semiring-Large-Preorder =
    refl-leq-left-ideal-Semiring R
  transitive-leq-Large-Preorder left-ideal-Semiring-Large-Preorder =
    transitive-leq-left-ideal-Semiring R

  left-ideal-Semiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset left-ideal-Semiring-Large-Poset =
    left-ideal-Semiring-Large-Preorder
  antisymmetric-leq-Large-Poset left-ideal-Semiring-Large-Poset =
    antisymmetric-leq-left-ideal-Semiring R
```

### The similarity relation on left ideals in a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-left-ideal-Semiring =
    sim-prop-Large-Poset (left-ideal-Semiring-Large-Poset R)

  sim-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-left-ideal-Semiring = sim-Large-Poset (left-ideal-Semiring-Large-Poset R)

  is-prop-sim-left-ideal-Semiring :
    {l2 l3 : Level}
    (I : left-ideal-Semiring l2 R) (J : left-ideal-Semiring l3 R) →
    is-prop (sim-left-ideal-Semiring I J)
  is-prop-sim-left-ideal-Semiring =
    is-prop-sim-Large-Poset (left-ideal-Semiring-Large-Poset R)

  eq-sim-left-ideal-Semiring :
    {l2 : Level}
    (I J : left-ideal-Semiring l2 R) → sim-left-ideal-Semiring I J → I ＝ J
  eq-sim-left-ideal-Semiring =
    eq-sim-Large-Poset (left-ideal-Semiring-Large-Poset R)
```

## Properties

### The forgetful function from left ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-left-ideal-Semiring :
    {l1 l2 : Level}
    (I : left-ideal-Semiring l1 R) (J : left-ideal-Semiring l2 R) →
    leq-left-ideal-Semiring R I J →
    subset-left-ideal-Semiring R I ⊆ subset-left-ideal-Semiring R J
  preserves-order-subset-left-ideal-Semiring I J H = H

  subset-left-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( left-ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder subset-left-ideal-hom-large-poset-Semiring =
    subset-left-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subset-left-ideal-hom-large-poset-Semiring =
    preserves-order-subset-left-ideal-Semiring
```
