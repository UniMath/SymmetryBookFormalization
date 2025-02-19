# The poset of right ideals of a semiring

```agda
module ring-theory.poset-of-right-ideals-semirings where
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

open import ring-theory.right-ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

The [right ideals](ring-theory.right-ideals-semirings.md) of a
[semiring](ring-theory.semirings.md) form a
[large poset](order-theory.large-posets.md) ordered by inclusion.

## Definition

### The inclusion relation on right ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-right-ideal-Semiring :
    {l2 l3 : Level} →
    right-ideal-Semiring l2 R → right-ideal-Semiring l3 R → Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-right-ideal-Semiring I J =
    leq-prop-subtype
      ( subset-right-ideal-Semiring R I)
      ( subset-right-ideal-Semiring R J)

  leq-right-ideal-Semiring :
    {l2 l3 : Level} →
    right-ideal-Semiring l2 R → right-ideal-Semiring l3 R → UU (l1 ⊔ l2 ⊔ l3)
  leq-right-ideal-Semiring I J =
    subset-right-ideal-Semiring R I ⊆ subset-right-ideal-Semiring R J

  is-prop-leq-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R) →
    is-prop (leq-right-ideal-Semiring I J)
  is-prop-leq-right-ideal-Semiring I J =
    is-prop-leq-subtype
      ( subset-right-ideal-Semiring R I)
      ( subset-right-ideal-Semiring R J)

  refl-leq-right-ideal-Semiring :
    {l2 : Level} → is-reflexive (leq-right-ideal-Semiring {l2})
  refl-leq-right-ideal-Semiring I =
    refl-leq-subtype (subset-right-ideal-Semiring R I)

  transitive-leq-right-ideal-Semiring :
    {l2 l3 l4 : Level}
    (I : right-ideal-Semiring l2 R)
    (J : right-ideal-Semiring l3 R)
    (K : right-ideal-Semiring l4 R) →
    leq-right-ideal-Semiring J K →
    leq-right-ideal-Semiring I J →
    leq-right-ideal-Semiring I K
  transitive-leq-right-ideal-Semiring I J K =
    transitive-leq-subtype
      ( subset-right-ideal-Semiring R I)
      ( subset-right-ideal-Semiring R J)
      ( subset-right-ideal-Semiring R K)

  antisymmetric-leq-right-ideal-Semiring :
    {l2 : Level} → is-antisymmetric (leq-right-ideal-Semiring {l2})
  antisymmetric-leq-right-ideal-Semiring I J U V =
    eq-has-same-elements-right-ideal-Semiring R I J (λ x → U x , V x)
```

### The large poset of right ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  right-ideal-Semiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder right-ideal-Semiring-Large-Preorder l =
    right-ideal-Semiring l R
  leq-prop-Large-Preorder right-ideal-Semiring-Large-Preorder =
    leq-prop-right-ideal-Semiring R
  refl-leq-Large-Preorder right-ideal-Semiring-Large-Preorder =
    refl-leq-right-ideal-Semiring R
  transitive-leq-Large-Preorder right-ideal-Semiring-Large-Preorder =
    transitive-leq-right-ideal-Semiring R

  right-ideal-Semiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset right-ideal-Semiring-Large-Poset =
    right-ideal-Semiring-Large-Preorder
  antisymmetric-leq-Large-Poset right-ideal-Semiring-Large-Poset =
    antisymmetric-leq-right-ideal-Semiring R
```

### The similarity relation on right ideals in a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-right-ideal-Semiring =
    sim-prop-Large-Poset (right-ideal-Semiring-Large-Poset R)

  sim-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-right-ideal-Semiring =
    sim-Large-Poset (right-ideal-Semiring-Large-Poset R)

  is-prop-sim-right-ideal-Semiring :
    {l2 l3 : Level}
    (I : right-ideal-Semiring l2 R) (J : right-ideal-Semiring l3 R) →
    is-prop (sim-right-ideal-Semiring I J)
  is-prop-sim-right-ideal-Semiring =
    is-prop-sim-Large-Poset (right-ideal-Semiring-Large-Poset R)

  eq-sim-right-ideal-Semiring :
    {l2 : Level}
    (I J : right-ideal-Semiring l2 R) → sim-right-ideal-Semiring I J → I ＝ J
  eq-sim-right-ideal-Semiring =
    eq-sim-Large-Poset (right-ideal-Semiring-Large-Poset R)
```

## Properties

### The forgetful function from right ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-right-ideal-Semiring :
    {l1 l2 : Level}
    (I : right-ideal-Semiring l1 R) (J : right-ideal-Semiring l2 R) →
    leq-right-ideal-Semiring R I J →
    subset-right-ideal-Semiring R I ⊆ subset-right-ideal-Semiring R J
  preserves-order-subset-right-ideal-Semiring I J H = H

  subset-right-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( right-ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder subset-right-ideal-hom-large-poset-Semiring =
    subset-right-ideal-Semiring R
  preserves-order-hom-Large-Preorder
    subset-right-ideal-hom-large-poset-Semiring =
    preserves-order-subset-right-ideal-Semiring
```
