# The poset of ideals of a semiring

```agda
module ring-theory.poset-of-ideals-semirings where
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

open import ring-theory.ideals-semirings
open import ring-theory.semirings
```

</details>

## Idea

The [ideals](ring-theory.ideals-semirings.md) of a [semiring](ring-theory.semirings.md) form
a [large poset](order-theory.large-posets.md) ordered by inclusion.

## Definition

### The inclusion relation on ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  leq-prop-ideal-Semiring :
    {l2 l3 : Level} → ideal-Semiring l2 R → ideal-Semiring l3 R →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-prop-ideal-Semiring I J =
    leq-prop-subtype
      ( subset-ideal-Semiring R I)
      ( subset-ideal-Semiring R J)

  leq-ideal-Semiring :
    {l2 l3 : Level} → ideal-Semiring l2 R → ideal-Semiring l3 R →
    UU (l1 ⊔ l2 ⊔ l3)
  leq-ideal-Semiring I J =
    subset-ideal-Semiring R I ⊆ subset-ideal-Semiring R J

  is-prop-leq-ideal-Semiring :
    {l2 l3 : Level} (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R) →
    is-prop (leq-ideal-Semiring I J)
  is-prop-leq-ideal-Semiring I J =
    is-prop-leq-subtype (subset-ideal-Semiring R I) (subset-ideal-Semiring R J)

  refl-leq-ideal-Semiring :
    {l2 : Level} → is-reflexive (leq-ideal-Semiring {l2})
  refl-leq-ideal-Semiring I =
    refl-leq-subtype (subset-ideal-Semiring R I)

  transitive-leq-ideal-Semiring :
    {l2 l3 l4 : Level}
    (I : ideal-Semiring l2 R)
    (J : ideal-Semiring l3 R)
    (K : ideal-Semiring l4 R) →
    leq-ideal-Semiring J K →
    leq-ideal-Semiring I J →
    leq-ideal-Semiring I K
  transitive-leq-ideal-Semiring I J K =
    transitive-leq-subtype
      ( subset-ideal-Semiring R I)
      ( subset-ideal-Semiring R J)
      ( subset-ideal-Semiring R K)

  antisymmetric-leq-ideal-Semiring :
    {l2 : Level} → is-antisymmetric (leq-ideal-Semiring {l2})
  antisymmetric-leq-ideal-Semiring I J U V =
    eq-has-same-elements-ideal-Semiring R I J (λ x → U x , V x)
```

### The large poset of ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  ideal-Semiring-Large-Preorder :
    Large-Preorder (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  type-Large-Preorder ideal-Semiring-Large-Preorder l =
    ideal-Semiring l R
  leq-prop-Large-Preorder ideal-Semiring-Large-Preorder =
    leq-prop-ideal-Semiring R
  refl-leq-Large-Preorder ideal-Semiring-Large-Preorder =
    refl-leq-ideal-Semiring R
  transitive-leq-Large-Preorder ideal-Semiring-Large-Preorder =
    transitive-leq-ideal-Semiring R

  ideal-Semiring-Large-Poset :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  large-preorder-Large-Poset ideal-Semiring-Large-Poset =
    ideal-Semiring-Large-Preorder
  antisymmetric-leq-Large-Poset ideal-Semiring-Large-Poset =
    antisymmetric-leq-ideal-Semiring R
```

### The similarity relation on ideals in a semiring

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  sim-prop-ideal-Semiring :
    {l2 l3 : Level} (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R) →
    Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-ideal-Semiring =
    sim-prop-Large-Poset (ideal-Semiring-Large-Poset R)

  sim-ideal-Semiring :
    {l2 l3 : Level} (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R) →
    UU (l1 ⊔ l2 ⊔ l3)
  sim-ideal-Semiring = sim-Large-Poset (ideal-Semiring-Large-Poset R)

  is-prop-sim-ideal-Semiring :
    {l2 l3 : Level} (I : ideal-Semiring l2 R) (J : ideal-Semiring l3 R) →
    is-prop (sim-ideal-Semiring I J)
  is-prop-sim-ideal-Semiring =
    is-prop-sim-Large-Poset (ideal-Semiring-Large-Poset R)

  eq-sim-ideal-Semiring :
    {l2 : Level} (I J : ideal-Semiring l2 R) → sim-ideal-Semiring I J → I ＝ J
  eq-sim-ideal-Semiring = eq-sim-Large-Poset (ideal-Semiring-Large-Poset R)
```

## Properties

### The forgetful function from ideals to subsets preserves inclusions

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-order-subset-ideal-Semiring :
    {l1 l2 : Level} (I : ideal-Semiring l1 R) (J : ideal-Semiring l2 R) →
    leq-ideal-Semiring R I J →
    subset-ideal-Semiring R I ⊆ subset-ideal-Semiring R J
  preserves-order-subset-ideal-Semiring I J H = H

  subset-ideal-hom-large-poset-Semiring :
    hom-Large-Poset
      ( λ l → l)
      ( ideal-Semiring-Large-Poset R)
      ( powerset-Large-Poset (type-Semiring R))
  map-hom-Large-Preorder subset-ideal-hom-large-poset-Semiring =
    subset-ideal-Semiring R
  preserves-order-hom-Large-Preorder subset-ideal-hom-large-poset-Semiring =
    preserves-order-subset-ideal-Semiring
```
