# Double negation dense subtypes of types

```agda
module logic.double-negation-dense-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements-subtypes
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import logic.double-negation-dense-maps
```

</details>

## Idea

A
{{#concept "double negationdense" Disambiguation="subtype" Agda=is-double-negation-dense-subtype Agda=double-negation-dense-subtype}}
[subtype](foundation.subtypes.md) of a type `X` is a subtype `P ⊆ X` such that
its double [complement](foundation.complements-subtypes.md) is
[full](foundation.full-subtypes.md).

## Definitions

### The predicate on a subtype of being double negation dense

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-double-negation-dense-subtype-Prop : Prop (l1 ⊔ l2)
  is-double-negation-dense-subtype-Prop =
    is-full-subtype-Prop (complement-subtype (complement-subtype P))

  is-double-negation-dense-subtype : UU (l1 ⊔ l2)
  is-double-negation-dense-subtype =
    type-Prop is-double-negation-dense-subtype-Prop

  is-prop-is-double-negation-dense-subtype :
    is-prop is-double-negation-dense-subtype
  is-prop-is-double-negation-dense-subtype =
    is-prop-type-Prop is-double-negation-dense-subtype-Prop
```

### The type of double negation dense subtypes

```agda
double-negation-dense-subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
double-negation-dense-subtype l2 A =
  Σ (subtype l2 A) is-double-negation-dense-subtype

module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-dense-subtype l2 A)
  where

  subtype-double-negation-dense-subtype : subtype l2 A
  subtype-double-negation-dense-subtype = pr1 P

  is-double-negation-dense-double-negation-dense-subtype :
    is-double-negation-dense-subtype subtype-double-negation-dense-subtype
  is-double-negation-dense-double-negation-dense-subtype = pr2 P

  type-double-negation-dense-subtype : UU (l1 ⊔ l2)
  type-double-negation-dense-subtype =
    type-subtype subtype-double-negation-dense-subtype

  is-in-double-negation-dense-subtype : A → UU l2
  is-in-double-negation-dense-subtype =
    is-in-subtype subtype-double-negation-dense-subtype

  is-prop-is-in-double-negation-dense-subtype :
    (x : A) → is-prop (is-in-double-negation-dense-subtype x)
  is-prop-is-in-double-negation-dense-subtype =
    is-prop-is-in-subtype subtype-double-negation-dense-subtype

  inclusion-double-negation-dense-subtype :
    type-double-negation-dense-subtype → A
  inclusion-double-negation-dense-subtype =
    inclusion-subtype subtype-double-negation-dense-subtype
```

## Properties

### A subtype is double negation dense if and only if the inclusion is double negation dense

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-double-negation-dense-inclusion-is-double-negation-dense-subtype :
    is-double-negation-dense-subtype P →
    is-double-negation-dense-map (inclusion-subtype P)
  is-double-negation-dense-inclusion-is-double-negation-dense-subtype H x =
    map-double-negation (λ y → ((x , y) , refl)) (H x)

  double-negation-dense-inclusion-is-double-negation-dense-subtype :
    is-double-negation-dense-subtype P → type-subtype P ↠¬¬ A
  double-negation-dense-inclusion-is-double-negation-dense-subtype H =
    ( inclusion-subtype P ,
      is-double-negation-dense-inclusion-is-double-negation-dense-subtype H)

  is-dense-is-double-negation-dense-inclusion-subtype :
    is-double-negation-dense-map (inclusion-subtype P) →
    is-double-negation-dense-subtype P
  is-dense-is-double-negation-dense-inclusion-subtype H x =
    map-double-negation (λ p → tr (is-in-subtype P) (pr2 p) (pr2 (pr1 p))) (H x)

module _
  {l1 l2 : Level} {A : UU l1} (P : double-negation-dense-subtype l2 A)
  where

  is-double-negation-dense-inclusion-double-negation-dense-subtype :
    is-double-negation-dense-map (inclusion-double-negation-dense-subtype P)
  is-double-negation-dense-inclusion-double-negation-dense-subtype =
    is-double-negation-dense-inclusion-is-double-negation-dense-subtype
      ( subtype-double-negation-dense-subtype P)
      ( is-double-negation-dense-double-negation-dense-subtype P)

  double-negation-dense-inclusion-double-negation-dense-subtype :
    type-double-negation-dense-subtype P ↠¬¬ A
  double-negation-dense-inclusion-double-negation-dense-subtype =
    double-negation-dense-inclusion-is-double-negation-dense-subtype
      ( subtype-double-negation-dense-subtype P)
      ( is-double-negation-dense-double-negation-dense-subtype P)
```
