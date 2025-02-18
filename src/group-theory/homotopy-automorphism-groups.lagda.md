# Homotopy automorphism groups

```agda
module group-theory.homotopy-automorphism-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.connected-components
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-groups

open import higher-group-theory.automorphism-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The concrete
{{#concept "homotopy automorphism group" Disambiguation="of a pointed type" Agda=concrete-group-Pointed-Type}}
of a [pointed type](structured-types.pointed-types.md) `A` is the
[automorphism group](group-theory.automorphism-groups.md) of the
[groupoidification](foundation.truncations.md) of `A` at its base point.

## Definitions

### Homotopy automorphism groups of pointed types

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  concrete-group-Pointed-Type : Concrete-Group l
  concrete-group-Pointed-Type =
    Automorphism-Group
      ( trunc one-𝕋 (type-Pointed-Type A))
      ( unit-trunc (point-Pointed-Type A))

  classifying-type-concrete-group-Pointed-Type : UU l
  classifying-type-concrete-group-Pointed-Type =
    classifying-type-Concrete-Group concrete-group-Pointed-Type

  shape-concrete-group-Pointed-Type :
    classifying-type-concrete-group-Pointed-Type
  shape-concrete-group-Pointed-Type =
    shape-Concrete-Group concrete-group-Pointed-Type

  ∞-group-concrete-group-Pointed-Type : ∞-Group l
  ∞-group-concrete-group-Pointed-Type =
    ∞-group-Concrete-Group concrete-group-Pointed-Type
```
