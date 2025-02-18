# Automorphism groups

```agda
module group-theory.automorphism-groups where
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
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-groups

open import higher-group-theory.automorphism-groups
open import higher-group-theory.higher-groups
```

</details>

## Idea

The concrete
{{#concept "automorphism group" Disambiguation="of a 1-type at a point" WD="automorphism group" WDID=Q60790315 Agda=Automorphism-Group}}
of an element `a` of a [1-type](foundation.1-types.md) `A` is the
[connected component](foundation.connected-components.md) of `a`.

## Definitions

### Automorphism groups of objects in a 1-type

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  classifying-type-Automorphism-Group : UU l
  classifying-type-Automorphism-Group =
    classifying-type-Automorphism-∞-Group a

  shape-Automorphism-Group : classifying-type-Automorphism-Group
  shape-Automorphism-Group = shape-Automorphism-∞-Group a

  Automorphism-Group : Concrete-Group l
  pr1 Automorphism-Group = Automorphism-∞-Group a
  pr2 Automorphism-Group =
    is-trunc-connected-component
      ( type-1-Type A)
      ( a)
      ( is-1-type-type-1-Type A)
      ( a , refl-mere-eq a)
      ( a , refl-mere-eq a)

  ∞-group-Automorphism-Group : ∞-Group l
  ∞-group-Automorphism-Group = ∞-group-Concrete-Group Automorphism-Group
```

## Properties

### Characerizing the identity type of `Automorphism-Group`

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) → UU l
  Eq-classifying-type-Automorphism-Group =
    Eq-classifying-type-Automorphism-∞-Group a

  refl-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X X
  refl-Eq-classifying-type-Automorphism-Group =
    refl-Eq-classifying-type-Automorphism-∞-Group a

  is-torsorial-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    is-torsorial (Eq-classifying-type-Automorphism-Group X)
  is-torsorial-Eq-classifying-type-Automorphism-Group =
    is-torsorial-Eq-classifying-type-Automorphism-∞-Group a

  Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) → Eq-classifying-type-Automorphism-Group X Y
  Eq-eq-classifying-type-Automorphism-Group X .X refl =
    refl-Eq-classifying-type-Automorphism-Group X

  is-equiv-Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    is-equiv (Eq-eq-classifying-type-Automorphism-Group X Y)
  is-equiv-Eq-eq-classifying-type-Automorphism-Group X =
    fundamental-theorem-id
      ( is-torsorial-Eq-classifying-type-Automorphism-Group X)
      ( Eq-eq-classifying-type-Automorphism-Group X)

  extensionality-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) ≃ Eq-classifying-type-Automorphism-Group X Y
  pr1 (extensionality-classifying-type-Automorphism-Group X Y) =
    Eq-eq-classifying-type-Automorphism-Group X Y
  pr2 (extensionality-classifying-type-Automorphism-Group X Y) =
    is-equiv-Eq-eq-classifying-type-Automorphism-Group X Y

  eq-Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X Y → X ＝ Y
  eq-Eq-classifying-type-Automorphism-Group X Y =
    map-inv-equiv (extensionality-classifying-type-Automorphism-Group X Y)
```

### Equal elements in a 1-type have isomorphic automorphism groups

```agda
module _
  {l : Level} (A : 1-Type l)
  where

  equiv-eq-Automorphism-Group :
    {x y : type-1-Type A} (p : x ＝ y) →
    equiv-Concrete-Group (Automorphism-Group A x) (Automorphism-Group A y)
  equiv-eq-Automorphism-Group refl =
    id-equiv-Concrete-Group (Automorphism-Group A _)
```

## See also

- [Automorphism $∞$-groups](higher-group-theory.automorphism-groups.md)
