---
title: Homomorphisms of groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.homomorphisms-groups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.identity-types using (Id; inv; _∙_; ap)
open import foundation.sets using (is-set; UU-Set)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.groups using
  ( Group; type-Group; semigroup-Group; unit-Group; left-unit-law-Group;
    mul-Group; left-inverse-law-Group; associative-mul-Group; inv-Group;
    right-unit-law-Group; right-inverse-law-Group)
open import group-theory.homomorphisms-semigroups using
  ( preserves-mul-Semigroup; type-hom-Semigroup; htpy-hom-Semigroup;
    refl-htpy-hom-Semigroup; htpy-eq-hom-Semigroup;
    is-contr-total-htpy-hom-Semigroup; is-equiv-htpy-eq-hom-Semigroup;
    eq-htpy-hom-Semigroup; is-set-type-hom-Semigroup; id-hom-Semigroup;
    comp-hom-Semigroup; associative-comp-hom-Semigroup;
    left-unit-law-comp-hom-Semigroup; right-unit-law-comp-hom-Semigroup)
```

## Idea

A group homomorphism from one group to another is a semigroup homomorphism between their underlying semigroups

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group f =
    preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H) f

  type-hom-Group : UU (l1 ⊔ l2)
  type-hom-Group =
    type-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  map-hom-Group : type-hom-Group → type-Group G → type-Group H
  map-hom-Group = pr1

  preserves-mul-hom-Group :
    (f : type-hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = pr2
```

### The identity group homomorphism

```agda
id-hom-Group : {l : Level} (G : Group l) → type-hom-Group G G
id-hom-Group G = id-hom-Semigroup (semigroup-Group G)
```

### Composition of group homomorphisms

```agda
comp-hom-Group :
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3) →
  type-hom-Group H K → type-hom-Group G H → type-hom-Group G K
comp-hom-Group G H K =
  comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)
```

## Properties

### Characterization of the identity type of group homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  htpy-hom-Group : (f g : type-hom-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Group = htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  refl-htpy-hom-Group : (f : type-hom-Group G H) → htpy-hom-Group f f
  refl-htpy-hom-Group =
    refl-htpy-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  htpy-eq-hom-Group : (f g : type-hom-Group G H) → Id f g → htpy-hom-Group f g
  htpy-eq-hom-Group =
    htpy-eq-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  abstract
    is-contr-total-htpy-hom-Group :
      ( f : type-hom-Group G H) →
      is-contr (Σ (type-hom-Group G H) (htpy-hom-Group f))
    is-contr-total-htpy-hom-Group =
      is-contr-total-htpy-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : type-hom-Group G H) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group =
      is-equiv-htpy-eq-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  extensionality-hom-Group :
    (f g : type-hom-Group G H) → Id f g ≃ htpy-hom-Group f g
  pr1 (extensionality-hom-Group f g) = htpy-eq-hom-Group f g
  pr2 (extensionality-hom-Group f g) = is-equiv-htpy-eq-hom-Group f g

  eq-htpy-hom-Group : {f g : type-hom-Group G H} → htpy-hom-Group f g → Id f g
  eq-htpy-hom-Group =
    eq-htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-set-type-hom-Group : is-set (type-hom-Group G H)
  is-set-type-hom-Group =
    is-set-type-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-Group : UU-Set (l1 ⊔ l2)
  pr1 hom-Group = type-hom-Group G H
  pr2 hom-Group = is-set-type-hom-Group
```

### Associativity of composition of group homomorphisms

```agda
associative-comp-hom-Group :
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  (h : type-hom-Group K L) (g : type-hom-Group H K) (f : type-hom-Group G H) →
  Id ( comp-hom-Group G H L (comp-hom-Group H K L h g) f)
     ( comp-hom-Group G K L h (comp-hom-Group G H K g f))
associative-comp-hom-Group G H K L =
  associative-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
    ( semigroup-Group K)
    ( semigroup-Group L)
```

### The left and right unit laws for composition of group homomorphisms

```agda
left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G H H (id-hom-Group H) f) f
left-unit-law-comp-hom-Group G H =
  left-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : type-hom-Group G H) →
  Id (comp-hom-Group G G H f (id-hom-Group G)) f
right-unit-law-comp-hom-Group G H =
  right-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
```

### Group homomorphisms preserve the unit element

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where
  
  preserves-unit-Group : (type-Group G → type-Group H) → UU l2
  preserves-unit-Group f = Id (f (unit-Group G)) (unit-Group H)

  abstract
    preserves-unit-hom-Group :
      ( f : type-hom-Group G H) → preserves-unit-Group (map-hom-Group G H f)
    preserves-unit-hom-Group f =
      ( inv (left-unit-law-Group H (map-hom-Group G H f (unit-Group G)))) ∙
      ( ( ap ( λ x → mul-Group H x (map-hom-Group G H f (unit-Group G)))
             ( inv
               ( left-inverse-law-Group H
                 ( map-hom-Group G H f (unit-Group G))))) ∙
        ( ( associative-mul-Group H
            ( inv-Group H (map-hom-Group G H f (unit-Group G)))
            ( map-hom-Group G H f (unit-Group G))
            ( map-hom-Group G H f (unit-Group G))) ∙
          ( ( ap
              ( mul-Group H (inv-Group H (map-hom-Group G H f (unit-Group G))))
              ( inv
                ( preserves-mul-hom-Group G H f
                  ( unit-Group G)
                  ( unit-Group G)))) ∙
            ( ( ap
                ( λ x →
                  mul-Group H
                    ( inv-Group H (map-hom-Group G H f (unit-Group G)))
                    ( map-hom-Group G H f x))
                ( left-unit-law-Group G (unit-Group G))) ∙
              ( left-inverse-law-Group H
                ( map-hom-Group G H f (unit-Group G)))))))
```

### Group homomorphisms preserve inverses

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-inverses-Group :
    (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-inverses-Group f =
    (x : type-Group G) → Id (f (inv-Group G x)) (inv-Group H (f x))

  abstract
    preserves-inverses-hom-Group :
      (f : type-hom-Group G H) → preserves-inverses-Group (map-hom-Group G H f)
    preserves-inverses-hom-Group f x =
      ( inv ( right-unit-law-Group H (map-hom-Group G H f (inv-Group G x)))) ∙
      ( ( ap
          ( mul-Group H (map-hom-Group G H f (inv-Group G x)))
          ( inv (right-inverse-law-Group H (map-hom-Group G H f x)))) ∙
        ( ( inv
            ( associative-mul-Group H
              ( map-hom-Group G H f (inv-Group G x))
              ( map-hom-Group G H f x)
              ( inv-Group H (map-hom-Group G H f x)))) ∙
          ( ( inv
              ( ap
                ( λ y → mul-Group H y (inv-Group H (map-hom-Group G H f x)))
                ( preserves-mul-hom-Group G H f (inv-Group G x) x))) ∙
            ( ( ap
                ( λ y →
                  mul-Group H
                    ( map-hom-Group G H f y)
                    ( inv-Group H (map-hom-Group G H f x)))
                ( left-inverse-law-Group G x)) ∙
              ( ( ap
                  ( λ y → mul-Group H y (inv-Group H (map-hom-Group G H f x)))
                  ( preserves-unit-hom-Group G H f)) ∙
                ( left-unit-law-Group H
                  ( inv-Group H (map-hom-Group G H f x))))))))
```

### Group homomorphisms preserve all group structure

```agda
hom-Group' :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) → UU (l1 ⊔ l2)
hom-Group' G H =
  Σ ( type-hom-Group G H)
    ( λ f →
      ( preserves-unit-Group G H (map-hom-Group G H f)) ×
      ( preserves-inverses-Group G H (map-hom-Group G H f)))

preserves-group-structure-hom-Group :
  { l1 l2 : Level} (G : Group l1) (H : Group l2) →
  type-hom-Group G H → hom-Group' G H
pr1 (preserves-group-structure-hom-Group G H f) = f
pr1 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-unit-hom-Group G H f
pr2 (pr2 (preserves-group-structure-hom-Group G H f)) =
  preserves-inverses-hom-Group G H f
```
