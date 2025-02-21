# Posets

```agda
module order-theory.posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **poset** is a [set](foundation-core.sets.md)
[equipped](foundation.structure.md) with a reflexive, antisymmetric, transitive
[relation](foundation.binary-relations.md) that takes values in
[propositions](foundation-core.propositions.md).

## Definitions

```agda
is-antisymmetric-leq-Preorder :
  {l1 l2 : Level} (P : Preorder l1 l2) → UU (l1 ⊔ l2)
is-antisymmetric-leq-Preorder P = is-antisymmetric (leq-Preorder P)

Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Poset l1 l2 =
  Σ (Preorder l1 l2) (is-antisymmetric-leq-Preorder)

module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  preorder-Poset : Preorder l1 l2
  preorder-Poset = pr1 X

  type-Poset : UU l1
  type-Poset = type-Preorder preorder-Poset

  leq-prop-Poset : (x y : type-Poset) → Prop l2
  leq-prop-Poset = leq-prop-Preorder preorder-Poset

  leq-Poset : (x y : type-Poset) → UU l2
  leq-Poset = leq-Preorder preorder-Poset

  is-prop-leq-Poset : (x y : type-Poset) → is-prop (leq-Poset x y)
  is-prop-leq-Poset = is-prop-leq-Preorder preorder-Poset

  concatenate-eq-leq-Poset' :
    {x y z : type-Poset} → x ＝ y → leq-Poset x z → leq-Poset y z
  concatenate-eq-leq-Poset' = concatenate-eq-leq-Preorder' preorder-Poset

  concatenate-eq-leq-Poset :
    {x y z : type-Poset} → x ＝ y → leq-Poset y z → leq-Poset x z
  concatenate-eq-leq-Poset = concatenate-eq-leq-Preorder preorder-Poset

  concatenate-leq-eq-Poset :
    {x y z : type-Poset} → leq-Poset x y → y ＝ z → leq-Poset x z
  concatenate-leq-eq-Poset = concatenate-leq-eq-Preorder preorder-Poset

  concatenate-eq-leq-eq-Poset :
    {x y z w : type-Poset} → x ＝ y → leq-Poset y z → z ＝ w → leq-Poset x w
  concatenate-eq-leq-eq-Poset = concatenate-eq-leq-eq-Preorder preorder-Poset

  concatenate-eq-leq-eq-Poset' :
    {x y z w : type-Poset} → x ＝ y → leq-Poset x z → z ＝ w → leq-Poset y w
  concatenate-eq-leq-eq-Poset' = concatenate-eq-leq-eq-Preorder' preorder-Poset

  refl-leq-Poset : is-reflexive leq-Poset
  refl-leq-Poset = refl-leq-Preorder preorder-Poset

  transitive-leq-Poset : is-transitive leq-Poset
  transitive-leq-Poset = transitive-leq-Preorder preorder-Poset

  le-prop-Poset : (x y : type-Poset) → Prop (l1 ⊔ l2)
  le-prop-Poset = le-prop-Preorder preorder-Poset

  le-Poset : (x y : type-Poset) → UU (l1 ⊔ l2)
  le-Poset = le-Preorder preorder-Poset

  is-prop-le-Poset :
    (x y : type-Poset) → is-prop (le-Poset x y)
  is-prop-le-Poset = is-prop-le-Preorder preorder-Poset

  antisymmetric-leq-Poset : is-antisymmetric leq-Poset
  antisymmetric-leq-Poset = pr2 X
```

## Reasoning with inequalities in posets

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Poset X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Poset X
    ≤ z
      by ineq-2
      in-Poset X
    ≤ v
      by ineq-3
      in-Poset X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Poset_chain-of-inequalities_
infixl 0 step-calculate-in-Poset

calculate-in-Poset_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Poset l1 l2)
  (x : type-Poset X) → leq-Poset X x x
calculate-in-Poset_chain-of-inequalities_ = refl-leq-Poset

step-calculate-in-Poset :
  {l1 l2 : Level} (X : Poset l1 l2)
  {x y : type-Poset X} → leq-Poset X x y →
  (z : type-Poset X) → leq-Poset X y z → leq-Poset X x z
step-calculate-in-Poset X {x} {y} u z v = transitive-leq-Poset X x y z v u

syntax step-calculate-in-Poset X u z v = u ≤ z by v in-Poset X
```

## Properties

### The underlying type of a poset is a set

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-set-type-Poset : is-set (type-Poset X)
  is-set-type-Poset =
    is-set-prop-in-id
      ( λ x y → leq-Poset X x y × leq-Poset X y x)
      ( λ x y →
        is-prop-product (is-prop-leq-Poset X x y) (is-prop-leq-Poset X y x))
      ( λ x → refl-leq-Poset X x , refl-leq-Poset X x)
      ( λ x y (H , K) → antisymmetric-leq-Poset X x y H K)

  set-Poset : Set l1
  set-Poset = (type-Poset X , is-set-type-Poset)
```

We characterize equality in a poset as _similarity of elements_ in
[`order-theory.similarity-of-elements-posets`](order-theory.similarity-of-elements-posets.md).

### Posets are categories whose underlying hom-sets are propositions

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  precategory-Poset : Precategory l1 l2
  precategory-Poset = precategory-Preorder (preorder-Poset X)

  is-category-precategory-Poset : is-category-Precategory precategory-Poset
  is-category-precategory-Poset x y =
    is-equiv-has-converse-is-prop
      ( is-set-type-Poset X x y)
      ( is-prop-iso-is-prop-hom-Precategory precategory-Poset
        ( is-prop-leq-Poset X x y))
      ( λ f →
        antisymmetric-leq-Poset X x y
          ( hom-iso-Precategory precategory-Poset f)
          ( hom-inv-iso-Precategory precategory-Poset f))

  category-Poset : Category l1 l2
  pr1 category-Poset = precategory-Poset
  pr2 category-Poset = is-category-precategory-Poset

module _
  {l1 l2 : Level} (C : Category l1 l2)
  (is-prop-hom-C : (x y : obj-Category C) → is-prop (hom-Category C x y))
  where

  preorder-is-prop-hom-Category : Preorder l1 l2
  preorder-is-prop-hom-Category =
    preorder-is-prop-hom-Precategory (precategory-Category C) (is-prop-hom-C)

  poset-is-prop-hom-Category : Poset l1 l2
  pr1 poset-is-prop-hom-Category = preorder-is-prop-hom-Category
  pr2 poset-is-prop-hom-Category x y f g =
    map-inv-is-equiv
      ( is-category-Category C x y)
      ( iso-is-prop-hom-Precategory
        ( precategory-Category C) is-prop-hom-C f g)
```

It remains to show that these constructions form inverses to eachother.
