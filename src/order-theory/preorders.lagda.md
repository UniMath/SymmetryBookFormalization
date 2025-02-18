# Preorders

```agda
module order-theory.preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A **preorder** is a type equipped with a reflexive, transitive relation that is
valued in propositions.

## Definitions

### The predicate on a propositional relation of being a preorder

```agda
is-preorder-Relation-Prop :
  {l1 l2 : Level} {X : UU l1} → Relation-Prop l2 X → UU (l1 ⊔ l2)
is-preorder-Relation-Prop R =
  is-reflexive-Relation-Prop R × is-transitive-Relation-Prop R
```

### The type of preorders

```agda
Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Preorder l1 l2 =
  Σ (UU l1) (λ X → Σ (Relation-Prop l2 X) (is-preorder-Relation-Prop))

module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  type-Preorder : UU l1
  type-Preorder = pr1 X

  leq-prop-Preorder : Relation-Prop l2 type-Preorder
  leq-prop-Preorder = pr1 (pr2 X)

  leq-Preorder : (x y : type-Preorder) → UU l2
  leq-Preorder x y = type-Prop (leq-prop-Preorder x y)

  is-prop-leq-Preorder : (x y : type-Preorder) → is-prop (leq-Preorder x y)
  is-prop-leq-Preorder = is-prop-type-Relation-Prop leq-prop-Preorder

  concatenate-eq-leq-Preorder' :
    {x y z : type-Preorder} → x ＝ y → leq-Preorder x z → leq-Preorder y z
  concatenate-eq-leq-Preorder' {z = z} = tr (λ p → leq-Preorder p z)

  concatenate-eq-leq-Preorder :
    {x y z : type-Preorder} → x ＝ y → leq-Preorder y z → leq-Preorder x z
  concatenate-eq-leq-Preorder p = concatenate-eq-leq-Preorder' (inv p)

  concatenate-leq-eq-Preorder :
    {x y z : type-Preorder} → leq-Preorder x y → y ＝ z → leq-Preorder x z
  concatenate-leq-eq-Preorder {x} H p = tr (leq-Preorder x) p H

  concatenate-eq-leq-eq-Preorder' :
    {x y z w : type-Preorder} →
    x ＝ y → leq-Preorder x z → z ＝ w → leq-Preorder y w
  concatenate-eq-leq-eq-Preorder' p H q =
    concatenate-eq-leq-Preorder' p (concatenate-leq-eq-Preorder H q)

  concatenate-eq-leq-eq-Preorder :
    {x y z w : type-Preorder} →
    x ＝ y → leq-Preorder y z → z ＝ w → leq-Preorder x w
  concatenate-eq-leq-eq-Preorder p H q =
    concatenate-eq-leq-Preorder p (concatenate-leq-eq-Preorder H q)

  le-prop-Preorder : Relation-Prop (l1 ⊔ l2) type-Preorder
  le-prop-Preorder x y =
    product-Prop (x ≠ y , is-prop-neg) (leq-prop-Preorder x y)

  le-Preorder : Relation (l1 ⊔ l2) type-Preorder
  le-Preorder x y = type-Prop (le-prop-Preorder x y)

  is-prop-le-Preorder : (x y : type-Preorder) → is-prop (le-Preorder x y)
  is-prop-le-Preorder = is-prop-type-Relation-Prop le-prop-Preorder

  refl-leq-Preorder : is-reflexive leq-Preorder
  refl-leq-Preorder = pr1 (pr2 (pr2 X))

  transitive-leq-Preorder : is-transitive leq-Preorder
  transitive-leq-Preorder = pr2 (pr2 (pr2 X))
```

## Reasoning with inequalities in preorders

Inequalities in preorders can be constructed by equational reasoning as follows:

```text
calculate-in-Preorder X
  chain-of-inequalities
  x ≤ y
      by ineq-1
      in-Preorder X
    ≤ z
      by ineq-2
      in-Preorder X
    ≤ v
      by ineq-3
      in-Preorder X
```

Note, however, that in our setup of equational reasoning with inequalities it is
not possible to mix inequalities with equalities or strict inequalities.

```agda
infixl 1 calculate-in-Preorder_chain-of-inequalities_
infixl 0 step-calculate-in-Preorder

calculate-in-Preorder_chain-of-inequalities_ :
  {l1 l2 : Level} (X : Preorder l1 l2)
  (x : type-Preorder X) → leq-Preorder X x x
calculate-in-Preorder_chain-of-inequalities_ = refl-leq-Preorder

step-calculate-in-Preorder :
  {l1 l2 : Level} (X : Preorder l1 l2)
  {x y : type-Preorder X} → leq-Preorder X x y →
  (z : type-Preorder X) → leq-Preorder X y z → leq-Preorder X x z
step-calculate-in-Preorder X {x} {y} u z v =
  transitive-leq-Preorder X x y z v u

syntax step-calculate-in-Preorder X u z v = u ≤ z by v in-Preorder X
```

## Properties

### Preorders are precategories whose hom-sets are propositions

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  precategory-Preorder : Precategory l1 l2
  precategory-Preorder =
    make-Precategory
      ( type-Preorder X)
      ( λ x y → set-Prop (leq-prop-Preorder X x y))
      ( λ {x} {y} {z} → transitive-leq-Preorder X x y z)
      ( refl-leq-Preorder X)
      ( λ {x} {y} {z} {w} h g f →
        eq-is-prop (is-prop-type-Prop (leq-prop-Preorder X x w)))
      ( λ {x} {y} f → eq-is-prop (is-prop-type-Prop (leq-prop-Preorder X x y)))
      ( λ {x} {y} f → eq-is-prop (is-prop-type-Prop (leq-prop-Preorder X x y)))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  ( is-prop-hom-C : (x y : obj-Precategory C) → is-prop (hom-Precategory C x y))
  where

  preorder-is-prop-hom-Precategory : Preorder l1 l2
  pr1 preorder-is-prop-hom-Precategory =
    obj-Precategory C
  pr1 (pr1 (pr2 preorder-is-prop-hom-Precategory) x y) =
    hom-Precategory C x y
  pr2 (pr1 (pr2 preorder-is-prop-hom-Precategory) x y) =
    is-prop-hom-C x y
  pr1 (pr2 (pr2 preorder-is-prop-hom-Precategory)) x =
    id-hom-Precategory C
  pr2 (pr2 (pr2 preorder-is-prop-hom-Precategory)) x y z =
    comp-hom-Precategory C
```

It remains to show that these constructions form inverses to eachother.
