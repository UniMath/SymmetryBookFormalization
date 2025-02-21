# Ordinals

```agda
module order-theory.ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.transitive-well-founded-relations
open import order-theory.well-founded-relations
```

</details>

## Idea

An
{{#concept "ordinal" WDID=Q191780 WD="ordinal number" Agda=is-ordinal Agda=Ordinal}}
is a type `X` [equipped](foundation.structure.md) with a
[propositional](foundation-core.propositions.md)
[relation](foundation.binary-relations.md) `_<_` that is

- **Well-founded:** a structure on which it is well-defined to do induction.
- **Transitive:** if `x < y` and `y < z` then `x < z`.
- **Extensional:** `x ＝ y` precisely if they are greater than the same
  elements.

In other words, it is a
[transitive well-founded relation](order-theory.transitive-well-founded-relations.md)
that is `Prop`-valued and extensional.

## Definitions

### The extensionality principle of ordinals

```agda
extensionality-principle-Ordinal :
  {l1 l2 : Level} {X : UU l1} → Relation-Prop l2 X → UU (l1 ⊔ l2)
extensionality-principle-Ordinal {X = X} R =
  (x y : X) →
  ((u : X) → type-Relation-Prop R u x ↔ type-Relation-Prop R u y) → x ＝ y
```

### The predicate of being an ordinal

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Relation-Prop l2 X)
  where

  is-ordinal : UU (l1 ⊔ l2)
  is-ordinal =
    ( is-transitive-well-founded-relation-Relation (type-Relation-Prop R)) ×
    ( extensionality-principle-Ordinal R)
```

### The type of ordinals

```agda
Ordinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Ordinal l1 l2 = Σ (UU l1) (λ X → Σ (Relation-Prop l2 X) is-ordinal)

module _
  {l1 l2 : Level} (O : Ordinal l1 l2)
  where

  type-Ordinal : UU l1
  type-Ordinal = pr1 O

  le-prop-Ordinal : Relation-Prop l2 type-Ordinal
  le-prop-Ordinal = pr1 (pr2 O)

  le-Ordinal : Relation l2 type-Ordinal
  le-Ordinal = type-Relation-Prop le-prop-Ordinal

  is-ordinal-Ordinal : is-ordinal le-prop-Ordinal
  is-ordinal-Ordinal = pr2 (pr2 O)

  is-transitive-well-founded-relation-le-Ordinal :
    is-transitive-well-founded-relation-Relation le-Ordinal
  is-transitive-well-founded-relation-le-Ordinal = pr1 is-ordinal-Ordinal

  transitive-well-founded-relation-Ordinal :
    Transitive-Well-Founded-Relation l2 type-Ordinal
  transitive-well-founded-relation-Ordinal =
    ( le-Ordinal , is-transitive-well-founded-relation-le-Ordinal)

  is-extensional-Ordinal : extensionality-principle-Ordinal le-prop-Ordinal
  is-extensional-Ordinal = pr2 is-ordinal-Ordinal

  transitive-le-Ordinal : is-transitive le-Ordinal
  transitive-le-Ordinal =
    transitive-le-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  is-well-founded-relation-le-Ordinal : is-well-founded-Relation le-Ordinal
  is-well-founded-relation-le-Ordinal =
    is-well-founded-relation-le-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  well-founded-relation-Ordinal : Well-Founded-Relation l2 type-Ordinal
  well-founded-relation-Ordinal =
    well-founded-relation-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  is-asymmetric-le-Ordinal : is-asymmetric le-Ordinal
  is-asymmetric-le-Ordinal =
    is-asymmetric-le-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  is-irreflexive-le-Ordinal : is-irreflexive le-Ordinal
  is-irreflexive-le-Ordinal =
    is-irreflexive-le-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal
```

The associated reflexive relation on an ordinal.

```agda
  leq-Ordinal : Relation (l1 ⊔ l2) type-Ordinal
  leq-Ordinal =
    leq-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  is-prop-leq-Ordinal : {x y : type-Ordinal} → is-prop (leq-Ordinal x y)
  is-prop-leq-Ordinal {y = y} =
    is-prop-Π
      ( λ u →
        is-prop-function-type (is-prop-type-Relation-Prop le-prop-Ordinal u y))

  leq-prop-Ordinal : Relation-Prop (l1 ⊔ l2) type-Ordinal
  leq-prop-Ordinal x y = (leq-Ordinal x y , is-prop-leq-Ordinal)

  refl-leq-Ordinal : is-reflexive leq-Ordinal
  refl-leq-Ordinal =
    refl-leq-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  leq-eq-Ordinal : {x y : type-Ordinal} → x ＝ y → leq-Ordinal x y
  leq-eq-Ordinal =
    leq-eq-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  transitive-leq-Ordinal : is-transitive leq-Ordinal
  transitive-leq-Ordinal =
    transitive-leq-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  leq-le-Ordinal : {x y : type-Ordinal} → le-Ordinal x y → leq-Ordinal x y
  leq-le-Ordinal =
    leq-le-Transitive-Well-Founded-Relation
      transitive-well-founded-relation-Ordinal

  antisymmetric-leq-Ordinal : is-antisymmetric leq-Ordinal
  antisymmetric-leq-Ordinal x y p q =
    is-extensional-Ordinal x y (λ u → (p u , q u))

  is-preorder-leq-Ordinal : is-preorder-Relation-Prop leq-prop-Ordinal
  is-preorder-leq-Ordinal = (refl-leq-Ordinal , transitive-leq-Ordinal)

  preorder-Ordinal : Preorder l1 (l1 ⊔ l2)
  preorder-Ordinal = (type-Ordinal , leq-prop-Ordinal , is-preorder-leq-Ordinal)

  poset-Ordinal : Poset l1 (l1 ⊔ l2)
  poset-Ordinal = (preorder-Ordinal , antisymmetric-leq-Ordinal)

  is-set-type-Ordinal : is-set type-Ordinal
  is-set-type-Ordinal = is-set-type-Poset poset-Ordinal

  set-Ordinal : Set l1
  set-Ordinal = (type-Ordinal , is-set-type-Ordinal)
```
