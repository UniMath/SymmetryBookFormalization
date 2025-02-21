# Decidable posets

```agda
module order-theory.decidable-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-posets
```

</details>

## Idea

A {{#concept "decidable poset" Agda=Decidable-Poset}} is a
[poset](order-theory.posets.md) of which the ordering relation is
[decidable](foundation.decidable-types.md). It follows that decidable posets
have [decidable equality](foundation.decidable-equality.md).

## Definitions

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-decidable-leq-prop-Poset : Prop (l1 ⊔ l2)
  is-decidable-leq-prop-Poset =
    is-decidable-leq-prop-Preorder (preorder-Poset X)

  is-decidable-leq-Poset : UU (l1 ⊔ l2)
  is-decidable-leq-Poset = type-Prop is-decidable-leq-prop-Poset

  is-prop-is-decidable-leq-Poset : is-prop is-decidable-leq-Poset
  is-prop-is-decidable-leq-Poset = is-prop-type-Prop is-decidable-leq-prop-Poset

Decidable-Poset : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Poset l1 l2 = Σ (Poset l1 l2) is-decidable-leq-Poset

module _
  {l1 l2 : Level} (X : Decidable-Poset l1 l2)
  where

  poset-Decidable-Poset : Poset l1 l2
  poset-Decidable-Poset = pr1 X

  preorder-Decidable-Poset : Preorder l1 l2
  preorder-Decidable-Poset = preorder-Poset poset-Decidable-Poset

  is-decidable-leq-Decidable-Poset :
    is-decidable-leq-Poset (poset-Decidable-Poset)
  is-decidable-leq-Decidable-Poset = pr2 X

  type-Decidable-Poset : UU l1
  type-Decidable-Poset = type-Poset poset-Decidable-Poset

  leq-Decidable-Poset-Prop : (x y : type-Decidable-Poset) → Prop l2
  leq-Decidable-Poset-Prop = leq-prop-Poset poset-Decidable-Poset

  leq-Decidable-Poset : (x y : type-Decidable-Poset) → UU l2
  leq-Decidable-Poset = leq-Poset poset-Decidable-Poset

  is-prop-leq-Decidable-Poset :
    (x y : type-Decidable-Poset) → is-prop (leq-Decidable-Poset x y)
  is-prop-leq-Decidable-Poset = is-prop-leq-Poset poset-Decidable-Poset

  decidable-preorder-Decidable-Poset : Decidable-Preorder l1 l2
  pr1 decidable-preorder-Decidable-Poset = preorder-Decidable-Poset
  pr2 decidable-preorder-Decidable-Poset = is-decidable-leq-Decidable-Poset

  leq-decidable-poset-decidable-Prop :
    (x y : type-Decidable-Poset) → Decidable-Prop l2
  leq-decidable-poset-decidable-Prop =
    leq-Decidable-Preorder-Decidable-Prop decidable-preorder-Decidable-Poset

  concatenate-eq-leq-Decidable-Poset :
    {x y z : type-Decidable-Poset} → x ＝ y →
    leq-Decidable-Poset y z → leq-Decidable-Poset x z
  concatenate-eq-leq-Decidable-Poset =
    concatenate-eq-leq-Poset poset-Decidable-Poset

  concatenate-leq-eq-Decidable-Poset :
    {x y z : type-Decidable-Poset} →
    leq-Decidable-Poset x y → y ＝ z → leq-Decidable-Poset x z
  concatenate-leq-eq-Decidable-Poset =
    concatenate-leq-eq-Poset poset-Decidable-Poset

  refl-leq-Decidable-Poset : is-reflexive leq-Decidable-Poset
  refl-leq-Decidable-Poset = refl-leq-Poset poset-Decidable-Poset

  transitive-leq-Decidable-Poset : is-transitive leq-Decidable-Poset
  transitive-leq-Decidable-Poset = transitive-leq-Poset poset-Decidable-Poset

  antisymmetric-leq-Decidable-Poset : is-antisymmetric leq-Decidable-Poset
  antisymmetric-leq-Decidable-Poset =
    antisymmetric-leq-Poset poset-Decidable-Poset

  is-set-type-Decidable-Poset : is-set type-Decidable-Poset
  is-set-type-Decidable-Poset = is-set-type-Poset poset-Decidable-Poset

  set-Decidable-Poset : Set l1
  set-Decidable-Poset = set-Poset poset-Decidable-Poset
```

## Properties

### Decidable posets have decidable equality

**Proof.** By antisymmetry, equality `x ＝ y` in a poset is characterized by
smiliarity, `(x ≤ y) × (y ≤ x)`, and this is a decidable type.

```agda
module _
  {l1 l2 : Level} (P : Decidable-Poset l1 l2)
  where

  is-decidable-sim-Decidable-Poset :
    {x y : type-Decidable-Poset P} →
    is-decidable (sim-Poset (poset-Decidable-Poset P) x y)
  is-decidable-sim-Decidable-Poset {x} {y} =
    is-decidable-product
      ( is-decidable-leq-Decidable-Poset P x y)
      ( is-decidable-leq-Decidable-Poset P y x)

  has-decidable-equality-type-Decidable-Poset :
    has-decidable-equality (type-Decidable-Poset P)
  has-decidable-equality-type-Decidable-Poset x y =
    is-decidable-equiv
      ( extensionality-Poset (poset-Decidable-Poset P) x y)
      ( is-decidable-sim-Decidable-Poset)

  discrete-type-Decidable-Poset : Discrete-Type l1
  discrete-type-Decidable-Poset =
    ( type-Decidable-Poset P , has-decidable-equality-type-Decidable-Poset)
```
