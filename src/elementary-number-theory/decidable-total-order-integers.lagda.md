# The decidable total order of integers

```agda
module elementary-number-theory.decidable-total-order-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-preorders
open import order-theory.decidable-total-orders
open import order-theory.decidable-total-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
open import order-theory.total-preorders
```

</details>

## Idea

The type of [integers](elementary-number-theory.integers.md)
[equipped](foundation.structure.md) with its
[standard ordering relation](elementary-number-theory.inequality-integers.md)
forms a [decidable total order](order-theory.decidable-total-orders.md).

## Definitions

### The totally ordered set of integers ordered by inequality

```agda
ℤ-Preorder : Preorder lzero lzero
pr1 ℤ-Preorder = ℤ
pr1 (pr2 ℤ-Preorder) = leq-ℤ-Prop
pr1 (pr2 (pr2 ℤ-Preorder)) = refl-leq-ℤ
pr2 (pr2 (pr2 ℤ-Preorder)) = transitive-leq-ℤ

ℤ-Decidable-Preorder : Decidable-Preorder lzero lzero
pr1 ℤ-Decidable-Preorder = ℤ-Preorder
pr2 ℤ-Decidable-Preorder = is-decidable-leq-ℤ

ℤ-Poset : Poset lzero lzero
pr1 ℤ-Poset = ℤ-Preorder
pr2 ℤ-Poset a b = antisymmetric-leq-ℤ

ℤ-Decidable-Poset : Decidable-Poset lzero lzero
pr1 ℤ-Decidable-Poset = ℤ-Poset
pr2 ℤ-Decidable-Poset = is-decidable-leq-ℤ

is-total-leq-ℤ : is-total-Poset ℤ-Poset
is-total-leq-ℤ x y = unit-trunc-Prop (linear-leq-ℤ x y)

ℤ-Total-Preorder : Total-Preorder lzero lzero
pr1 ℤ-Total-Preorder = ℤ-Preorder
pr2 ℤ-Total-Preorder a b = unit-trunc-Prop (linear-leq-ℤ a b)

ℤ-Decidable-Total-Preorder : Decidable-Total-Preorder lzero lzero
pr1 ℤ-Decidable-Total-Preorder = ℤ-Preorder
pr1 (pr2 ℤ-Decidable-Total-Preorder) a b = unit-trunc-Prop (linear-leq-ℤ a b)
pr2 (pr2 ℤ-Decidable-Total-Preorder) = is-decidable-leq-ℤ

ℤ-Total-Order : Total-Order lzero lzero
pr1 ℤ-Total-Order = ℤ-Poset
pr2 ℤ-Total-Order a b = unit-trunc-Prop (linear-leq-ℤ a b)

ℤ-Decidable-Total-Order : Decidable-Total-Order lzero lzero
pr1 ℤ-Decidable-Total-Order = ℤ-Poset
pr1 (pr2 ℤ-Decidable-Total-Order) a b = unit-trunc-Prop (linear-leq-ℤ a b)
pr2 (pr2 ℤ-Decidable-Total-Order) = is-decidable-leq-ℤ
```
