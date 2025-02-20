# Upper bounds in large posets

```agda
module order-theory.upper-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
```

</details>

## Idea

A **binary upper bound** of two elements `a` and `b` of a
[large poset](order-theory.large-posets.md) `P` is an element `x` of `P` such
that `a ≤ x` and `b ≤ x` both hold. Similarly, an **upper bound** of a family
`a : I → P` of elements of `P` is an element `x` of `P` such that the inequality
`(a i) ≤ x` holds for every `i : I`.

## Definitions

### The predicate of being an upper bound of a pair of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-upper-bound-prop-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → Prop (β l1 l3 ⊔ β l2 l3)
  is-binary-upper-bound-prop-Large-Poset y =
    leq-prop-Large-Poset P a y ∧ leq-prop-Large-Poset P b y

  is-binary-upper-bound-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → UU (β l1 l3 ⊔ β l2 l3)
  is-binary-upper-bound-Large-Poset y =
    type-Prop (is-binary-upper-bound-prop-Large-Poset y)
```

### The predicate of being an upper bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-upper-bound-prop-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → Prop (β l2 l3 ⊔ l1)
  is-upper-bound-prop-family-of-elements-Large-Poset y =
    Π-Prop I (λ i → leq-prop-Large-Poset P (x i) y)

  is-upper-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → UU (β l2 l3 ⊔ l1)
  is-upper-bound-family-of-elements-Large-Poset y =
    type-Prop (is-upper-bound-prop-family-of-elements-Large-Poset y)

  is-prop-is-upper-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) →
    is-prop (is-upper-bound-family-of-elements-Large-Poset y)
  is-prop-is-upper-bound-family-of-elements-Large-Poset y =
    is-prop-type-Prop (is-upper-bound-prop-family-of-elements-Large-Poset y)
```

## Properties

### An element `x : Π-Large-Poset P` of a dependent product of large posets `P i` indexed by `i : I` is an upper bound of a family `a : J → Π-Large-Poset P` if and only if `x i` is an upper bound of the family `(j ↦ a j i) : J → P i` of elements of `P i`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  {l2 l3 : Level} {J : UU l2} (a : J → type-Π-Large-Poset P l3)
  {l4 : Level} (x : type-Π-Large-Poset P l4)
  where

  is-upper-bound-family-of-elements-Π-Large-Poset :
    ( (i : I) →
      is-upper-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)) →
    is-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  is-upper-bound-family-of-elements-Π-Large-Poset H j i = H i j

  map-inv-is-upper-bound-family-of-elements-Π-Large-Poset :
    is-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x →
    (i : I) →
    is-upper-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)
  map-inv-is-upper-bound-family-of-elements-Π-Large-Poset H i j = H j i

  logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Poset :
    ( (i : I) →
      is-upper-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)) ↔
    is-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  pr1 logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Poset =
    is-upper-bound-family-of-elements-Π-Large-Poset
  pr2 logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Poset =
    map-inv-is-upper-bound-family-of-elements-Π-Large-Poset
```
