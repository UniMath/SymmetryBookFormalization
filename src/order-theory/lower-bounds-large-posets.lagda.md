# Lower bounds in large posets

```agda
module order-theory.lower-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
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

A **binary lower bound** of two elements `a` and `b` in a large poset `P` is an
element `x` such that both `x ≤ a` and `x ≤ b` hold. Similarly, a **lower
bound** of a family of elements `a : I → P` in a large poset `P` is an element
`x` such that `x ≤ a i` holds for every `i : I`.

## Definitions

### The predicate that an element of a large poset is a lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-lower-bound-prop-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → Prop (β l3 l1 ⊔ β l3 l2)
  is-binary-lower-bound-prop-Large-Poset x =
    leq-prop-Large-Poset P x a ∧ leq-prop-Large-Poset P x b

  is-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UU (β l3 l1 ⊔ β l3 l2)
  is-binary-lower-bound-Large-Poset x =
    type-Prop (is-binary-lower-bound-prop-Large-Poset x)
```

### The predicate of being a lower bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-lower-bound-prop-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → Prop (β l3 l2 ⊔ l1)
  is-lower-bound-prop-family-of-elements-Large-Poset y =
    Π-Prop I (λ i → leq-prop-Large-Poset P y (x i))

  is-lower-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → UU (β l3 l2 ⊔ l1)
  is-lower-bound-family-of-elements-Large-Poset y =
    type-Prop (is-lower-bound-prop-family-of-elements-Large-Poset y)

  is-prop-is-lower-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) →
    is-prop (is-lower-bound-family-of-elements-Large-Poset y)
  is-prop-is-lower-bound-family-of-elements-Large-Poset y =
    is-prop-type-Prop (is-lower-bound-prop-family-of-elements-Large-Poset y)
```

## Properties

### An element of a dependent product of large posets is a binary lower bound of two elements if and only if it is a pointwise binary lower bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  {l1 l2 : Level} (x : type-Π-Large-Poset P l1) (y : type-Π-Large-Poset P l2)
  where

  is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    ((i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) →
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  pr1 (is-binary-lower-bound-Π-Large-Poset z H) i = pr1 (H i)
  pr2 (is-binary-lower-bound-Π-Large-Poset z H) i = pr2 (H i)

  is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z →
    (i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)
  pr1 (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z H i) =
    pr1 H i
  pr2 (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z H i) =
    pr2 H i

  logical-equivalence-is-binary-lower-bound-Π-Large-Poset :
    {l3 : Level} (z : type-Π-Large-Poset P l3) →
    ((i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) ↔
    is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  pr1 (logical-equivalence-is-binary-lower-bound-Π-Large-Poset z) =
    is-binary-lower-bound-Π-Large-Poset z
  pr2 (logical-equivalence-is-binary-lower-bound-Π-Large-Poset z) =
    is-binary-lower-bound-is-binary-lower-bound-Π-Large-Poset z
```

### An element `x : Π-Large-Poset P` of a dependent product of large posets `P i` indexed by `i : I` is a lower bound of a family `a : J → Π-Large-Poset P` if and only if `x i` is a lower bound of the family `(j ↦ a j i) : J → P i` of elements of `P i`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  {l2 l3 : Level} {J : UU l2} (a : J → type-Π-Large-Poset P l3)
  {l4 : Level} (x : type-Π-Large-Poset P l4)
  where

  is-lower-bound-family-of-elements-Π-Large-Poset :
    ( (i : I) →
      is-lower-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)) →
    is-lower-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  is-lower-bound-family-of-elements-Π-Large-Poset H j i = H i j

  map-inv-is-lower-bound-family-of-elements-Π-Large-Poset :
    is-lower-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x →
    (i : I) →
    is-lower-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)
  map-inv-is-lower-bound-family-of-elements-Π-Large-Poset H i j = H j i

  logical-equivalence-is-lower-bound-family-of-elements-Π-Large-Poset :
    ( (i : I) →
      is-lower-bound-family-of-elements-Large-Poset (P i) (λ j → a j i) (x i)) ↔
    is-lower-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  pr1 logical-equivalence-is-lower-bound-family-of-elements-Π-Large-Poset =
    is-lower-bound-family-of-elements-Π-Large-Poset
  pr2 logical-equivalence-is-lower-bound-family-of-elements-Π-Large-Poset =
    map-inv-is-lower-bound-family-of-elements-Π-Large-Poset
```
