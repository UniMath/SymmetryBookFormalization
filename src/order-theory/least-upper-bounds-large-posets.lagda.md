# Least upper bounds in large posets

```agda
module order-theory.least-upper-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A **least upper bound** of a family of elements `a : I → P` in a large poset `P`
is an element `x` in `P` such that the logial equivalence

```text
  is-upper-bound-family-of-elements-Large-Poset P a y ↔ (x ≤ y)
```

holds for every element in `P`.

## Definitions

### The predicate on large-posets of being a least upper bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-least-upper-bound-family-of-elements-Large-Poset :
    type-Large-Poset P l3 → UUω
  is-least-upper-bound-family-of-elements-Large-Poset y =
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-upper-bound-family-of-elements-Large-Poset P x z ↔ leq-Large-Poset P y z
```

### The predicate on families of elements in large posets of having least upper bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  record
    has-least-upper-bound-family-of-elements-Large-Poset : UUω
    where
    field
      sup-has-least-upper-bound-family-of-elements-Large-Poset :
        type-Large-Poset P (l1 ⊔ l2)
      is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset :
        is-least-upper-bound-family-of-elements-Large-Poset P x
          sup-has-least-upper-bound-family-of-elements-Large-Poset

  open has-least-upper-bound-family-of-elements-Large-Poset public
```

## Properties

### A family of least upper bounds of families of elements in a family of large poset is a least upper bound in their dependent product

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  {l2 l3 : Level} {J : UU l2} (a : J → type-Π-Large-Poset P l3)
  {l4 : Level} (x : type-Π-Large-Poset P l4)
  where

  is-least-upper-bound-Π-Large-Poset :
    ( (i : I) →
      is-least-upper-bound-family-of-elements-Large-Poset
        ( P i)
        ( λ j → a j i)
        ( x i)) →
    is-least-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  is-least-upper-bound-Π-Large-Poset H y =
    logical-equivalence-reasoning
      is-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a y
      ↔ ( (i : I) →
          is-upper-bound-family-of-elements-Large-Poset
            ( P i)
            ( λ j → a j i)
            ( y i))
        by
        inv-iff
          ( logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Poset
            ( P)
              ( a)
              ( y))
      ↔ leq-Π-Large-Poset P x y
        by
        iff-Π (λ i → H i (y i))
```
