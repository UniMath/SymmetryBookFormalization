# Greatest lower bounds in large posets

```agda
module order-theory.greatest-lower-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.lower-bounds-large-posets
```

</details>

## Idea

A **greatest binary lower bound** of two elements `a` and `b` in a large poset
`P` is an element `x` such that for every element `y` in `P` the logical
equivalence

```text
  is-binary-lower-bound-Large-Poset P a b y ↔ y ≤ x
```

holds.

## Definitions

### The predicate that an element of a large poset is the greatest lower bound of two elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-greatest-binary-lower-bound-Large-Poset :
    {l3 : Level} → type-Large-Poset P l3 → UUω
  is-greatest-binary-lower-bound-Large-Poset x =
    {l4 : Level} (y : type-Large-Poset P l4) →
    is-binary-lower-bound-Large-Poset P a b y ↔ leq-Large-Poset P y x
```

### The predicate on large posets of being a greatest lower bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-greatest-lower-bound-family-of-elements-Large-Poset :
    type-Large-Poset P l3 → UUω
  is-greatest-lower-bound-family-of-elements-Large-Poset y =
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-lower-bound-family-of-elements-Large-Poset P x z ↔ leq-Large-Poset P z y

  leq-is-greatest-lower-bound-family-of-elements-Large-Poset :
    (y : type-Large-Poset P l3) →
    is-greatest-lower-bound-family-of-elements-Large-Poset y →
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-lower-bound-family-of-elements-Large-Poset P x z →
    leq-Large-Poset P z y
  leq-is-greatest-lower-bound-family-of-elements-Large-Poset y H z K =
    forward-implication (H z) K
```

### The predicate on large posets of having a greatest lower bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level)
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  record
    has-greatest-lower-bound-family-of-elements-Large-Poset : UUω
    where
    field
      inf-has-greatest-lower-bound-family-of-elements-Large-Poset :
        type-Large-Poset P (γ ⊔ l1 ⊔ l2)
      is-greatest-lower-bound-inf-has-greatest-lower-bound-family-of-elements-Large-Poset :
        is-greatest-lower-bound-family-of-elements-Large-Poset P x
          inf-has-greatest-lower-bound-family-of-elements-Large-Poset

  open has-greatest-lower-bound-family-of-elements-Large-Poset public
```

## Properties

### Binary greatest lower bounds are lower bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-lower-bound-is-greatest-binary-lower-bound-Large-Poset :
    {l3 : Level} {y : type-Large-Poset P l3} →
    is-greatest-binary-lower-bound-Large-Poset P a b y →
    is-binary-lower-bound-Large-Poset P a b y
  is-binary-lower-bound-is-greatest-binary-lower-bound-Large-Poset H =
    backward-implication (H _) (refl-leq-Large-Poset P _)
```

### Any pointwise greatest lower bound of two elements in a dependent product of large posets is a greatest lower bound

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l : Level} {I : UU l} (P : I → Large-Poset α β)
  {l1 l2 l3 : Level}
  (x : type-Π-Large-Poset P l1)
  (y : type-Π-Large-Poset P l2)
  (z : type-Π-Large-Poset P l3)
  where

  is-greatest-binary-lower-bound-Π-Large-Poset :
    ( (i : I) →
      is-greatest-binary-lower-bound-Large-Poset (P i) (x i) (y i) (z i)) →
    is-greatest-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y z
  is-greatest-binary-lower-bound-Π-Large-Poset H u =
    logical-equivalence-reasoning
      is-binary-lower-bound-Large-Poset (Π-Large-Poset P) x y u
        ↔ ((i : I) → is-binary-lower-bound-Large-Poset (P i) (x i) (y i) (u i))
          by
          inv-iff
            ( logical-equivalence-is-binary-lower-bound-Π-Large-Poset P x y u)
        ↔ leq-Π-Large-Poset P u z
          by iff-Π-iff-family (λ i → H i (u i))
```

### A family of greatest lower bounds of families of elements in a family of large poset is a greatest lower bound in their dependent product

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  {l2 l3 : Level} {J : UU l2} (a : J → type-Π-Large-Poset P l3)
  {l4 : Level} (x : type-Π-Large-Poset P l4)
  where

  is-greatest-lower-bound-Π-Large-Poset :
    ( (i : I) →
      is-greatest-lower-bound-family-of-elements-Large-Poset
        ( P i)
        ( λ j → a j i)
        ( x i)) →
    is-greatest-lower-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  is-greatest-lower-bound-Π-Large-Poset H y =
    logical-equivalence-reasoning
      is-lower-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a y
      ↔ ( (i : I) →
          is-lower-bound-family-of-elements-Large-Poset
            ( P i)
            ( λ j → a j i)
            ( y i))
        by
        inv-iff
          ( logical-equivalence-is-lower-bound-family-of-elements-Π-Large-Poset
            ( P)
              ( a)
              ( y))
      ↔ leq-Π-Large-Poset P y x
        by
        iff-Π-iff-family (λ i → H i (y i))
```
