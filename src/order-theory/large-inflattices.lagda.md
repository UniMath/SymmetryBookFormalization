# Large inflattices

```agda
module order-theory.large-inflattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.inflattices
open import order-theory.large-posets
open import order-theory.lower-bounds-large-posets
open import order-theory.posets
```

</details>

## Idea

A **large inflattice** is a [large poset](order-theory.large-posets.md) `P` such
that for every family

```text
  x : I → type-Large-Poset P l1
```

indexed by `I : UU l2` there is an element `⋀ x : type-Large-Poset P (l1 ⊔ l2)`
such that the logical equivalence

```text
  (∀ᵢ y ≤ xᵢ ) ↔ (y ≤ ⋀ x)
```

holds for every element `y : type-Large-Poset P l3`.

## Definitions

### The predicate on large posets of having least upper bounds of families of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (γ : Level)
  (P : Large-Poset α β)
  where

  is-large-inflattice-Large-Poset : UUω
  is-large-inflattice-Large-Poset =
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2) →
    has-greatest-lower-bound-family-of-elements-Large-Poset γ P x

  module _
    (H : is-large-inflattice-Large-Poset)
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
    where

    inf-is-large-inflattice-Large-Poset : type-Large-Poset P (γ ⊔ l1 ⊔ l2)
    inf-is-large-inflattice-Large-Poset =
      inf-has-greatest-lower-bound-family-of-elements-Large-Poset (H x)

    is-greatest-lower-bound-inf-is-large-inflattice-Large-Poset :
      is-greatest-lower-bound-family-of-elements-Large-Poset P x
        inf-is-large-inflattice-Large-Poset
    is-greatest-lower-bound-inf-is-large-inflattice-Large-Poset =
      is-greatest-lower-bound-inf-has-greatest-lower-bound-family-of-elements-Large-Poset
        ( H x)
```

### Large inflattices

```agda
record
  Large-Inflattice
    (α : Level → Level) (β : Level → Level → Level) (γ : Level) : UUω
  where
  constructor
    make-Large-Inflattice
  field
    large-poset-Large-Inflattice : Large-Poset α β
    is-large-inflattice-Large-Inflattice :
      is-large-inflattice-Large-Poset γ large-poset-Large-Inflattice

open Large-Inflattice public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Inflattice α β γ)
  where

  set-Large-Inflattice : (l : Level) → Set (α l)
  set-Large-Inflattice = set-Large-Poset (large-poset-Large-Inflattice L)

  type-Large-Inflattice : (l : Level) → UU (α l)
  type-Large-Inflattice = type-Large-Poset (large-poset-Large-Inflattice L)

  is-set-type-Large-Inflattice : {l : Level} → is-set (type-Large-Inflattice l)
  is-set-type-Large-Inflattice =
    is-set-type-Large-Poset (large-poset-Large-Inflattice L)

  leq-prop-Large-Inflattice :
    Large-Relation-Prop β type-Large-Inflattice
  leq-prop-Large-Inflattice =
    leq-prop-Large-Poset (large-poset-Large-Inflattice L)

  leq-Large-Inflattice :
    Large-Relation β type-Large-Inflattice
  leq-Large-Inflattice = leq-Large-Poset (large-poset-Large-Inflattice L)

  is-prop-leq-Large-Inflattice :
    is-prop-Large-Relation type-Large-Inflattice leq-Large-Inflattice
  is-prop-leq-Large-Inflattice =
    is-prop-leq-Large-Poset (large-poset-Large-Inflattice L)

  refl-leq-Large-Inflattice :
    is-reflexive-Large-Relation type-Large-Inflattice leq-Large-Inflattice
  refl-leq-Large-Inflattice =
    refl-leq-Large-Poset (large-poset-Large-Inflattice L)

  antisymmetric-leq-Large-Inflattice :
    is-antisymmetric-Large-Relation type-Large-Inflattice leq-Large-Inflattice
  antisymmetric-leq-Large-Inflattice =
    antisymmetric-leq-Large-Poset (large-poset-Large-Inflattice L)

  transitive-leq-Large-Inflattice :
    is-transitive-Large-Relation type-Large-Inflattice leq-Large-Inflattice
  transitive-leq-Large-Inflattice =
    transitive-leq-Large-Poset (large-poset-Large-Inflattice L)

  inf-Large-Inflattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Inflattice l2) →
    type-Large-Inflattice (γ ⊔ l1 ⊔ l2)
  inf-Large-Inflattice x =
    inf-has-greatest-lower-bound-family-of-elements-Large-Poset
      ( is-large-inflattice-Large-Inflattice L x)

  is-lower-bound-family-of-elements-Large-Inflattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Inflattice l2)
    (y : type-Large-Inflattice l3) → UU (β l3 l2 ⊔ l1)
  is-lower-bound-family-of-elements-Large-Inflattice x y =
    is-lower-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Inflattice L)
      ( x)
      ( y)

  is-greatest-lower-bound-family-of-elements-Large-Inflattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Inflattice l2) →
    type-Large-Inflattice l3 → UUω
  is-greatest-lower-bound-family-of-elements-Large-Inflattice =
    is-greatest-lower-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Inflattice L)

  is-greatest-lower-bound-inf-Large-Inflattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Inflattice l2) →
    is-greatest-lower-bound-family-of-elements-Large-Inflattice x
      ( inf-Large-Inflattice x)
  is-greatest-lower-bound-inf-Large-Inflattice x =
    is-greatest-lower-bound-inf-has-greatest-lower-bound-family-of-elements-Large-Poset
      ( is-large-inflattice-Large-Inflattice L x)

  is-lower-bound-inf-Large-Inflattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Inflattice l2) →
    is-lower-bound-family-of-elements-Large-Inflattice x
      ( inf-Large-Inflattice x)
  is-lower-bound-inf-Large-Inflattice x =
    backward-implication
      ( is-greatest-lower-bound-inf-Large-Inflattice x (inf-Large-Inflattice x))
      ( refl-leq-Large-Inflattice (inf-Large-Inflattice x))
```

## Properties

### The operation `inf` is order preserving

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Inflattice α β γ)
  where

  preserves-order-inf-Large-Inflattice :
    {l1 l2 l3 : Level} {I : UU l1}
    {x : I → type-Large-Inflattice L l2}
    {y : I → type-Large-Inflattice L l3} →
    ((i : I) → leq-Large-Inflattice L (y i) (x i)) →
    leq-Large-Inflattice L
      ( inf-Large-Inflattice L y)
      ( inf-Large-Inflattice L x)
  preserves-order-inf-Large-Inflattice {x = x} {y} H =
    forward-implication
      ( is-greatest-lower-bound-inf-Large-Inflattice L x
        ( inf-Large-Inflattice L y))
      ( λ i →
        transitive-leq-Large-Inflattice L
          ( inf-Large-Inflattice L y)
          ( y i)
          ( x i)
          ( H i)
          ( is-lower-bound-inf-Large-Inflattice L y i))
```

### Small inflattices from large inflattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Inflattice α β γ)
  where

  poset-Large-Inflattice : (l : Level) → Poset (α l) (β l l)
  poset-Large-Inflattice = poset-Large-Poset (large-poset-Large-Inflattice L)

  is-inflattice-poset-Large-Inflattice :
    (l1 l2 : Level) →
    is-inflattice-Poset l1 (poset-Large-Inflattice (γ ⊔ l1 ⊔ l2))
  pr1 (is-inflattice-poset-Large-Inflattice l1 l2 I f) =
    inf-Large-Inflattice L f
  pr2 (is-inflattice-poset-Large-Inflattice l1 l2 I f) =
    is-greatest-lower-bound-inf-Large-Inflattice L f

  inflattice-Large-Inflattice :
    (l1 l2 : Level) →
    Inflattice (α (γ ⊔ l1 ⊔ l2)) (β (γ ⊔ l1 ⊔ l2) (γ ⊔ l1 ⊔ l2)) l1
  pr1 (inflattice-Large-Inflattice l1 l2) =
    poset-Large-Inflattice (γ ⊔ l1 ⊔ l2)
  pr2 (inflattice-Large-Inflattice l1 l2) =
    is-inflattice-poset-Large-Inflattice l1 l2
```
