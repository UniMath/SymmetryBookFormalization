# Large join-semilattices

```agda
module order-theory.large-join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.bottom-elements-large-posets
open import order-theory.join-semilattices
open import order-theory.large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.posets
```

</details>

## Idea

A **large join-semilattice** is a [large poset](order-theory.large-posets.md) in
which every pair of elements has a
[least binary upper bound](order-theory.least-upper-bounds-large-posets.md).

## Definition

### The predicate that a large poset has joins

```agda
record
  has-joins-Large-Poset
    { α : Level → Level}
    { β : Level → Level → Level}
    ( P : Large-Poset α β) :
    UUω
  where
  constructor
    make-has-joins-Large-Poset
  field
    join-has-joins-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      type-Large-Poset P (l1 ⊔ l2)
    is-least-binary-upper-bound-join-has-joins-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      is-least-binary-upper-bound-Large-Poset P x y
        ( join-has-joins-Large-Poset x y)

open has-joins-Large-Poset public
```

### The predicate of being a large join-semilattice

```agda
record
  is-large-join-semilattice-Large-Poset
    { α : Level → Level}
    { β : Level → Level → Level}
    ( P : Large-Poset α β) :
    UUω
  where
  field
    has-joins-is-large-join-semilattice-Large-Poset :
      has-joins-Large-Poset P
    has-bottom-element-is-large-join-semilattice-Large-Poset :
      has-bottom-element-Large-Poset P

open is-large-join-semilattice-Large-Poset public

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (P : Large-Poset α β)
  (H : is-large-join-semilattice-Large-Poset P)
  where

  join-is-large-join-semilattice-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    type-Large-Poset P (l1 ⊔ l2)
  join-is-large-join-semilattice-Large-Poset =
    join-has-joins-Large-Poset
      ( has-joins-is-large-join-semilattice-Large-Poset H)

  is-least-binary-upper-bound-join-is-large-join-semilattice-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    is-least-binary-upper-bound-Large-Poset P x y
      ( join-is-large-join-semilattice-Large-Poset x y)
  is-least-binary-upper-bound-join-is-large-join-semilattice-Large-Poset =
    is-least-binary-upper-bound-join-has-joins-Large-Poset
      ( has-joins-is-large-join-semilattice-Large-Poset H)

  bottom-is-large-join-semilattice-Large-Poset :
    type-Large-Poset P lzero
  bottom-is-large-join-semilattice-Large-Poset =
    bottom-has-bottom-element-Large-Poset
      ( has-bottom-element-is-large-join-semilattice-Large-Poset H)

  is-bottom-element-bottom-is-large-join-semilattice-Large-Poset :
    {l1 : Level} (x : type-Large-Poset P l1) →
    leq-Large-Poset P bottom-is-large-join-semilattice-Large-Poset x
  is-bottom-element-bottom-is-large-join-semilattice-Large-Poset =
    is-bottom-element-bottom-has-bottom-element-Large-Poset
      ( has-bottom-element-is-large-join-semilattice-Large-Poset H)
```

### Large join-semilattices

```agda
record
  Large-Join-Semilattice
    ( α : Level → Level)
    ( β : Level → Level → Level) :
    UUω
  where
  constructor
    make-Large-Join-Semilattice
  field
    large-poset-Large-Join-Semilattice :
      Large-Poset α β
    is-large-join-semilattice-Large-Join-Semilattice :
      is-large-join-semilattice-Large-Poset
        large-poset-Large-Join-Semilattice

open Large-Join-Semilattice public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  where

  type-Large-Join-Semilattice : (l : Level) → UU (α l)
  type-Large-Join-Semilattice =
    type-Large-Poset (large-poset-Large-Join-Semilattice L)

  set-Large-Join-Semilattice : (l : Level) → Set (α l)
  set-Large-Join-Semilattice =
    set-Large-Poset (large-poset-Large-Join-Semilattice L)

  is-set-type-Large-Join-Semilattice :
    {l : Level} → is-set (type-Large-Join-Semilattice l)
  is-set-type-Large-Join-Semilattice =
    is-set-type-Large-Poset (large-poset-Large-Join-Semilattice L)

  leq-Large-Join-Semilattice : Large-Relation β type-Large-Join-Semilattice
  leq-Large-Join-Semilattice =
    leq-Large-Poset (large-poset-Large-Join-Semilattice L)

  refl-leq-Large-Join-Semilattice :
    is-reflexive-Large-Relation
      ( type-Large-Join-Semilattice)
      ( leq-Large-Join-Semilattice)
  refl-leq-Large-Join-Semilattice =
    refl-leq-Large-Poset (large-poset-Large-Join-Semilattice L)

  antisymmetric-leq-Large-Join-Semilattice :
    is-antisymmetric-Large-Relation
      ( type-Large-Join-Semilattice)
      ( leq-Large-Join-Semilattice)
  antisymmetric-leq-Large-Join-Semilattice =
    antisymmetric-leq-Large-Poset (large-poset-Large-Join-Semilattice L)

  transitive-leq-Large-Join-Semilattice :
    is-transitive-Large-Relation
      ( type-Large-Join-Semilattice)
      ( leq-Large-Join-Semilattice)
  transitive-leq-Large-Join-Semilattice =
    transitive-leq-Large-Poset (large-poset-Large-Join-Semilattice L)

  has-joins-Large-Join-Semilattice :
    has-joins-Large-Poset (large-poset-Large-Join-Semilattice L)
  has-joins-Large-Join-Semilattice =
    has-joins-is-large-join-semilattice-Large-Poset
      ( is-large-join-semilattice-Large-Join-Semilattice L)

  join-Large-Join-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Join-Semilattice l1)
    (y : type-Large-Join-Semilattice l2) →
    type-Large-Join-Semilattice (l1 ⊔ l2)
  join-Large-Join-Semilattice =
    join-is-large-join-semilattice-Large-Poset
      ( large-poset-Large-Join-Semilattice L)
      ( is-large-join-semilattice-Large-Join-Semilattice L)

  is-least-binary-upper-bound-join-Large-Join-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Join-Semilattice l1)
    (y : type-Large-Join-Semilattice l2) →
    is-least-binary-upper-bound-Large-Poset
      ( large-poset-Large-Join-Semilattice L)
      ( x)
      ( y)
      ( join-Large-Join-Semilattice x y)
  is-least-binary-upper-bound-join-Large-Join-Semilattice =
    is-least-binary-upper-bound-join-is-large-join-semilattice-Large-Poset
      ( large-poset-Large-Join-Semilattice L)
      ( is-large-join-semilattice-Large-Join-Semilattice L)

  ap-join-Large-Join-Semilattice :
    {l1 l2 : Level}
    {x x' : type-Large-Join-Semilattice l1}
    {y y' : type-Large-Join-Semilattice l2} →
    (x ＝ x') → (y ＝ y') →
    join-Large-Join-Semilattice x y ＝ join-Large-Join-Semilattice x' y'
  ap-join-Large-Join-Semilattice p q =
    ap-binary join-Large-Join-Semilattice p q

  has-bottom-element-Large-Join-Semilattice :
    has-bottom-element-Large-Poset (large-poset-Large-Join-Semilattice L)
  has-bottom-element-Large-Join-Semilattice =
    has-bottom-element-is-large-join-semilattice-Large-Poset
      ( is-large-join-semilattice-Large-Join-Semilattice L)

  bottom-Large-Join-Semilattice :
    type-Large-Join-Semilattice lzero
  bottom-Large-Join-Semilattice =
    bottom-is-large-join-semilattice-Large-Poset
      ( large-poset-Large-Join-Semilattice L)
      ( is-large-join-semilattice-Large-Join-Semilattice L)

  is-bottom-element-bottom-Large-Join-Semilattice :
    {l1 : Level} (x : type-Large-Join-Semilattice l1) →
    leq-Large-Join-Semilattice bottom-Large-Join-Semilattice x
  is-bottom-element-bottom-Large-Join-Semilattice =
    is-bottom-element-bottom-is-large-join-semilattice-Large-Poset
      ( large-poset-Large-Join-Semilattice L)
      ( is-large-join-semilattice-Large-Join-Semilattice L)
```

### Small join semilattices from large join semilattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Join-Semilattice α β)
  where

  poset-Large-Join-Semilattice : (l : Level) → Poset (α l) (β l l)
  poset-Large-Join-Semilattice =
    poset-Large-Poset (large-poset-Large-Join-Semilattice L)

  is-join-semilattice-poset-Large-Join-Semilattice :
    {l : Level} → is-join-semilattice-Poset (poset-Large-Join-Semilattice l)
  pr1 (is-join-semilattice-poset-Large-Join-Semilattice x y) =
    join-Large-Join-Semilattice L x y
  pr2 (is-join-semilattice-poset-Large-Join-Semilattice x y) =
    is-least-binary-upper-bound-join-Large-Join-Semilattice L x y

  order-theoretic-join-semilattice-Large-Join-Semilattice :
    (l : Level) → Order-Theoretic-Join-Semilattice (α l) (β l l)
  pr1 (order-theoretic-join-semilattice-Large-Join-Semilattice l) =
    poset-Large-Join-Semilattice l
  pr2 (order-theoretic-join-semilattice-Large-Join-Semilattice l) =
    is-join-semilattice-poset-Large-Join-Semilattice

  join-semilattice-Large-Join-Semilattice :
    (l : Level) → Join-Semilattice (α l)
  join-semilattice-Large-Join-Semilattice l =
    join-semilattice-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Large-Join-Semilattice l)
```
