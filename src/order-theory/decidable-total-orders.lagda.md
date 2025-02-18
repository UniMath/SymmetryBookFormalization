# Decidable total orders

```agda
module order-theory.decidable-total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.decidable-posets
open import order-theory.decidable-total-preorders
open import order-theory.greatest-lower-bounds-posets
open import order-theory.join-semilattices
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-posets
open import order-theory.total-orders
```

</details>

## Idea

A **decidable total order** is a [total order](order-theory.total-orders.md) of
which the inequality [relation](foundation.binary-relations.md) is
[decidable](foundation.decidable-relations.md).

## Definitions

### The predicate on posets of being decidable total orders

```agda
is-decidable-total-prop-Poset : {l1 l2 : Level} → Poset l1 l2 → Prop (l1 ⊔ l2)
is-decidable-total-prop-Poset P =
  product-Prop (is-total-Poset-Prop P) (is-decidable-leq-prop-Poset P)

is-decidable-total-Poset : {l1 l2 : Level} → Poset l1 l2 → UU (l1 ⊔ l2)
is-decidable-total-Poset P = type-Prop (is-decidable-total-prop-Poset P)

is-prop-is-decidable-total-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) → is-prop (is-decidable-total-Poset P)
is-prop-is-decidable-total-Poset P =
  is-prop-type-Prop (is-decidable-total-prop-Poset P)
```

### The type of decidable total orders

```agda
Decidable-Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Decidable-Total-Order l1 l2 = Σ (Poset l1 l2) (is-decidable-total-Poset)

module _
  {l1 l2 : Level} (P : Decidable-Total-Order l1 l2)
  where

  poset-Decidable-Total-Order : Poset l1 l2
  poset-Decidable-Total-Order = pr1 P

  is-total-poset-Decidable-Total-Order :
    is-total-Poset (poset-Decidable-Total-Order)
  is-total-poset-Decidable-Total-Order = pr1 (pr2 P)

  is-decidable-poset-Decidable-Total-Order :
    is-decidable-leq-Poset (poset-Decidable-Total-Order)
  is-decidable-poset-Decidable-Total-Order = pr2 (pr2 P)

  type-Decidable-Total-Order : UU l1
  type-Decidable-Total-Order = type-Poset poset-Decidable-Total-Order

  leq-Decidable-Total-Order-Prop :
    (x y : type-Decidable-Total-Order) → Prop l2
  leq-Decidable-Total-Order-Prop = leq-prop-Poset poset-Decidable-Total-Order

  leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) → UU l2
  leq-Decidable-Total-Order = leq-Poset poset-Decidable-Total-Order

  is-prop-leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (leq-Decidable-Total-Order x y)
  is-prop-leq-Decidable-Total-Order =
    is-prop-leq-Poset poset-Decidable-Total-Order

  le-Decidable-Total-Order-Prop :
    (x y : type-Decidable-Total-Order) → Prop (l1 ⊔ l2)
  le-Decidable-Total-Order-Prop =
    le-prop-Poset poset-Decidable-Total-Order

  le-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) → UU (l1 ⊔ l2)
  le-Decidable-Total-Order =
    le-Poset poset-Decidable-Total-Order

  is-prop-le-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (le-Decidable-Total-Order x y)
  is-prop-le-Decidable-Total-Order =
    is-prop-le-Poset poset-Decidable-Total-Order

  decidable-poset-Decidable-Total-Order : Decidable-Poset l1 l2
  pr1 decidable-poset-Decidable-Total-Order = poset-Decidable-Total-Order
  pr2 decidable-poset-Decidable-Total-Order =
    is-decidable-poset-Decidable-Total-Order

  leq-total-decidable-poset-decidable-Prop :
    (x y : type-Decidable-Total-Order) → Decidable-Prop l2
  leq-total-decidable-poset-decidable-Prop =
    leq-decidable-poset-decidable-Prop decidable-poset-Decidable-Total-Order

  concatenate-eq-leq-Decidable-Total-Order :
    {x y z : type-Decidable-Total-Order} → x ＝ y →
    leq-Decidable-Total-Order y z → leq-Decidable-Total-Order x z
  concatenate-eq-leq-Decidable-Total-Order =
    concatenate-eq-leq-Poset poset-Decidable-Total-Order

  concatenate-leq-eq-Decidable-Total-Order :
    {x y z : type-Decidable-Total-Order} →
    leq-Decidable-Total-Order x y → y ＝ z → leq-Decidable-Total-Order x z
  concatenate-leq-eq-Decidable-Total-Order =
    concatenate-leq-eq-Poset poset-Decidable-Total-Order

  refl-leq-Decidable-Total-Order : is-reflexive leq-Decidable-Total-Order
  refl-leq-Decidable-Total-Order =
    refl-leq-Poset poset-Decidable-Total-Order

  transitive-leq-Decidable-Total-Order : is-transitive leq-Decidable-Total-Order
  transitive-leq-Decidable-Total-Order =
    transitive-leq-Poset poset-Decidable-Total-Order

  preorder-Decidable-Total-Order : Preorder l1 l2
  preorder-Decidable-Total-Order = preorder-Poset poset-Decidable-Total-Order

  decidable-total-preorder-Decidable-Total-Order :
    Decidable-Total-Preorder l1 l2
  pr1 decidable-total-preorder-Decidable-Total-Order =
    preorder-Decidable-Total-Order
  pr1 (pr2 decidable-total-preorder-Decidable-Total-Order) =
    is-total-poset-Decidable-Total-Order
  pr2 (pr2 decidable-total-preorder-Decidable-Total-Order) =
    is-decidable-poset-Decidable-Total-Order

  leq-or-strict-greater-Decidable-Poset :
    (x y : type-Decidable-Total-Order) → UU (l1 ⊔ l2)
  leq-or-strict-greater-Decidable-Poset =
    leq-or-strict-greater-Decidable-Preorder
      decidable-total-preorder-Decidable-Total-Order

  is-leq-or-strict-greater-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    leq-or-strict-greater-Decidable-Poset x y
  is-leq-or-strict-greater-Decidable-Total-Order =
    is-leq-or-strict-greater-Decidable-Total-Preorder
      decidable-total-preorder-Decidable-Total-Order

  antisymmetric-leq-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    leq-Decidable-Total-Order x y → leq-Decidable-Total-Order y x → Id x y
  antisymmetric-leq-Decidable-Total-Order =
    antisymmetric-leq-Poset poset-Decidable-Total-Order

  is-prop-leq-or-strict-greater-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order) →
    is-prop (leq-or-strict-greater-Decidable-Poset x y)
  is-prop-leq-or-strict-greater-Decidable-Total-Order x y =
    is-prop-coproduct
      ( λ p q →
        pr1 q (inv (antisymmetric-leq-Decidable-Total-Order x y p (pr2 q))))
      ( is-prop-leq-Decidable-Total-Order x y)
      ( is-prop-le-Decidable-Total-Order y x)

  is-set-type-Decidable-Total-Order : is-set type-Decidable-Total-Order
  is-set-type-Decidable-Total-Order =
    is-set-type-Poset poset-Decidable-Total-Order

  set-Decidable-Total-Order : Set l1
  set-Decidable-Total-Order = set-Poset poset-Decidable-Total-Order
```

## Properties


### Decidable total orders have decidable equality

**Proof.** By antisymmetry, equality `x ＝ y` in a decidable total order is
characterized by smiliarity, `(x ≤ y) × (y ≤ x)`, and this is a decidable type.

```agda
module _
  {l1 l2 : Level} (P : Decidable-Total-Order l1 l2)
  where

  is-decidable-sim-Decidable-Total-Order :
    {x y : type-Decidable-Total-Order P} →
    is-decidable (sim-Poset (poset-Decidable-Total-Order P) x y)
  is-decidable-sim-Decidable-Total-Order =
    is-decidable-sim-Decidable-Poset (decidable-poset-Decidable-Total-Order P)

  has-decidable-equality-type-Decidable-Total-Order :
    has-decidable-equality (type-Decidable-Total-Order P)
  has-decidable-equality-type-Decidable-Total-Order =
    has-decidable-equality-type-Decidable-Poset
      ( decidable-poset-Decidable-Total-Order P)

  discrete-type-Decidable-Total-Order : Discrete-Type l1
  discrete-type-Decidable-Total-Order =
    discrete-type-Decidable-Poset (decidable-poset-Decidable-Total-Order P)
```

### Any two elements in a decidable total order have a minimum and maximum

```agda
module _
  {l1 l2 : Level}
  (T : Decidable-Total-Order l1 l2)
  (x y : type-Decidable-Total-Order T)
  where

  min-Decidable-Total-Order : type-Decidable-Total-Order T
  min-Decidable-Total-Order =
    rec-coproduct
      ( λ x≤y → x)
      ( λ y<x → y)
      ( is-leq-or-strict-greater-Decidable-Total-Order T x y)

  max-Decidable-Total-Order : type-Decidable-Total-Order T
  max-Decidable-Total-Order =
    rec-coproduct
      ( λ x≤y → y)
      ( λ y<x → x)
      ( is-leq-or-strict-greater-Decidable-Total-Order T x y)
```

### The binary minimum is the binary greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (T : Decidable-Total-Order l1 l2)
  (x y : type-Decidable-Total-Order T)
  where

  min-is-greatest-binary-lower-bound-Decidable-Total-Order :
    is-greatest-binary-lower-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( x)
      ( y)
      ( min-Decidable-Total-Order T x y)
  pr1 (min-is-greatest-binary-lower-bound-Decidable-Total-Order z) (z≤x , z≤y)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = z≤x
  ... | inr y<x = z≤y
  pr1 (pr2 (min-is-greatest-binary-lower-bound-Decidable-Total-Order z) z≤min)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = z≤min
  ... | inr y<x = transitive-leq-Decidable-Total-Order T z y x (pr2 y<x) z≤min
  pr2 (pr2 (min-is-greatest-binary-lower-bound-Decidable-Total-Order z) z≤min)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = transitive-leq-Decidable-Total-Order T z x y x≤y z≤min
  ... | inr y<x = z≤min

  has-greatest-binary-lower-bound-Decidable-Total-Order :
    has-greatest-binary-lower-bound-Poset (poset-Decidable-Total-Order T) x y
  pr1 has-greatest-binary-lower-bound-Decidable-Total-Order =
    min-Decidable-Total-Order T x y
  pr2 has-greatest-binary-lower-bound-Decidable-Total-Order =
    min-is-greatest-binary-lower-bound-Decidable-Total-Order
```

### The minimum of two values is a lower bound

```agda
module _
  {l1 l2 : Level}
  (T : Decidable-Total-Order l1 l2)
  (x y : type-Decidable-Total-Order T)
  where

  leq-left-min-Decidable-Total-Order :
    leq-Decidable-Total-Order T (min-Decidable-Total-Order T x y) x
  leq-left-min-Decidable-Total-Order =
    leq-left-is-greatest-binary-lower-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( min-is-greatest-binary-lower-bound-Decidable-Total-Order T x y)

  leq-right-min-Decidable-Total-Order :
    leq-Decidable-Total-Order T (min-Decidable-Total-Order T x y) y
  leq-right-min-Decidable-Total-Order =
    leq-right-is-greatest-binary-lower-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( min-is-greatest-binary-lower-bound-Decidable-Total-Order T x y)
```

### The maximum of two values is their least upper bound

```agda
  max-is-least-binary-upper-bound-Decidable-Total-Order :
    is-least-binary-upper-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( x)
      ( y)
      ( max-Decidable-Total-Order T x y)
  pr1 (max-is-least-binary-upper-bound-Decidable-Total-Order z) (x≤z , y≤z)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = y≤z
  ... | inr y<x = x≤z
  pr1 (pr2 (max-is-least-binary-upper-bound-Decidable-Total-Order z) min≤z)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = transitive-leq-Decidable-Total-Order T x y z min≤z x≤y
  ... | inr y<x = min≤z
  pr2 (pr2 (max-is-least-binary-upper-bound-Decidable-Total-Order z) min≤z)
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = min≤z
  ... | inr y<x = transitive-leq-Decidable-Total-Order T y x z min≤z (pr2 y<x)

  has-least-binary-upper-bound-Decidable-Total-Order :
    has-least-binary-upper-bound-Poset (poset-Decidable-Total-Order T) x y
  pr1 has-least-binary-upper-bound-Decidable-Total-Order =
    max-Decidable-Total-Order T x y
  pr2 has-least-binary-upper-bound-Decidable-Total-Order =
    max-is-least-binary-upper-bound-Decidable-Total-Order
```

### The maximum of two values is an upper bound

```agda
  leq-left-max-Decidable-Total-Order :
    leq-Decidable-Total-Order T x (max-Decidable-Total-Order T x y)
  leq-left-max-Decidable-Total-Order =
    leq-left-is-least-binary-upper-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( max-is-least-binary-upper-bound-Decidable-Total-Order)

  leq-right-max-Decidable-Total-Order :
    leq-Decidable-Total-Order T y (max-Decidable-Total-Order T x y)
  leq-right-max-Decidable-Total-Order =
    leq-right-is-least-binary-upper-bound-Poset
      ( poset-Decidable-Total-Order T)
      ( max-is-least-binary-upper-bound-Decidable-Total-Order)
```

### Decidable total orders are meet semilattices

```agda
module _
  {l1 l2 : Level}
  (T : Decidable-Total-Order l1 l2)
  where

  is-meet-semilattice-Decidable-Total-Order :
    is-meet-semilattice-Poset (poset-Decidable-Total-Order T)
  is-meet-semilattice-Decidable-Total-Order =
    has-greatest-binary-lower-bound-Decidable-Total-Order T

  order-theoretic-meet-semilattice-Decidable-Total-Order :
    Order-Theoretic-Meet-Semilattice l1 l2
  order-theoretic-meet-semilattice-Decidable-Total-Order =
    poset-Decidable-Total-Order T , is-meet-semilattice-Decidable-Total-Order
```

### Decidable total orders are join semilattices

```agda
  is-join-semilattice-Decidable-Total-Order :
    is-join-semilattice-Poset (poset-Decidable-Total-Order T)
  is-join-semilattice-Decidable-Total-Order =
    has-least-binary-upper-bound-Decidable-Total-Order T

  order-theoretic-join-semilattice-Decidable-Total-Order :
    Order-Theoretic-Join-Semilattice l1 l2
  order-theoretic-join-semilattice-Decidable-Total-Order =
    poset-Decidable-Total-Order T , is-join-semilattice-Decidable-Total-Order
```

### The binary minimum operation is associative

```agda
  associative-min-Decidable-Total-Order :
    (x y z : type-Decidable-Total-Order T) →
    min-Decidable-Total-Order T (min-Decidable-Total-Order T x y) z ＝
    min-Decidable-Total-Order T x (min-Decidable-Total-Order T y z)
  associative-min-Decidable-Total-Order =
    associative-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Decidable-Total-Order)
```

### The binary maximum operation is associative

```agda
  associative-max-Decidable-Total-Order :
    (x y z : type-Decidable-Total-Order T) →
    max-Decidable-Total-Order T (max-Decidable-Total-Order T x y) z ＝
    max-Decidable-Total-Order T x (max-Decidable-Total-Order T y z)
  associative-max-Decidable-Total-Order =
    associative-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Decidable-Total-Order)
```

### The binary minimum operation is commutative

```agda
  commutative-min-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    min-Decidable-Total-Order T x y ＝ min-Decidable-Total-Order T y x
  commutative-min-Decidable-Total-Order =
    commutative-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Decidable-Total-Order)
```

### The binary maximum operation is commutative

```agda
  commutative-max-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    max-Decidable-Total-Order T x y ＝ max-Decidable-Total-Order T y x
  commutative-max-Decidable-Total-Order =
    commutative-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Decidable-Total-Order)
```

### The binary minimum operation is idempotent

```agda
  idempotent-min-Decidable-Total-Order :
    (x : type-Decidable-Total-Order T) →
    min-Decidable-Total-Order T x x ＝ x
  idempotent-min-Decidable-Total-Order =
    idempotent-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Decidable-Total-Order)
```

### The binary maximum operation is idempotent

```agda
  idempotent-max-Decidable-Total-Order :
    (x : type-Decidable-Total-Order T) →
    max-Decidable-Total-Order T x x ＝ x
  idempotent-max-Decidable-Total-Order =
    idempotent-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Decidable-Total-Order)
```

### If `x` is less than or equal to `y`, the minimum of `x` and `y` is `x`

```agda
  left-leq-right-min-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    leq-Decidable-Total-Order T x y → min-Decidable-Total-Order T x y ＝ x
  left-leq-right-min-Decidable-Total-Order x y H
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = refl
  ... | inr y<x =
    ex-falso
      ( pr1 y<x (antisymmetric-leq-Decidable-Total-Order T y x (pr2 y<x) H))
```

### If `y` is less than or equal to `x`, the minimum of `x` and `y` is `y`

```agda
  right-leq-left-min-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    leq-Decidable-Total-Order T y x → min-Decidable-Total-Order T x y ＝ y
  right-leq-left-min-Decidable-Total-Order x y H
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = antisymmetric-leq-Decidable-Total-Order T x y x≤y H
  ... | inr y<x = refl
```

### If `x` is less than or equal to `y`, the maximum of `x` and `y` is `y`

```agda
  left-leq-right-max-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    leq-Decidable-Total-Order T x y → max-Decidable-Total-Order T x y ＝ y
  left-leq-right-max-Decidable-Total-Order x y H
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = refl
  ... | inr y<x =
    ex-falso
      ( pr1 y<x (antisymmetric-leq-Decidable-Total-Order T y x (pr2 y<x) H))
```

### If `y` is less than or equal to `x`, the maximum of `x` and `y` is `x`

```agda
  right-leq-left-max-Decidable-Total-Order :
    (x y : type-Decidable-Total-Order T) →
    leq-Decidable-Total-Order T y x → max-Decidable-Total-Order T x y ＝ x
  right-leq-left-max-Decidable-Total-Order x y H
    with is-leq-or-strict-greater-Decidable-Total-Order T x y
  ... | inl x≤y = antisymmetric-leq-Decidable-Total-Order T y x H x≤y
  ... | inr y<x = refl
```
