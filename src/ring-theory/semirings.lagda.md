# Semirings

```agda
module ring-theory.semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.magmas
```

</details>

## Idea

The concept of a _semiring_ vastly generalizes the arithmetical structure on the
[natural numbers](elementary-number-theory.natural-numbers.md). A
{{#concept "semiring" Agda=Semiring}} consists of a
[set](foundation-core.sets.md) equipped with addition and multiplication, where
the addition operation gives the semiring the structure of a
[commutative monoid](group-theory.commutative-monoids.md), and the
multiplication is associative, unital, and distributive over addition.

## Definitions

### Semirings

```agda
has-mul-Commutative-Monoid :
  {l : Level} → Commutative-Monoid l → UU l
has-mul-Commutative-Monoid M =
  Σ ( has-associative-mul-Set (set-Commutative-Monoid M))
    ( λ μ →
      ( is-unital (pr1 μ)) ×
      ( ( (a b c : type-Commutative-Monoid M) →
          pr1 μ a (mul-Commutative-Monoid M b c) ＝
          mul-Commutative-Monoid M (pr1 μ a b) (pr1 μ a c)) ×
        ( (a b c : type-Commutative-Monoid M) →
          pr1 μ (mul-Commutative-Monoid M a b) c ＝
          mul-Commutative-Monoid M (pr1 μ a c) (pr1 μ b c))))

zero-laws-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) → has-mul-Commutative-Monoid M → UU l
zero-laws-Commutative-Monoid M ((μ , α) , laws) =
  ( (x : type-Commutative-Monoid M) →
    μ (unit-Commutative-Monoid M) x ＝ unit-Commutative-Monoid M) ×
  ((x : type-Commutative-Monoid M) →
    μ x (unit-Commutative-Monoid M) ＝ unit-Commutative-Monoid M)

Semiring : (l : Level) → UU (lsuc l)
Semiring l1 =
  Σ ( Commutative-Monoid l1)
    ( λ M →
      Σ (has-mul-Commutative-Monoid M) (zero-laws-Commutative-Monoid M))

module _
  {l : Level} (R : Semiring l)
  where

  additive-commutative-monoid-Semiring : Commutative-Monoid l
  additive-commutative-monoid-Semiring = pr1 R

  additive-monoid-Semiring : Monoid l
  additive-monoid-Semiring =
    monoid-Commutative-Monoid additive-commutative-monoid-Semiring

  additive-unital-magma-Semiring : Unital-Magma l
  additive-unital-magma-Semiring =
    unital-magma-Monoid additive-monoid-Semiring

  additive-semigroup-Semiring : Semigroup l
  additive-semigroup-Semiring =
    semigroup-Commutative-Monoid additive-commutative-monoid-Semiring

  set-Semiring : Set l
  set-Semiring =
    set-Commutative-Monoid additive-commutative-monoid-Semiring

  type-Semiring : UU l
  type-Semiring =
    type-Commutative-Monoid additive-commutative-monoid-Semiring

  is-set-type-Semiring : is-set type-Semiring
  is-set-type-Semiring =
    is-set-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring)
```

### Addition in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-add-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-add-Semiring =
    has-associative-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  add-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring =
    mul-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  add-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring' =
    mul-Commutative-Monoid' (additive-commutative-monoid-Semiring R)

  ap-add-Semiring :
    {x y x' y' : type-Semiring R} →
    x ＝ x' → y ＝ y' → add-Semiring x y ＝ add-Semiring x' y'
  ap-add-Semiring =
    ap-mul-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  associative-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring x (add-Semiring y z)
  associative-add-Semiring =
    associative-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  commutative-add-Semiring :
    (x y : type-Semiring R) → add-Semiring x y ＝ add-Semiring y x
  commutative-add-Semiring =
    commutative-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  interchange-add-add-Semiring :
    (x y x' y' : type-Semiring R) →
    ( add-Semiring (add-Semiring x y) (add-Semiring x' y')) ＝
    ( add-Semiring (add-Semiring x x') (add-Semiring y y'))
  interchange-add-add-Semiring =
    interchange-mul-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring (add-Semiring x z) y
  right-swap-add-Semiring =
    right-swap-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  left-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring x (add-Semiring y z) ＝ add-Semiring y (add-Semiring x z)
  left-swap-add-Semiring =
    left-swap-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### The zero element of a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-zero-Semiring : is-unital (add-Semiring R)
  has-zero-Semiring =
    has-unit-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  zero-Semiring : type-Semiring R
  zero-Semiring =
    unit-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  is-zero-Semiring : type-Semiring R → UU l
  is-zero-Semiring x = Id x zero-Semiring

  is-nonzero-Semiring : type-Semiring R → UU l
  is-nonzero-Semiring x = ¬ (is-zero-Semiring x)

  is-zero-semiring-Prop : type-Semiring R → Prop l
  is-zero-semiring-Prop x = Id-Prop (set-Semiring R) x zero-Semiring

  left-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R zero-Semiring x) x
  left-unit-law-add-Semiring =
    left-unit-law-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  right-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R x zero-Semiring) x
  right-unit-law-add-Semiring =
    right-unit-law-mul-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Multiplication in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-mul-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-mul-Semiring = pr1 (pr1 (pr2 R))

  mul-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring = pr1 has-associative-mul-Semiring

  mul-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring' x y = mul-Semiring y x

  ap-mul-Semiring :
    {x x' y y' : type-Semiring R} (p : Id x x') (q : Id y y') →
    Id (mul-Semiring x y) (mul-Semiring x' y')
  ap-mul-Semiring p q = ap-binary mul-Semiring p q

  associative-mul-Semiring :
    (x y z : type-Semiring R) →
    Id (mul-Semiring (mul-Semiring x y) z) (mul-Semiring x (mul-Semiring y z))
  associative-mul-Semiring = pr2 has-associative-mul-Semiring

  multiplicative-semigroup-Semiring : Semigroup l
  pr1 multiplicative-semigroup-Semiring = set-Semiring R
  pr2 multiplicative-semigroup-Semiring = has-associative-mul-Semiring

  left-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    mul-Semiring x (add-Semiring R y z) ＝
    add-Semiring R (mul-Semiring x y) (mul-Semiring x z)
  left-distributive-mul-add-Semiring =
    pr1 (pr2 (pr2 (pr1 (pr2 R))))

  right-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    mul-Semiring (add-Semiring R x y) z ＝
    add-Semiring R (mul-Semiring x z) (mul-Semiring y z)
  right-distributive-mul-add-Semiring =
    pr2 (pr2 (pr2 (pr1 (pr2 R))))

  bidistributive-mul-add-Semiring :
    (u v x y : type-Semiring R) →
    mul-Semiring (add-Semiring R u v) (add-Semiring R x y) ＝
    add-Semiring R
      ( add-Semiring R (mul-Semiring u x) (mul-Semiring u y))
      ( add-Semiring R (mul-Semiring v x) (mul-Semiring v y))
  bidistributive-mul-add-Semiring u v x y =
    ( right-distributive-mul-add-Semiring u v (add-Semiring R x y)) ∙
    ( ap-add-Semiring R
      ( left-distributive-mul-add-Semiring u x y)
      ( left-distributive-mul-add-Semiring v x y))

  left-zero-law-mul-Semiring :
    (x : type-Semiring R) → mul-Semiring (zero-Semiring R) x ＝ zero-Semiring R
  left-zero-law-mul-Semiring = pr1 (pr2 (pr2 R))

  right-zero-law-mul-Semiring :
    (x : type-Semiring R) → mul-Semiring x (zero-Semiring R) ＝ zero-Semiring R
  right-zero-law-mul-Semiring = pr2 (pr2 (pr2 R))
```

### Multiplicative units in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-unital-Semiring : is-unital (mul-Semiring R)
  is-unital-Semiring = pr1 (pr2 (pr1 (pr2 R)))

  multiplicative-monoid-Semiring : Monoid l
  pr1 multiplicative-monoid-Semiring = multiplicative-semigroup-Semiring R
  pr2 multiplicative-monoid-Semiring = is-unital-Semiring

  one-Semiring : type-Semiring R
  one-Semiring = unit-Monoid multiplicative-monoid-Semiring

  left-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R one-Semiring x) x
  left-unit-law-mul-Semiring =
    left-unit-law-mul-Monoid multiplicative-monoid-Semiring

  right-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R x one-Semiring) x
  right-unit-law-mul-Semiring =
    right-unit-law-mul-Monoid multiplicative-monoid-Semiring
```

### Scalar multiplication of semiring elements by natural numbers

```agda
module _
  {l : Level} (R : Semiring l)
  where

  mul-nat-scalar-Semiring : ℕ → type-Semiring R → type-Semiring R
  mul-nat-scalar-Semiring zero-ℕ x = zero-Semiring R
  mul-nat-scalar-Semiring (succ-ℕ n) x =
    add-Semiring R (mul-nat-scalar-Semiring n x) x

  ap-mul-nat-scalar-Semiring :
    {m n : ℕ} {x y : type-Semiring R} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Semiring m x ＝ mul-nat-scalar-Semiring n y
  ap-mul-nat-scalar-Semiring p q = ap-binary mul-nat-scalar-Semiring p q

  left-zero-law-mul-nat-scalar-Semiring :
    (x : type-Semiring R) → mul-nat-scalar-Semiring 0 x ＝ zero-Semiring R
  left-zero-law-mul-nat-scalar-Semiring x = refl

  right-zero-law-mul-nat-scalar-Semiring :
    (n : ℕ) → mul-nat-scalar-Semiring n (zero-Semiring R) ＝ zero-Semiring R
  right-zero-law-mul-nat-scalar-Semiring zero-ℕ = refl
  right-zero-law-mul-nat-scalar-Semiring (succ-ℕ n) =
    ( right-unit-law-add-Semiring R _) ∙
    ( right-zero-law-mul-nat-scalar-Semiring n)

  left-unit-law-mul-nat-scalar-Semiring :
    (x : type-Semiring R) → mul-nat-scalar-Semiring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Semiring x = left-unit-law-add-Semiring R x

  left-nat-scalar-law-mul-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-Semiring R (mul-nat-scalar-Semiring n x) y ＝
    mul-nat-scalar-Semiring n (mul-Semiring R x y)
  left-nat-scalar-law-mul-Semiring zero-ℕ x y =
    left-zero-law-mul-Semiring R y
  left-nat-scalar-law-mul-Semiring (succ-ℕ n) x y =
    ( right-distributive-mul-add-Semiring R
      ( mul-nat-scalar-Semiring n x)
      ( x)
      ( y)) ∙
    ( ap
      ( add-Semiring' R (mul-Semiring R x y))
      ( left-nat-scalar-law-mul-Semiring n x y))

  right-nat-scalar-law-mul-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-Semiring R x (mul-nat-scalar-Semiring n y) ＝
    mul-nat-scalar-Semiring n (mul-Semiring R x y)
  right-nat-scalar-law-mul-Semiring zero-ℕ x y =
    right-zero-law-mul-Semiring R x
  right-nat-scalar-law-mul-Semiring (succ-ℕ n) x y =
    ( left-distributive-mul-add-Semiring R x
      ( mul-nat-scalar-Semiring n y)
      ( y)) ∙
    ( ap
      ( add-Semiring' R (mul-Semiring R x y))
      ( right-nat-scalar-law-mul-Semiring n x y))

  left-distributive-mul-nat-scalar-add-Semiring :
    (n : ℕ) (x y : type-Semiring R) →
    mul-nat-scalar-Semiring n (add-Semiring R x y) ＝
    add-Semiring R (mul-nat-scalar-Semiring n x) (mul-nat-scalar-Semiring n y)
  left-distributive-mul-nat-scalar-add-Semiring zero-ℕ x y =
    inv (left-unit-law-add-Semiring R (zero-Semiring R))
  left-distributive-mul-nat-scalar-add-Semiring (succ-ℕ n) x y =
    ( ap
      ( add-Semiring' R (add-Semiring R x y))
      ( left-distributive-mul-nat-scalar-add-Semiring n x y)) ∙
    ( interchange-add-add-Semiring R
      ( mul-nat-scalar-Semiring n x)
      ( mul-nat-scalar-Semiring n y)
      ( x)
      ( y))

  right-distributive-mul-nat-scalar-add-Semiring :
    (m n : ℕ) (x : type-Semiring R) →
    mul-nat-scalar-Semiring (m +ℕ n) x ＝
    add-Semiring R (mul-nat-scalar-Semiring m x) (mul-nat-scalar-Semiring n x)
  right-distributive-mul-nat-scalar-add-Semiring m zero-ℕ x =
    inv (right-unit-law-add-Semiring R (mul-nat-scalar-Semiring m x))
  right-distributive-mul-nat-scalar-add-Semiring m (succ-ℕ n) x =
    ( ap
      ( add-Semiring' R x)
      ( right-distributive-mul-nat-scalar-add-Semiring m n x)) ∙
    ( associative-add-Semiring R
      ( mul-nat-scalar-Semiring m x)
      ( mul-nat-scalar-Semiring n x) x)
```
