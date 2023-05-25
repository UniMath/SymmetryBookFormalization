# Finite rings

```agda
module finite-algebra.finite-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers

open import ring-theory.rings
open import ring-theory.semirings

open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.sets
open import foundation.identity-types
open import foundation.equivalences
open import foundation.binary-equivalences
open import foundation.binary-embeddings
open import foundation.embeddings
open import foundation.injective-maps
open import foundation.unital-binary-operations
open import foundation.involutions

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import lists.lists
open import lists.concatenation-lists

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite ring** is a ring where the underlying type is finite.

## Definitions

### Finite Rings

```agda
Ring-𝔽 : (l1 : Level) → UU (lsuc l1)
Ring-𝔽 l1 = Σ (Ring l1) (λ R → is-finite (type-Ring R))

module _
  {l : Level} (R : Ring-𝔽 l)
  where

  ring-Ring-𝔽 : Ring l
  ring-Ring-𝔽 = pr1 R

  ab-Ring-𝔽 : Ab l
  ab-Ring-𝔽 = ab-Ring ring-Ring-𝔽

  group-Ring-𝔽 : Group l
  group-Ring-𝔽 = group-Ring ring-Ring-𝔽

  additive-commutative-monoid-Ring-𝔽 : Commutative-Monoid l
  additive-commutative-monoid-Ring-𝔽 =
    additive-commutative-monoid-Ring ring-Ring-𝔽

  additive-monoid-Ring-𝔽 : Monoid l
  additive-monoid-Ring-𝔽 = additive-monoid-Ring ring-Ring-𝔽

  additive-semigroup-Ring-𝔽 : Semigroup l
  additive-semigroup-Ring-𝔽 = additive-semigroup-Ring ring-Ring-𝔽

  set-Ring-𝔽 : Set l
  set-Ring-𝔽 = set-Ring ring-Ring-𝔽

  type-Ring-𝔽 : UU l
  type-Ring-𝔽 = type-Ring ring-Ring-𝔽

  is-finite-type-Ring-𝔽 : is-finite (type-Ring-𝔽)
  is-finite-type-Ring-𝔽 = pr2 R

  finite-type-Ring-𝔽 : 𝔽 l
  pr1 finite-type-Ring-𝔽 = type-Ring-𝔽
  pr2 finite-type-Ring-𝔽 = is-finite-type-Ring-𝔽

  is-set-type-Ring-𝔽 : is-set type-Ring-𝔽
  is-set-type-Ring-𝔽 = is-set-type-Ring ring-Ring-𝔽
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-associative-add-Ring-𝔽 : has-associative-mul-Set (set-Ring-𝔽 R)
  has-associative-add-Ring-𝔽 = has-associative-add-Ring (ring-Ring-𝔽 R)

  add-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  add-Ring-𝔽 = add-Ring (ring-Ring-𝔽 R)

  add-Ring-𝔽' : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  add-Ring-𝔽' = add-Ring' (ring-Ring-𝔽 R)

  ap-add-Ring-𝔽 :
    {x y x' y' : type-Ring-𝔽 R} →
    Id x x' → Id y y' → Id (add-Ring-𝔽 x y) (add-Ring-𝔽 x' y')
  ap-add-Ring-𝔽 = ap-add-Ring (ring-Ring-𝔽 R)

  associative-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    Id (add-Ring-𝔽 (add-Ring-𝔽 x y) z) (add-Ring-𝔽 x (add-Ring-𝔽 y z))
  associative-add-Ring-𝔽 = associative-add-Ring (ring-Ring-𝔽 R)

  is-group-additive-semigroup-Ring-𝔽 : is-group (additive-semigroup-Ring-𝔽 R)
  is-group-additive-semigroup-Ring-𝔽 =
    is-group-additive-semigroup-Ring (ring-Ring-𝔽 R)

  commutative-add-Ring-𝔽 : (x y : type-Ring-𝔽 R) → Id (add-Ring-𝔽 x y) (add-Ring-𝔽 y x)
  commutative-add-Ring-𝔽 = commutative-add-Ring (ring-Ring-𝔽 R)

  interchange-add-add-Ring-𝔽 :
    (x y x' y' : type-Ring-𝔽 R) →
    ( add-Ring-𝔽 (add-Ring-𝔽 x y) (add-Ring-𝔽 x' y')) ＝
    ( add-Ring-𝔽 (add-Ring-𝔽 x x') (add-Ring-𝔽 y y'))
  interchange-add-add-Ring-𝔽 =
    interchange-add-add-Ring (ring-Ring-𝔽 R)

  right-swap-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    add-Ring-𝔽 (add-Ring-𝔽 x y) z ＝ add-Ring-𝔽 (add-Ring-𝔽 x z) y
  right-swap-add-Ring-𝔽 = right-swap-add-Ring (ring-Ring-𝔽 R)

  left-swap-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    add-Ring-𝔽 x (add-Ring-𝔽 y z) ＝ add-Ring-𝔽 y (add-Ring-𝔽 x z)
  left-swap-add-Ring-𝔽 = left-swap-add-Ring (ring-Ring-𝔽 R)

  is-equiv-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-equiv (add-Ring-𝔽 x)
  is-equiv-add-Ring-𝔽 = is-equiv-add-Ring (ring-Ring-𝔽 R)

  is-equiv-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-equiv (add-Ring-𝔽' x)
  is-equiv-add-Ring-𝔽' = is-equiv-add-Ring' (ring-Ring-𝔽 R)

  is-binary-equiv-add-Ring-𝔽 : is-binary-equiv add-Ring-𝔽
  is-binary-equiv-add-Ring-𝔽 = is-binary-equiv-add-Ring (ring-Ring-𝔽 R)

  is-binary-emb-add-Ring-𝔽 : is-binary-emb add-Ring-𝔽
  is-binary-emb-add-Ring-𝔽 = is-binary-emb-add-Ring (ring-Ring-𝔽 R)

  is-emb-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-emb (add-Ring-𝔽 x)
  is-emb-add-Ring-𝔽 = is-emb-add-Ring (ring-Ring-𝔽 R)

  is-emb-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-emb (add-Ring-𝔽' x)
  is-emb-add-Ring-𝔽' = is-emb-add-Ring' (ring-Ring-𝔽 R)

  is-injective-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → is-injective (add-Ring-𝔽 x)
  is-injective-add-Ring-𝔽 = is-injective-add-Ring (ring-Ring-𝔽 R)

  is-injective-add-Ring-𝔽' : (x : type-Ring-𝔽 R) → is-injective (add-Ring-𝔽' x)
  is-injective-add-Ring-𝔽' = is-injective-add-Ring' (ring-Ring-𝔽 R)
```

### The zero element of a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-zero-Ring-𝔽 : is-unital (add-Ring-𝔽 R)
  has-zero-Ring-𝔽 = has-zero-Ring (ring-Ring-𝔽 R)

  zero-Ring-𝔽 : type-Ring-𝔽 R
  zero-Ring-𝔽 = zero-Ring (ring-Ring-𝔽 R)

  is-zero-Ring-𝔽 : type-Ring-𝔽 R → UU l
  is-zero-Ring-𝔽 = is-zero-Ring (ring-Ring-𝔽 R)

  is-nonzero-Ring-𝔽 : type-Ring-𝔽 R → UU l
  is-nonzero-Ring-𝔽 = is-nonzero-Ring (ring-Ring-𝔽 R)

  is-zero-finite-ring-Prop : type-Ring-𝔽 R → Prop l
  is-zero-finite-ring-Prop = is-zero-ring-Prop (ring-Ring-𝔽 R)

  is-nonzero-finite-ring-Prop : type-Ring-𝔽 R → Prop l
  is-nonzero-finite-ring-Prop = is-nonzero-ring-Prop (ring-Ring-𝔽 R)

  left-unit-law-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R zero-Ring-𝔽 x) x
  left-unit-law-add-Ring-𝔽 = left-unit-law-add-Ring (ring-Ring-𝔽 R)

  right-unit-law-add-Ring-𝔽 : (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R x zero-Ring-𝔽) x
  right-unit-law-add-Ring-𝔽 = right-unit-law-add-Ring (ring-Ring-𝔽 R)
```

### Additive inverses in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-negatives-Ring-𝔽 : is-group' (additive-semigroup-Ring-𝔽 R) (has-zero-Ring-𝔽 R)
  has-negatives-Ring-𝔽 = has-negatives-Ring (ring-Ring-𝔽 R)

  neg-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R
  neg-Ring-𝔽 = neg-Ring (ring-Ring-𝔽 R)

  left-inverse-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R (neg-Ring-𝔽 x) x) (zero-Ring-𝔽 R)
  left-inverse-law-add-Ring-𝔽 = left-inverse-law-add-Ring (ring-Ring-𝔽 R)

  right-inverse-law-add-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (add-Ring-𝔽 R x (neg-Ring-𝔽 x)) (zero-Ring-𝔽 R)
  right-inverse-law-add-Ring-𝔽 = right-inverse-law-add-Ring (ring-Ring-𝔽 R)

  neg-neg-Ring-𝔽 : (x : type-Ring-𝔽 R) → neg-Ring-𝔽 (neg-Ring-𝔽 x) ＝ x
  neg-neg-Ring-𝔽 = neg-neg-Ring (ring-Ring-𝔽 R)

  distributive-neg-add-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    neg-Ring-𝔽 (add-Ring-𝔽 R x y) ＝ add-Ring-𝔽 R (neg-Ring-𝔽 x) (neg-Ring-𝔽 y)
  distributive-neg-add-Ring-𝔽 = distributive-neg-add-Ring (ring-Ring-𝔽 R)
```

### Multiplication in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-associative-mul-Ring-𝔽 : has-associative-mul-Set (set-Ring-𝔽 R)
  has-associative-mul-Ring-𝔽 = has-associative-mul-Ring (ring-Ring-𝔽 R)

  mul-Ring-𝔽 : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-Ring-𝔽 = mul-Ring (ring-Ring-𝔽 R)

  mul-Ring-𝔽' : type-Ring-𝔽 R → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-Ring-𝔽' = mul-Ring' (ring-Ring-𝔽 R)

  ap-mul-Ring-𝔽 :
    {x x' y y' : type-Ring-𝔽 R} (p : Id x x') (q : Id y y') →
    Id (mul-Ring-𝔽 x y) (mul-Ring-𝔽 x' y')
  ap-mul-Ring-𝔽 = ap-mul-Ring (ring-Ring-𝔽 R)

  associative-mul-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    Id (mul-Ring-𝔽 (mul-Ring-𝔽 x y) z) (mul-Ring-𝔽 x (mul-Ring-𝔽 y z))
  associative-mul-Ring-𝔽 = associative-mul-Ring (ring-Ring-𝔽 R)

  multiplicative-semigroup-Ring-𝔽 : Semigroup l
  multiplicative-semigroup-Ring-𝔽 =
    multiplicative-semigroup-Ring (ring-Ring-𝔽 R)

  left-distributive-mul-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    mul-Ring-𝔽 x (add-Ring-𝔽 R y z) ＝ add-Ring-𝔽 R (mul-Ring-𝔽 x y) (mul-Ring-𝔽 x z)
  left-distributive-mul-add-Ring-𝔽 =
    left-distributive-mul-add-Ring (ring-Ring-𝔽 R)

  right-distributive-mul-add-Ring-𝔽 :
    (x y z : type-Ring-𝔽 R) →
    mul-Ring-𝔽 (add-Ring-𝔽 R x y) z ＝ add-Ring-𝔽 R (mul-Ring-𝔽 x z) (mul-Ring-𝔽 y z)
  right-distributive-mul-add-Ring-𝔽 =
    right-distributive-mul-add-Ring (ring-Ring-𝔽 R)
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  is-unital-Ring-𝔽 : is-unital (mul-Ring-𝔽 R)
  is-unital-Ring-𝔽 = is-unital-Ring (ring-Ring-𝔽 R)

  multiplicative-monoid-Ring-𝔽 : Monoid l
  multiplicative-monoid-Ring-𝔽 = multiplicative-monoid-Ring (ring-Ring-𝔽 R)

  one-Ring-𝔽 : type-Ring-𝔽 R
  one-Ring-𝔽 = one-Ring (ring-Ring-𝔽 R)

  left-unit-law-mul-Ring-𝔽 : (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R one-Ring-𝔽 x) x
  left-unit-law-mul-Ring-𝔽 = left-unit-law-mul-Ring (ring-Ring-𝔽 R)

  right-unit-law-mul-Ring-𝔽 : (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R x one-Ring-𝔽) x
  right-unit-law-mul-Ring-𝔽 = right-unit-law-mul-Ring (ring-Ring-𝔽 R)
```

### The zero laws for multiplication of a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  left-zero-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R (zero-Ring-𝔽 R) x) (zero-Ring-𝔽 R)
  left-zero-law-mul-Ring-𝔽 =
    left-zero-law-mul-Ring (ring-Ring-𝔽 R)

  right-zero-law-mul-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → Id (mul-Ring-𝔽 R x (zero-Ring-𝔽 R)) (zero-Ring-𝔽 R)
  right-zero-law-mul-Ring-𝔽 =
    right-zero-law-mul-Ring (ring-Ring-𝔽 R)
```

### Rings are semirings

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  has-mul-Ring-𝔽 :
    has-mul-Commutative-Monoid (additive-commutative-monoid-Ring-𝔽 R)
  has-mul-Ring-𝔽 = has-mul-Ring (ring-Ring-𝔽 R)

  zero-laws-mul-Ring-𝔽 :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-Ring-𝔽 R)
      ( has-mul-Ring-𝔽)
  zero-laws-mul-Ring-𝔽 = zero-laws-mul-Ring (ring-Ring-𝔽 R)

  semiring-Ring-𝔽 : Semiring l
  semiring-Ring-𝔽 = semiring-Ring (ring-Ring-𝔽 R)
```

### Computing multiplication with minus one in a ring

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  neg-one-Ring-𝔽 : type-Ring-𝔽 R
  neg-one-Ring-𝔽 = neg-one-Ring (ring-Ring-𝔽 R)

  mul-neg-one-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-Ring-𝔽 R neg-one-Ring-𝔽 x ＝ neg-Ring-𝔽 R x
  mul-neg-one-Ring-𝔽 =
    mul-neg-one-Ring (ring-Ring-𝔽 R)

  mul-neg-one-Ring-𝔽' :
    (x : type-Ring-𝔽 R) → mul-Ring-𝔽 R x neg-one-Ring-𝔽 ＝ neg-Ring-𝔽 R x
  mul-neg-one-Ring-𝔽' =
    mul-neg-one-Ring' (ring-Ring-𝔽 R)

  is-involution-mul-neg-one-Ring-𝔽 :
    is-involution (mul-Ring-𝔽 R neg-one-Ring-𝔽)
  is-involution-mul-neg-one-Ring-𝔽 =
    is-involution-mul-neg-one-Ring (ring-Ring-𝔽 R)

  is-involution-mul-neg-one-Ring-𝔽' :
    is-involution (mul-Ring-𝔽' R neg-one-Ring-𝔽)
  is-involution-mul-neg-one-Ring-𝔽' =
    is-involution-mul-neg-one-Ring' (ring-Ring-𝔽 R)
```

### Left and right negative laws for multiplication

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  left-negative-law-mul-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (neg-Ring-𝔽 R x) y ＝ neg-Ring-𝔽 R (mul-Ring-𝔽 R x y)
  left-negative-law-mul-Ring-𝔽 =
    left-negative-law-mul-Ring (ring-Ring-𝔽 R)

  right-negative-law-mul-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R x (neg-Ring-𝔽 R y) ＝ neg-Ring-𝔽 R (mul-Ring-𝔽 R x y)
  right-negative-law-mul-Ring-𝔽 =
    right-negative-law-mul-Ring (ring-Ring-𝔽 R)

  mul-neg-Ring-𝔽 :
    (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (neg-Ring-𝔽 R x) (neg-Ring-𝔽 R y) ＝ mul-Ring-𝔽 R x y
  mul-neg-Ring-𝔽 =
    mul-neg-Ring (ring-Ring-𝔽 R)
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  mul-nat-scalar-Ring-𝔽 : ℕ → type-Ring-𝔽 R → type-Ring-𝔽 R
  mul-nat-scalar-Ring-𝔽 = mul-nat-scalar-Ring (ring-Ring-𝔽 R)

  ap-mul-nat-scalar-Ring-𝔽 :
    {m n : ℕ} {x y : type-Ring-𝔽 R} →
    (m ＝ n) → (x ＝ y) → mul-nat-scalar-Ring-𝔽 m x ＝ mul-nat-scalar-Ring-𝔽 n y
  ap-mul-nat-scalar-Ring-𝔽 = ap-mul-nat-scalar-Ring (ring-Ring-𝔽 R)

  left-zero-law-mul-nat-scalar-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-nat-scalar-Ring-𝔽 0 x ＝ zero-Ring-𝔽 R
  left-zero-law-mul-nat-scalar-Ring-𝔽 =
    left-zero-law-mul-nat-scalar-Ring (ring-Ring-𝔽 R)

  right-zero-law-mul-nat-scalar-Ring-𝔽 :
    (n : ℕ) → mul-nat-scalar-Ring-𝔽 n (zero-Ring-𝔽 R) ＝ zero-Ring-𝔽 R
  right-zero-law-mul-nat-scalar-Ring-𝔽 =
    right-zero-law-mul-nat-scalar-Ring (ring-Ring-𝔽 R)

  left-unit-law-mul-nat-scalar-Ring-𝔽 :
    (x : type-Ring-𝔽 R) → mul-nat-scalar-Ring-𝔽 1 x ＝ x
  left-unit-law-mul-nat-scalar-Ring-𝔽 =
    left-unit-law-mul-nat-scalar-Ring (ring-Ring-𝔽 R)

  left-nat-scalar-law-mul-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 n x) y ＝
    mul-nat-scalar-Ring-𝔽 n (mul-Ring-𝔽 R x y)
  left-nat-scalar-law-mul-Ring-𝔽 =
    left-nat-scalar-law-mul-Ring (ring-Ring-𝔽 R)

  right-nat-scalar-law-mul-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-Ring-𝔽 R x (mul-nat-scalar-Ring-𝔽 n y) ＝
    mul-nat-scalar-Ring-𝔽 n (mul-Ring-𝔽 R x y)
  right-nat-scalar-law-mul-Ring-𝔽 =
    right-nat-scalar-law-mul-Ring (ring-Ring-𝔽 R)

  left-distributive-mul-nat-scalar-add-Ring-𝔽 :
    (n : ℕ) (x y : type-Ring-𝔽 R) →
    mul-nat-scalar-Ring-𝔽 n (add-Ring-𝔽 R x y) ＝
    add-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 n x) (mul-nat-scalar-Ring-𝔽 n y)
  left-distributive-mul-nat-scalar-add-Ring-𝔽 =
    left-distributive-mul-nat-scalar-add-Ring (ring-Ring-𝔽 R)

  right-distributive-mul-nat-scalar-add-Ring-𝔽 :
    (m n : ℕ) (x : type-Ring-𝔽 R) →
    mul-nat-scalar-Ring-𝔽 (m +ℕ n) x ＝
    add-Ring-𝔽 R (mul-nat-scalar-Ring-𝔽 m x) (mul-nat-scalar-Ring-𝔽 n x)
  right-distributive-mul-nat-scalar-add-Ring-𝔽 =
    right-distributive-mul-nat-scalar-add-Ring (ring-Ring-𝔽 R)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (R : Ring-𝔽 l)
  where

  add-list-Ring-𝔽 : list (type-Ring-𝔽 R) → type-Ring-𝔽 R
  add-list-Ring-𝔽 = add-list-Ring (ring-Ring-𝔽 R)

  preserves-concat-add-list-Ring-𝔽 :
    (l1 l2 : list (type-Ring-𝔽 R)) →
    Id ( add-list-Ring-𝔽 (concat-list l1 l2))
       ( add-Ring-𝔽 R (add-list-Ring-𝔽 l1) (add-list-Ring-𝔽 l2))
  preserves-concat-add-list-Ring-𝔽 =
    preserves-concat-add-list-Ring (ring-Ring-𝔽 R)
```

### Equip a finite type with a structure of finite ring

```agda
structure-ring-𝔽 :
  {l1 : Level} → 𝔽 l1 → UU l1
structure-ring-𝔽 X = structure-ring (type-𝔽 X)

compute-structure-ring-𝔽 :
  {l1 : Level} → (X : 𝔽 l1) → structure-ring-𝔽 X →  Ring-𝔽 l1
pr1 (compute-structure-ring-𝔽 X r) = compute-structure-ring (type-𝔽 X) r
pr2 (compute-structure-ring-𝔽 X r) = is-finite-type-𝔽 X
```
