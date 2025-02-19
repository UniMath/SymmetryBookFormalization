# Powers of elements in commutative semirings

```agda
module commutative-algebra.powers-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.homomorphisms-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.powers-of-elements-semirings
```

</details>

## Idea

The **power operation** on a commutative semiring is the map `n x ↦ xⁿ`, which
is defined by iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) →
  ℕ → type-Commutative-Semiring A → type-Commutative-Semiring A
power-Commutative-Semiring A = power-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  power-one-Commutative-Semiring :
    (n : ℕ) →
    power-Commutative-Semiring A n (one-Commutative-Semiring A) ＝
    one-Commutative-Semiring A
  power-one-Commutative-Semiring =
    power-one-Semiring (semiring-Commutative-Semiring A)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  power-succ-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A) →
    power-Commutative-Semiring A (succ-ℕ n) x ＝
    mul-Commutative-Semiring A (power-Commutative-Semiring A n x) x
  power-succ-Commutative-Semiring =
    power-succ-Semiring (semiring-Commutative-Semiring A)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  power-succ-Commutative-Semiring' :
    (n : ℕ) (x : type-Commutative-Semiring A) →
    power-Commutative-Semiring A (succ-ℕ n) x ＝
    mul-Commutative-Semiring A x (power-Commutative-Semiring A n x)
  power-succ-Commutative-Semiring' =
    power-succ-Semiring' (semiring-Commutative-Semiring A)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  distributive-power-add-Commutative-Semiring :
    (m n : ℕ) {x : type-Commutative-Semiring A} →
    power-Commutative-Semiring A (m +ℕ n) x ＝
    mul-Commutative-Semiring A
      ( power-Commutative-Semiring A m x)
      ( power-Commutative-Semiring A n x)
  distributive-power-add-Commutative-Semiring =
    distributive-power-add-Semiring (semiring-Commutative-Semiring A)
```

### Powers distribute over products

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  distributive-power-mul-Commutative-Semiring :
    (n : ℕ) (x y : type-Commutative-Semiring A) →
    power-Commutative-Semiring A n (mul-Commutative-Semiring A x y) ＝
    mul-Commutative-Semiring A
      ( power-Commutative-Semiring A n x)
      ( power-Commutative-Semiring A n y)
  distributive-power-mul-Commutative-Semiring n x y =
    distributive-power-mul-Semiring
      ( semiring-Commutative-Semiring A)
      ( n)
      ( commutative-mul-Commutative-Semiring A x y)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  power-mul-Commutative-Semiring :
    (m n : ℕ) {x : type-Commutative-Semiring A} →
    power-Commutative-Semiring A (m *ℕ n) x ＝
    power-Commutative-Semiring A n (power-Commutative-Semiring A m x)
  power-mul-Commutative-Semiring =
    power-mul-Semiring (semiring-Commutative-Semiring A)
```

### Homomorphisms of semirings preserve powers

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Semiring l1) (B : Commutative-Semiring l2)
  (f : hom-Commutative-Semiring A B)
  where

  preserves-powers-hom-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A) →
    map-hom-Commutative-Semiring A B f (power-Commutative-Semiring A n x) ＝
    power-Commutative-Semiring B n (map-hom-Commutative-Semiring A B f x)
  preserves-powers-hom-Commutative-Semiring =
    preserves-powers-hom-Semiring
      ( semiring-Commutative-Semiring A)
      ( semiring-Commutative-Semiring B)
      ( f)
```
