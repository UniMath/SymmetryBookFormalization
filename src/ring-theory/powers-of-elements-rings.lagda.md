# Powers of elements in rings

```agda
module ring-theory.powers-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import ring-theory.central-elements-rings
open import ring-theory.powers-of-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

The power operation on a ring is the map `n x ↦ xⁿ`, which is defined by
iteratively multiplying `x` with itself `n` times.

## Definition

```agda
power-Ring : {l : Level} (R : Ring l) → ℕ → type-Ring R → type-Ring R
power-Ring R = power-Semiring (semiring-Ring R)
```

## Properties

### `0ⁿ⁺¹ ＝ 0`

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-zero-succ-Ring :
    (n : ℕ) → power-Ring R (succ-ℕ n) (zero-Ring R) ＝ zero-Ring R
  power-zero-succ-Ring = power-zero-succ-Semiring (semiring-Ring R)
```

### `xⁿ⁺¹ = xⁿx` and `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-succ-Ring :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R (succ-ℕ n) x ＝ mul-Ring R (power-Ring R n x) x
  power-succ-Ring = power-succ-Semiring (semiring-Ring R)

  power-succ-Ring' :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R (succ-ℕ n) x ＝ mul-Ring R x (power-Ring R n x)
  power-succ-Ring' = power-succ-Semiring' (semiring-Ring R)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  distributive-power-add-Ring :
    (m n : ℕ) {x : type-Ring R} →
    power-Ring R (m +ℕ n) x ＝
    mul-Ring R (power-Ring R m x) (power-Ring R n x)
  distributive-power-add-Ring =
    distributive-power-add-Semiring (semiring-Ring R)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-mul-Ring :
    (m n : ℕ) {x : type-Ring R} →
    power-Ring R (m *ℕ n) x ＝ power-Ring R n (power-Ring R m x)
  power-mul-Ring = power-mul-Semiring (semiring-Ring R)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (R : Ring l)
  where

  commute-powers-Ring' :
    (n : ℕ) {x y : type-Ring R} →
    ( mul-Ring R x y ＝ mul-Ring R y x) →
    ( mul-Ring R (power-Ring R n x) y) ＝
    ( mul-Ring R y (power-Ring R n x))
  commute-powers-Ring' = commute-powers-Semiring' (semiring-Ring R)

  commute-powers-Ring :
    (m n : ℕ) {x y : type-Ring R} → mul-Ring R x y ＝ mul-Ring R y x →
    ( mul-Ring R (power-Ring R m x) (power-Ring R n y)) ＝
    ( mul-Ring R (power-Ring R n y) (power-Ring R m x))
  commute-powers-Ring = commute-powers-Semiring (semiring-Ring R)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (R : Ring l)
  where

  distributive-power-mul-Ring :
    (n : ℕ) {x y : type-Ring R} → mul-Ring R x y ＝ mul-Ring R y x →
    power-Ring R n (mul-Ring R x y) ＝
    mul-Ring R (power-Ring R n x) (power-Ring R n y)
  distributive-power-mul-Ring =
    distributive-power-mul-Semiring (semiring-Ring R)
```

### `(-x)ⁿ = (-1)ⁿxⁿ`

```agda
module _
  {l : Level} (R : Ring l)
  where

  power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    power-Ring R n (neg-Ring R x) ＝
    mul-Ring R (power-Ring R n (neg-one-Ring R)) (power-Ring R n x)
  power-neg-Ring n x =
    ( ap (power-Ring R n) (inv (mul-neg-one-Ring R x))) ∙
    ( distributive-power-mul-Ring R n (is-central-element-neg-one-Ring R x))

  even-power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    is-even-ℕ n → power-Ring R n (neg-Ring R x) ＝ power-Ring R n x
  even-power-neg-Ring zero-ℕ x H = refl
  even-power-neg-Ring (succ-ℕ zero-ℕ) x H = ex-falso (is-odd-one-ℕ H)
  even-power-neg-Ring (succ-ℕ (succ-ℕ n)) x H =
    ( right-negative-law-mul-Ring R
      ( power-Ring R (succ-ℕ n) (neg-Ring R x))
      ( x)) ∙
    ( ( ap
        ( neg-Ring R)
        ( ( ap
            ( mul-Ring' R x)
            ( ( power-succ-Ring R n (neg-Ring R x)) ∙
              ( ( right-negative-law-mul-Ring R
                  ( power-Ring R n (neg-Ring R x))
                  ( x)) ∙
                ( ap
                  ( neg-Ring R)
                  ( ( ap
                      ( mul-Ring' R x)
                      ( even-power-neg-Ring n x
                        ( is-even-is-even-succ-succ-ℕ n H))) ∙
                    ( inv (power-succ-Ring R n x))))))) ∙
          ( left-negative-law-mul-Ring R (power-Ring R (succ-ℕ n) x) x))) ∙
      ( neg-neg-Ring R (power-Ring R (succ-ℕ (succ-ℕ n)) x)))

  odd-power-neg-Ring :
    (n : ℕ) (x : type-Ring R) →
    is-odd-ℕ n → power-Ring R n (neg-Ring R x) ＝ neg-Ring R (power-Ring R n x)
  odd-power-neg-Ring zero-ℕ x H = ex-falso (H is-even-zero-ℕ)
  odd-power-neg-Ring (succ-ℕ zero-ℕ) x H = refl
  odd-power-neg-Ring (succ-ℕ (succ-ℕ n)) x H =
    ( right-negative-law-mul-Ring R
      ( power-Ring R (succ-ℕ n) (neg-Ring R x))
      ( x)) ∙
    ( ap
      ( neg-Ring R ∘ mul-Ring' R x)
      ( ( power-succ-Ring R n (neg-Ring R x)) ∙
        ( ( right-negative-law-mul-Ring R
            ( power-Ring R n (neg-Ring R x))
            ( x)) ∙
          ( ( ap
              ( neg-Ring R)
              ( ( ap
                  ( mul-Ring' R x)
                  ( odd-power-neg-Ring n x
                    ( is-odd-is-odd-succ-succ-ℕ n H))) ∙
                ( ( left-negative-law-mul-Ring R (power-Ring R n x) x) ∙
                  ( ap (neg-Ring R) (inv (power-succ-Ring R n x)))))) ∙
            ( neg-neg-Ring R (power-Ring R (succ-ℕ n) x))))))
```
