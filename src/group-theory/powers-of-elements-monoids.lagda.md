# Powers of elements in monoids

```agda
module group-theory.powers-of-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.monoids
```

</details>

## Idea

The {{#concept "power operation" Disambiguation="monoid" Agda=power-Monoid}} on a [monoid](group-theory.monoids.md) is the map
`n x ↦ xⁿ`, which is defined by [iteratively](foundation.iterating-functions.md)
multiplying `x` with itself `n` times.

We define the power operation such that the following equalities hold by definition:

```text
  x⁰ ≐ 1
  x¹ ≐ x
  xⁿ⁺² ≐ xⁿ⁺¹ · x.
```

This setup requires one extra step for the most basic properties, but it avoids having a superficial factor of the multiplicative unit in its definition for `n ≥ 1`.

## Definitions

### Powers of elements of monoids

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-Monoid : ℕ → type-Monoid M → type-Monoid M
  power-Monoid zero-ℕ x = unit-Monoid M
  power-Monoid (succ-ℕ zero-ℕ) x = x
  power-Monoid (succ-ℕ (succ-ℕ n)) x =
    mul-Monoid M (power-Monoid (succ-ℕ n) x) x
```

### The predicate of being a power of an element of a monoid

We say that an element `y` **is a power** of an element `x` if there
[exists](foundation.existential-quantification.md) a number `n` such that
`xⁿ ＝ y`.

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-power-of-element-prop-Monoid : (x y : type-Monoid M) → Prop l
  is-power-of-element-prop-Monoid x y =
    exists-structure-Prop ℕ (λ n → power-Monoid M n x ＝ y)

  is-power-of-element-Monoid : (x y : type-Monoid M) → UU l
  is-power-of-element-Monoid x y =
    type-Prop (is-power-of-element-prop-Monoid x y)

  is-prop-is-power-of-element-Monoid :
    (x y : type-Monoid M) → is-prop (is-power-of-element-Monoid x y)
  is-prop-is-power-of-element-Monoid x y =
    is-prop-type-Prop (is-power-of-element-prop-Monoid x y)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-unit-Monoid :
    (n : ℕ) →
    power-Monoid M n (unit-Monoid M) ＝ unit-Monoid M
  power-unit-Monoid zero-ℕ = refl
  power-unit-Monoid (succ-ℕ zero-ℕ) = refl
  power-unit-Monoid (succ-ℕ (succ-ℕ n)) =
    right-unit-law-mul-Monoid M _ ∙ power-unit-Monoid (succ-ℕ n)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-succ-Monoid :
    (n : ℕ) (x : type-Monoid M) →
    power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M (power-Monoid M n x) x
  power-succ-Monoid zero-ℕ x = inv (left-unit-law-mul-Monoid M x)
  power-succ-Monoid (succ-ℕ n) x = refl
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-succ-Monoid' :
    (n : ℕ) (x : type-Monoid M) →
    power-Monoid M (succ-ℕ n) x ＝ mul-Monoid M x (power-Monoid M n x)
  power-succ-Monoid' zero-ℕ x = inv (right-unit-law-mul-Monoid M x)
  power-succ-Monoid' (succ-ℕ zero-ℕ) x = refl
  power-succ-Monoid' (succ-ℕ (succ-ℕ n)) x =
    ( ap (mul-Monoid' M x) (power-succ-Monoid' (succ-ℕ n) x)) ∙
    ( associative-mul-Monoid M x (power-Monoid M (succ-ℕ n) x) x)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  distributive-power-add-Monoid :
    (m n : ℕ) {x : type-Monoid M} →
    power-Monoid M (m +ℕ n) x ＝
    mul-Monoid M (power-Monoid M m x) (power-Monoid M n x)
  distributive-power-add-Monoid m zero-ℕ {x} =
    inv
      ( right-unit-law-mul-Monoid M
        ( power-Monoid M m x))
  distributive-power-add-Monoid m (succ-ℕ n) {x} =
    ( power-succ-Monoid M (m +ℕ n) x) ∙
    ( ap (mul-Monoid' M x) (distributive-power-add-Monoid m n)) ∙
    ( associative-mul-Monoid M
      ( power-Monoid M m x)
      ( power-Monoid M n x)
      ( x)) ∙
    ( ap
      ( mul-Monoid M (power-Monoid M m x))
      ( inv (power-succ-Monoid M n x)))
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  commute-powers-Monoid' :
    (n : ℕ) {x y : type-Monoid M} →
    ( mul-Monoid M x y ＝ mul-Monoid M y x) →
    ( mul-Monoid M (power-Monoid M n x) y) ＝
    ( mul-Monoid M y (power-Monoid M n x))
  commute-powers-Monoid' zero-ℕ H =
    left-unit-law-mul-Monoid M _ ∙ inv (right-unit-law-mul-Monoid M _)
  commute-powers-Monoid' (succ-ℕ zero-ℕ) {x} {y} H = H
  commute-powers-Monoid' (succ-ℕ (succ-ℕ n)) {x} {y} H =
    ( associative-mul-Monoid M (power-Monoid M (succ-ℕ n) x) x y) ∙
    ( ap (mul-Monoid M (power-Monoid M (succ-ℕ n) x)) H) ∙
    ( inv (associative-mul-Monoid M (power-Monoid M (succ-ℕ n) x) y x)) ∙
    ( ap (mul-Monoid' M x) (commute-powers-Monoid' (succ-ℕ n) H)) ∙
    ( associative-mul-Monoid M y (power-Monoid M (succ-ℕ n) x) x)

  commute-powers-Monoid :
    (m n : ℕ) {x y : type-Monoid M} →
    ( mul-Monoid M x y ＝ mul-Monoid M y x) →
    ( mul-Monoid M
      ( power-Monoid M m x)
      ( power-Monoid M n y)) ＝
    ( mul-Monoid M
      ( power-Monoid M n y)
      ( power-Monoid M m x))
  commute-powers-Monoid zero-ℕ zero-ℕ H = refl
  commute-powers-Monoid zero-ℕ (succ-ℕ n) H =
    ( left-unit-law-mul-Monoid M (power-Monoid M (succ-ℕ n) _)) ∙
    ( inv (right-unit-law-mul-Monoid M (power-Monoid M (succ-ℕ n) _)))
  commute-powers-Monoid (succ-ℕ m) zero-ℕ H =
    ( right-unit-law-mul-Monoid M (power-Monoid M (succ-ℕ m) _)) ∙
    ( inv (left-unit-law-mul-Monoid M (power-Monoid M (succ-ℕ m) _)))
  commute-powers-Monoid (succ-ℕ m) (succ-ℕ n) {x} {y} H =
    ( ap-mul-Monoid M (power-succ-Monoid M m x) (power-succ-Monoid M n y)) ∙
    ( associative-mul-Monoid M
      ( power-Monoid M m x)
      ( x)
      ( mul-Monoid M (power-Monoid M n y) y)) ∙
    ( ap
      ( mul-Monoid M (power-Monoid M m x))
      ( ( inv (associative-mul-Monoid M x (power-Monoid M n y) y)) ∙
        ( ap
          ( mul-Monoid' M y)
          ( inv (commute-powers-Monoid' n (inv H)))) ∙
        ( associative-mul-Monoid M (power-Monoid M n y) x y) ∙
        ( ap (mul-Monoid M (power-Monoid M n y)) H) ∙
        ( inv (associative-mul-Monoid M (power-Monoid M n y) y x)))) ∙
    ( inv
      ( associative-mul-Monoid M
        ( power-Monoid M m x)
        ( mul-Monoid M (power-Monoid M n y) y)
        ( x))) ∙
    ( ap
      ( mul-Monoid' M x)
      ( ( inv
          ( associative-mul-Monoid M
            ( power-Monoid M m x)
            ( power-Monoid M n y)
            ( y))) ∙
        ( ap
          ( mul-Monoid' M y)
          ( commute-powers-Monoid m n H)) ∙
        ( associative-mul-Monoid M
          ( power-Monoid M n y)
          ( power-Monoid M m x)
          ( y)) ∙
        ( ap
          ( mul-Monoid M (power-Monoid M n y))
          ( commute-powers-Monoid' m H)) ∙
        ( inv
          ( associative-mul-Monoid M
            ( power-Monoid M n y)
            ( y)
            ( power-Monoid M m x))) ∙
        ( ap
          ( mul-Monoid' M (power-Monoid M m x))
          ( inv (power-succ-Monoid M n y))))) ∙
      ( associative-mul-Monoid M
        ( power-Monoid M (succ-ℕ n) y)
        ( power-Monoid M m x)
        ( x)) ∙
      ( ap
        ( mul-Monoid M (power-Monoid M (succ-ℕ n) y))
        ( inv (power-succ-Monoid M m x)))
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  distributive-power-mul-Monoid :
    (n : ℕ) {x y : type-Monoid M} →
    (H : mul-Monoid M x y ＝ mul-Monoid M y x) →
    power-Monoid M n (mul-Monoid M x y) ＝
    mul-Monoid M (power-Monoid M n x) (power-Monoid M n y)
  distributive-power-mul-Monoid zero-ℕ H =
    inv (left-unit-law-mul-Monoid M (unit-Monoid M))
  distributive-power-mul-Monoid (succ-ℕ n) {x} {y} H =
    ( power-succ-Monoid M n (mul-Monoid M x y)) ∙
    ( ap
      ( mul-Monoid' M (mul-Monoid M x y))
      ( distributive-power-mul-Monoid n H)) ∙
    ( inv
      ( associative-mul-Monoid M
        ( mul-Monoid M (power-Monoid M n x) (power-Monoid M n y))
        ( x)
        ( y))) ∙
    ( ap
      ( mul-Monoid' M y)
      ( ( associative-mul-Monoid M
          ( power-Monoid M n x)
          ( power-Monoid M n y)
          ( x)) ∙
        ( ap
          ( mul-Monoid M (power-Monoid M n x))
          ( commute-powers-Monoid' M n (inv H))) ∙
        ( inv
          ( associative-mul-Monoid M
            ( power-Monoid M n x)
            ( x)
            ( power-Monoid M n y))))) ∙
    ( associative-mul-Monoid M
      ( mul-Monoid M (power-Monoid M n x) x)
      ( power-Monoid M n y)
      ( y)) ∙
    ( ap-mul-Monoid M
      ( inv (power-succ-Monoid M n x))
      ( inv (power-succ-Monoid M n y)))
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {l : Level} (M : Monoid l)
  where

  power-mul-Monoid :
    (m n : ℕ) {x : type-Monoid M} →
    power-Monoid M (m *ℕ n) x ＝
    power-Monoid M n (power-Monoid M m x)
  power-mul-Monoid zero-ℕ n {x} =
    inv (power-unit-Monoid M n)
  power-mul-Monoid (succ-ℕ zero-ℕ) n {x} =
    ap (λ t → power-Monoid M t x) (left-unit-law-add-ℕ n)
  power-mul-Monoid (succ-ℕ (succ-ℕ m)) n {x} =
    ( distributive-power-add-Monoid M (succ-ℕ m *ℕ n) n) ∙
    ( ap
      ( mul-Monoid' M (power-Monoid M n x))
      ( power-mul-Monoid (succ-ℕ m) n)) ∙
    ( inv
      ( distributive-power-mul-Monoid M n
        ( commute-powers-Monoid' M (succ-ℕ m) refl)))
```

### Monoid homomorphisms preserve powers

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  preserves-powers-hom-Monoid :
    (n : ℕ) (x : type-Monoid M) →
    map-hom-Monoid M N f (power-Monoid M n x) ＝
    power-Monoid N n (map-hom-Monoid M N f x)
  preserves-powers-hom-Monoid zero-ℕ x = preserves-unit-hom-Monoid M N f
  preserves-powers-hom-Monoid (succ-ℕ zero-ℕ) x = refl
  preserves-powers-hom-Monoid (succ-ℕ (succ-ℕ n)) x =
    ( preserves-mul-hom-Monoid M N f) ∙
    ( ap (mul-Monoid' N _) (preserves-powers-hom-Monoid (succ-ℕ n) x))
```
