# Multiplication on integer fractions

```agda
module elementary-number-theory.multiplication-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

**Multiplication on integer fractions** is an extension of the
[multiplicative operation](elementary-number-theory.multiplication-integers.md)
on the [integers](elementary-number-theory.integers.md) to
[integer fractions](elementary-number-theory.integer-fractions.md). Note that
the basic properties of multiplication on integer fraction only hold up to
fraction similarity.

## Definitions

### Multiplication of integer fractions

```agda
numerator-mul-fraction-ℤ :
  (x y : fraction-ℤ) → ℤ
numerator-mul-fraction-ℤ x y =
  numerator-fraction-ℤ x *ℤ numerator-fraction-ℤ y

positive-denominator-mul-fraction-ℤ :
  (x y : fraction-ℤ) → positive-ℤ
positive-denominator-mul-fraction-ℤ x y =
  mul-positive-ℤ
    ( positive-denominator-fraction-ℤ x)
    ( positive-denominator-fraction-ℤ y)

denominator-mul-fraction-ℤ :
  (x y : fraction-ℤ) → ℤ
denominator-mul-fraction-ℤ x y =
  int-positive-ℤ (positive-denominator-mul-fraction-ℤ x y)

is-positive-denominator-mul-fraction-ℤ :
  (x y : fraction-ℤ) → is-positive-ℤ (denominator-mul-fraction-ℤ x y)
is-positive-denominator-mul-fraction-ℤ x y =
  is-positive-int-positive-ℤ (positive-denominator-mul-fraction-ℤ x y)

mul-fraction-ℤ : fraction-ℤ → fraction-ℤ → fraction-ℤ
pr1 (mul-fraction-ℤ x y) = numerator-mul-fraction-ℤ x y
pr2 (mul-fraction-ℤ x y) = positive-denominator-mul-fraction-ℤ x y

mul-fraction-ℤ' : fraction-ℤ → fraction-ℤ → fraction-ℤ
mul-fraction-ℤ' x y = mul-fraction-ℤ y x

infixl 40 _*fraction-ℤ_
_*fraction-ℤ_ = mul-fraction-ℤ

ap-mul-fraction-ℤ :
  {x y x' y' : fraction-ℤ} → x ＝ x' → y ＝ y' →
  x *fraction-ℤ y ＝ x' *fraction-ℤ y'
ap-mul-fraction-ℤ p q = ap-binary mul-fraction-ℤ p q
```

## Properties

### Multiplication on integer fractions respects the similarity relation

```agda
sim-fraction-mul-fraction-ℤ :
  {x x' y y' : fraction-ℤ} →
  sim-fraction-ℤ x x' →
  sim-fraction-ℤ y y' →
  sim-fraction-ℤ (x *fraction-ℤ y) (x' *fraction-ℤ y')
sim-fraction-mul-fraction-ℤ
  {(nx , dx , dxp)} {(nx' , dx' , dx'p)}
  {(ny , dy , dyp)} {(ny' , dy' , dy'p)} p q =
  equational-reasoning
    (nx *ℤ ny) *ℤ (dx' *ℤ dy')
    ＝ (nx *ℤ dx') *ℤ (ny *ℤ dy')
      by interchange-law-mul-mul-ℤ nx ny dx' dy'
    ＝ (nx' *ℤ dx) *ℤ (ny' *ℤ dy)
      by ap-mul-ℤ p q
    ＝ (nx' *ℤ ny') *ℤ (dx *ℤ dy)
      by interchange-law-mul-mul-ℤ nx' dx ny' dy
```

### Unit laws for multiplication on integer fractions

```agda
left-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ one-fraction-ℤ k) k
left-unit-law-mul-fraction-ℤ k = refl

right-unit-law-mul-fraction-ℤ :
  (k : fraction-ℤ) →
  sim-fraction-ℤ (mul-fraction-ℤ k one-fraction-ℤ) k
right-unit-law-mul-fraction-ℤ (n , d , p) =
  ap-mul-ℤ (right-unit-law-mul-ℤ n) (inv (right-unit-law-mul-ℤ d))
```

### Multiplication on integer fractions is associative

```agda
associative-mul-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    ( mul-fraction-ℤ (mul-fraction-ℤ x y) z)
    ( mul-fraction-ℤ x (mul-fraction-ℤ y z))
associative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
  ap-mul-ℤ (associative-mul-ℤ nx ny nz) (inv (associative-mul-ℤ dx dy dz))
```

### Multiplication on integer fractions is commutative

```agda
commutative-mul-fraction-ℤ :
  (x y : fraction-ℤ) → sim-fraction-ℤ (x *fraction-ℤ y) (y *fraction-ℤ x)
commutative-mul-fraction-ℤ (nx , dx , dxp) (ny , dy , dyp) =
  ap-mul-ℤ (commutative-mul-ℤ nx ny) (commutative-mul-ℤ dy dx)
```

### Multiplication on integer fractions distributes on the left over addition

```agda
left-distributive-mul-add-fraction-ℤ :
  (x y z : fraction-ℤ) →
  sim-fraction-ℤ
    ( mul-fraction-ℤ x (add-fraction-ℤ y z))
    ( add-fraction-ℤ (mul-fraction-ℤ x y) (mul-fraction-ℤ x z))
left-distributive-mul-add-fraction-ℤ
  (nx , dx , dxp) (ny , dy , dyp) (nz , dz , dzp) =
    ( ap
      ( ( nx *ℤ (ny *ℤ dz +ℤ nz *ℤ dy)) *ℤ_)
      ( ( interchange-law-mul-mul-ℤ dx dy dx dz) ∙
        ( associative-mul-ℤ dx dx (dy *ℤ dz)))) ∙
    ( interchange-law-mul-mul-ℤ
      ( nx)
      ( ny *ℤ dz +ℤ nz *ℤ dy)
      ( dx)
      ( dx *ℤ (dy *ℤ dz))) ∙
    ( inv
      ( associative-mul-ℤ
        ( nx *ℤ dx)
        ( ny *ℤ dz +ℤ nz *ℤ dy)
        ( dx *ℤ (dy *ℤ dz)))) ∙
    ( ap
      ( _*ℤ (dx *ℤ (dy *ℤ dz)))
      ( ( left-distributive-mul-add-ℤ
          ( nx *ℤ dx)
          ( ny *ℤ dz)
          ( nz *ℤ dy)) ∙
        ( ap-add-ℤ
          ( interchange-law-mul-mul-ℤ nx dx ny dz))
          ( interchange-law-mul-mul-ℤ nx dx nz dy)))
```
