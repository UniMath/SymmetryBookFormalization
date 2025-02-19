# The rational numbers

```agda
module elementary-number-theory.rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import set-theory.countable-sets
```

</details>

## Idea

The type of
{{#concept "rational numbers" Agda=ℚ WD="rational number" WDID=Q1244890}} is the
[quotient](foundation.set-quotients.md) of the type of
[integer fractions](elementary-number-theory.integer-fractions.md) by the
[equivalence relation](foundation.equivalence-relations.md) given by

$$
\frac{n}{m} \sim \frac{n'}{m'} := nm' = n'm.
$$

Since the
[reduced fractions](elementary-number-theory.reduced-integer-fractions.md) are
[canonical representatives](foundation.choice-of-representatives-equivalence-relation.md)
of the similarity relation on fractions, we simply define the
[set](foundation.sets.md) `ℚ` to be the type of reduced fractions and we obtain
the
[universal property of the set quotient](foundation.universal-property-set-quotients.md)
from the fact that each equivalence class has a unique canonical representative.

## Definitions

### The type of rationals

```agda
ℚ : UU lzero
ℚ = Σ fraction-ℤ is-reduced-fraction-ℤ

module _
  (x : ℚ)
  where

  fraction-ℚ : fraction-ℤ
  fraction-ℚ = pr1 x

  is-reduced-fraction-ℚ : is-reduced-fraction-ℤ fraction-ℚ
  is-reduced-fraction-ℚ = pr2 x

  numerator-ℚ : ℤ
  numerator-ℚ = numerator-fraction-ℤ fraction-ℚ

  positive-denominator-ℚ : positive-ℤ
  positive-denominator-ℚ = positive-denominator-fraction-ℤ fraction-ℚ

  denominator-ℚ : ℤ
  denominator-ℚ = denominator-fraction-ℤ fraction-ℚ

  is-positive-denominator-ℚ : is-positive-ℤ denominator-ℚ
  is-positive-denominator-ℚ = is-positive-denominator-fraction-ℤ fraction-ℚ
```

### Inclusion of fractions

```agda
rational-fraction-ℤ : fraction-ℤ → ℚ
pr1 (rational-fraction-ℤ x) = reduce-fraction-ℤ x
pr2 (rational-fraction-ℤ x) = is-reduced-reduce-fraction-ℤ x
```

### Inclusion of the integers

```agda
rational-ℤ : ℤ → ℚ
pr1 (pr1 (rational-ℤ x)) = x
pr2 (pr1 (rational-ℤ x)) = one-positive-ℤ
pr2 (rational-ℤ x) = is-one-gcd-one-ℤ' x
```

### Negative one, zero and one

```agda
neg-one-ℚ : ℚ
neg-one-ℚ = rational-ℤ neg-one-ℤ

is-neg-one-ℚ : ℚ → UU lzero
is-neg-one-ℚ x = (x ＝ neg-one-ℚ)

zero-ℚ : ℚ
zero-ℚ = rational-ℤ zero-ℤ

is-zero-ℚ : ℚ → UU lzero
is-zero-ℚ x = (x ＝ zero-ℚ)

is-nonzero-ℚ : ℚ → UU lzero
is-nonzero-ℚ k = ¬ (is-zero-ℚ k)

one-ℚ : ℚ
one-ℚ = rational-ℤ one-ℤ

is-one-ℚ : ℚ → UU lzero
is-one-ℚ x = (x ＝ one-ℚ)
```

### The negative of a rational number

```agda
neg-ℚ : ℚ → ℚ
pr1 (neg-ℚ (x , H)) = neg-fraction-ℤ x
pr2 (neg-ℚ (x , H)) = is-reduced-neg-fraction-ℤ x H
```

### The mediant of two rationals

```agda
mediant-ℚ : ℚ → ℚ → ℚ
mediant-ℚ x y =
  rational-fraction-ℤ
    ( mediant-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y))
```

## Properties

### The rational images of two similar integer fractions are equal

```agda
abstract
  eq-ℚ-sim-fraction-ℤ :
    (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
    rational-fraction-ℤ x ＝ rational-fraction-ℤ y
  eq-ℚ-sim-fraction-ℤ x y H =
    eq-pair-Σ'
      ( pair
        ( unique-reduce-fraction-ℤ x y H)
        ( eq-is-prop (is-prop-is-reduced-fraction-ℤ (reduce-fraction-ℤ y))))
```

### The type of rationals is a set

```agda
abstract
  is-set-ℚ : is-set ℚ
  is-set-ℚ =
    is-set-Σ
      ( is-set-fraction-ℤ)
      ( λ x → is-set-is-prop (is-prop-is-reduced-fraction-ℤ x))

ℚ-Set : Set lzero
pr1 ℚ-Set = ℚ
pr2 ℚ-Set = is-set-ℚ
```

### The rationals are a retract of the integer fractions

```agda
abstract
  is-retraction-rational-fraction-ℚ :
    (x : ℚ) → rational-fraction-ℤ (fraction-ℚ x) ＝ x
  is-retraction-rational-fraction-ℚ ((m , n , n-pos) , p) =
    eq-pair-Σ
      ( eq-pair
        ( eq-quotient-div-is-one-ℤ _ _ p (div-left-gcd-ℤ m n))
        ( eq-pair-Σ
          ( eq-quotient-div-is-one-ℤ _ _ p (div-right-gcd-ℤ m n))
          ( eq-is-prop (is-prop-is-positive-ℤ n))))
      ( eq-is-prop (is-prop-is-reduced-fraction-ℤ (m , n , n-pos)))

section-rational-fraction-ℤ : section rational-fraction-ℤ
section-rational-fraction-ℤ = (fraction-ℚ , is-retraction-rational-fraction-ℚ)

retract-integer-fraction-ℚ : ℚ retract-of fraction-ℤ
retract-integer-fraction-ℚ =
  ( fraction-ℚ , rational-fraction-ℤ , is-retraction-rational-fraction-ℚ)
```

### The rationals are countable

The denumerability of the rational numbers is the
[third](literature.100-theorems.md#3) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
is-countable-ℚ : is-countable ℚ-Set
is-countable-ℚ =
  is-countable-retract-of
    ( fraction-ℤ-Set)
    ( ℚ-Set)
    ( retract-integer-fraction-ℚ)
    ( is-countable-fraction-ℤ)
```

### Two fractions with the same numerator and same denominator are equal

```agda
module _
  ( x y : ℚ)
  ( H : numerator-ℚ x ＝ numerator-ℚ y)
  ( K : denominator-ℚ x ＝ denominator-ℚ y)
  where

  abstract
    eq-ℚ : x ＝ y
    eq-ℚ =
      ( inv (is-retraction-rational-fraction-ℚ x)) ∙
      ( eq-ℚ-sim-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)
        ( ap-mul-ℤ H (inv K))) ∙
      ( is-retraction-rational-fraction-ℚ y)
```

### A rational number is zero if and only if its numerator is zero

```agda
module _
  (x : ℚ)
  where

  abstract
    is-zero-numerator-is-zero-ℚ :
      is-zero-ℚ x → is-zero-ℤ (numerator-ℚ x)
    is-zero-numerator-is-zero-ℚ = ap numerator-ℚ

    is-zero-is-zero-numerator-ℚ :
      is-zero-ℤ (numerator-ℚ x) → is-zero-ℚ x
    is-zero-is-zero-numerator-ℚ H =
      ( inv (is-retraction-rational-fraction-ℚ x)) ∙
      ( eq-ℚ-sim-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ zero-ℚ)
        ( eq-is-zero-ℤ
          ( ap (mul-ℤ' one-ℤ) H ∙ right-zero-law-mul-ℤ one-ℤ)
          ( left-zero-law-mul-ℤ (denominator-ℚ x)))) ∙
      ( is-retraction-rational-fraction-ℚ zero-ℚ)
```

### The rational image of the negative of an integer is the rational negative of its image

```agda
abstract
  preserves-neg-rational-ℤ :
    (k : ℤ) → rational-ℤ (neg-ℤ k) ＝ neg-ℚ (rational-ℤ k)
  preserves-neg-rational-ℤ k =
    eq-ℚ (rational-ℤ (neg-ℤ k)) (neg-ℚ (rational-ℤ k)) refl refl
```

### The reduced fraction of the negative of an integer fraction is the negative of the reduced fraction

```agda
abstract
  preserves-neg-rational-fraction-ℤ :
    (x : fraction-ℤ) →
    rational-fraction-ℤ (neg-fraction-ℤ x) ＝ neg-ℚ (rational-fraction-ℤ x)
  preserves-neg-rational-fraction-ℤ x =
    ( eq-ℚ-sim-fraction-ℤ
      ( neg-fraction-ℤ x)
      ( fraction-ℚ (neg-ℚ (rational-fraction-ℤ x)))
      ( preserves-sim-neg-fraction-ℤ
        ( x)
        ( reduce-fraction-ℤ x)
        ( sim-reduced-fraction-ℤ x))) ∙
    ( is-retraction-rational-fraction-ℚ (neg-ℚ (rational-fraction-ℤ x)))
```

### The negative function on the rational numbers is an involution

```agda
abstract
  neg-neg-ℚ : (x : ℚ) → neg-ℚ (neg-ℚ x) ＝ x
  neg-neg-ℚ x = eq-ℚ (neg-ℚ (neg-ℚ x)) x (neg-neg-ℤ (numerator-ℚ x)) refl
```

### The reflecting map from `fraction-ℤ` to `ℚ`

```agda
reflecting-map-sim-fraction :
  reflecting-map-equivalence-relation equivalence-relation-sim-fraction-ℤ ℚ
pr1 reflecting-map-sim-fraction = rational-fraction-ℤ
pr2 reflecting-map-sim-fraction {x} {y} H = eq-ℚ-sim-fraction-ℤ x y H
```

## See also

- [Farey fractions](elementary-number-theory.farey-fractions.md) encode the type
  of rational numbers between $0$ and $1$ by a mutual recursive construction.
- [Unbounded Farey fractions](elementary-number-theory.unbounded-farey-fractions.md)
  encode the type of all rational numbers by a mutal recursive construction.

## References

{{#bibliography}}
