# The ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.ring-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.group-of-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

The
[commutative group of rational numbers](elementary-number-theory.group-of-rational-numbers.md)
equipped with
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [commutative ring](commutative-algebra.commutative-rings.md).

## Definitions

### The compatible multiplicative structure on the abelian group of rational numbers

```agda
has-associative-mul-ℚ : has-associative-mul ℚ
pr1 has-associative-mul-ℚ = mul-ℚ
pr2 has-associative-mul-ℚ = associative-mul-ℚ

is-unital-mul-ℚ : is-unital mul-ℚ
pr1 is-unital-mul-ℚ = one-ℚ
pr1 (pr2 is-unital-mul-ℚ) = left-unit-law-mul-ℚ
pr2 (pr2 is-unital-mul-ℚ) = right-unit-law-mul-ℚ

has-mul-ℚ-Ab : has-mul-Ab ℚ-Ab
pr1 has-mul-ℚ-Ab = has-associative-mul-ℚ
pr1 (pr2 has-mul-ℚ-Ab) = is-unital-mul-ℚ
pr1 (pr2 (pr2 has-mul-ℚ-Ab)) = left-distributive-mul-add-ℚ
pr2 (pr2 (pr2 has-mul-ℚ-Ab)) = right-distributive-mul-add-ℚ
```

### The ring of rational numbers

```agda
ℚ-Ring : Ring lzero
pr1 ℚ-Ring = ℚ-Ab
pr2 ℚ-Ring = has-mul-ℚ-Ab
```

### The commutative ring of rational numbers

```agda
ℚ-Commutative-Ring : Commutative-Ring lzero
pr1 ℚ-Commutative-Ring = ℚ-Ring
pr2 ℚ-Commutative-Ring = commutative-mul-ℚ
```
