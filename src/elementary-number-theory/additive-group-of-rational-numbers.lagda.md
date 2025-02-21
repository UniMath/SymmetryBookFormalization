# The additive group of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.additive-group-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
is a [commutative group](group-theory.abelian-groups.md) with unit `zero-ℚ` and
inverse given by`neg-ℚ`.

## Definitions

### The additive abelian group of rational numbers

```agda
semigroup-add-ℚ : Semigroup lzero
pr1 semigroup-add-ℚ = ℚ-Set
pr1 (pr2 semigroup-add-ℚ) = add-ℚ
pr2 (pr2 semigroup-add-ℚ) = associative-add-ℚ

is-unital-add-ℚ : is-unital add-ℚ
pr1 is-unital-add-ℚ = zero-ℚ
pr1 (pr2 is-unital-add-ℚ) = left-unit-law-add-ℚ
pr2 (pr2 is-unital-add-ℚ) = right-unit-law-add-ℚ

monoid-add-ℚ : Monoid lzero
pr1 monoid-add-ℚ = semigroup-add-ℚ
pr2 monoid-add-ℚ = is-unital-add-ℚ

group-add-ℚ : Group lzero
pr1 group-add-ℚ = semigroup-add-ℚ
pr1 (pr2 group-add-ℚ) = is-unital-add-ℚ
pr1 (pr2 (pr2 group-add-ℚ)) = neg-ℚ
pr1 (pr2 (pr2 (pr2 group-add-ℚ))) = left-inverse-law-add-ℚ
pr2 (pr2 (pr2 (pr2 group-add-ℚ))) = right-inverse-law-add-ℚ
```

## Properties

### The additive group of rational numbers is commutative

```agda
abelian-group-add-ℚ : Ab lzero
pr1 abelian-group-add-ℚ = group-add-ℚ
pr2 abelian-group-add-ℚ = commutative-add-ℚ
```

### Identities for addition on the rational numbers from group properties

```agda
abstract
  is-identity-right-conjugation-add-ℚ : (p q : ℚ) → p +ℚ (q -ℚ p) ＝ q
  is-identity-right-conjugation-add-ℚ =
    is-identity-right-conjugation-Ab abelian-group-add-ℚ

  is-identity-left-conjugation-add-ℚ : (p q : ℚ) → (p +ℚ q) -ℚ p ＝ q
  is-identity-left-conjugation-add-ℚ =
    is-identity-left-conjugation-Ab abelian-group-add-ℚ

  is-section-diff-ℚ : (p q : ℚ) → (q -ℚ p) +ℚ p ＝ q
  is-section-diff-ℚ = is-section-right-div-Group group-add-ℚ

  is-retraction-diff-ℚ : (p q : ℚ) → (q +ℚ p) -ℚ p ＝ q
  is-retraction-diff-ℚ = is-retraction-right-div-Group group-add-ℚ
```
