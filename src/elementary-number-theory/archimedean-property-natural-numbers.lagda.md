# The Archimedean property of the natural numbers

```agda
module elementary-number-theory.archimedean-property-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "Archimedean property" Disambiguation="natural numbers" Agda=archimedean-property-ℕ}}
of the [natural numbers](elementary-number-theory.natural-numbers.md) is that
for any [nonzero natural number](elementary-number-theory.nonzero-natural-numbers.md) `x` and any natural number `y`, there is an
`n : ℕ` such that `y < n *ℕ x`.

## Definitions

### The Archimedian property of the natural numbers

```agda
abstract
  archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → exists-structure ℕ (λ n → y <-ℕ n *ℕ x)
  archimedean-property-ℕ x y nonzero-x =
    intro-exists
      ( succ-ℕ (quotient-euclidean-division-ℕ x y))
      ( concatenate-eq-le-eq-ℕ
        ( y)
        ( quotient-euclidean-division-ℕ x y *ℕ x +ℕ
          remainder-euclidean-division-ℕ x y)
        ( quotient-euclidean-division-ℕ x y *ℕ x +ℕ x)
        ( succ-ℕ (quotient-euclidean-division-ℕ x y) *ℕ x)
        ( inv (eq-euclidean-division-ℕ x y))
        ( preserves-strict-order-right-add-ℕ
          ( quotient-euclidean-division-ℕ x y *ℕ x)
          ( remainder-euclidean-division-ℕ x y)
          ( x)
          ( strict-upper-bound-remainder-euclidean-division-ℕ x y nonzero-x))
        ( inv (left-successor-law-mul-ℕ (quotient-euclidean-division-ℕ x y) x)))
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
