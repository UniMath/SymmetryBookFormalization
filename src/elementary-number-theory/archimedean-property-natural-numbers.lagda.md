# The Archimedean property of the natural numbers

```agda
module elementary-number-theory.archimedean-property-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
```

</details>

## Definition

The
{{#concept "Archimedean property" Disambiguation="natural numbers" Agda=archimedean-property-ℕ}}
of the [natural numbers](elementary-number-theory.natural-numbers.md) is that
for any nonzero natural number `x` and any natural number `y`, there is an
`n : ℕ` such that `y < n *ℕ x`.

```agda
abstract
  bound-archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → Σ ℕ (λ n → le-ℕ y (n *ℕ x))
  bound-archimedean-property-ℕ x y nonzero-x =
    succ-ℕ (quotient-euclidean-division-ℕ x y) ,
    tr
      ( λ z → z <-ℕ succ-ℕ (quotient-euclidean-division-ℕ x y) *ℕ x)
      ( eq-euclidean-division-ℕ x y)
      ( preserves-le-left-add-ℕ
        ( quotient-euclidean-division-ℕ x y *ℕ x)
        ( remainder-euclidean-division-ℕ x y)
        ( x)
        ( strict-upper-bound-remainder-euclidean-division-ℕ x y nonzero-x))

  archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → exists ℕ (λ n → le-ℕ-Prop y (n *ℕ x))
  archimedean-property-ℕ x y nonzero-x =
    unit-trunc-Prop (bound-archimedean-property-ℕ x y nonzero-x)
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
