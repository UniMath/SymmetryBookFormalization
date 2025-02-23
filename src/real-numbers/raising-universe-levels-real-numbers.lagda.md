# Raising the universe levels of real numbers

```agda
module real-numbers.raising-universe-levels-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

[Real numbers](real-numbers.dedekind-real-numbers.md) are defined at specific
[universe levels](foundation.universe-levels.md), which do not overlap.

For any real number, we can construct a
[similar](real-numbers.similarity-real-numbers.md) real number in any higher
universe.

## Definition

### Raising lower Dedekind real numbers

```agda
module _
  {l0 : Level} (l : Level) (x : lower-ℝ l0)
  where

  cut-raise-lower-ℝ : subtype (l0 ⊔ l) ℚ
  cut-raise-lower-ℝ = raise-subtype l (cut-lower-ℝ x)

  abstract
    is-inhabited-cut-raise-lower-ℝ : is-inhabited-subtype cut-raise-lower-ℝ
    is-inhabited-cut-raise-lower-ℝ =
      map-tot-exists (λ _ → map-raise) (is-inhabited-cut-lower-ℝ x)

    is-rounded-cut-raise-lower-ℝ :
      (q : ℚ) →
      is-in-subtype cut-raise-lower-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-raise-lower-ℝ r)
    pr1 (is-rounded-cut-raise-lower-ℝ q) (map-raise q<x) =
      map-tot-exists
        ( λ _ → map-product id map-raise)
        ( forward-implication (is-rounded-cut-lower-ℝ x q) q<x)
    pr2 (is-rounded-cut-raise-lower-ℝ q) ∃r =
      map-raise
        ( backward-implication
          ( is-rounded-cut-lower-ℝ x q)
          ( map-tot-exists (λ _ → map-product id map-inv-raise) ∃r))

  raise-lower-ℝ : lower-ℝ (l0 ⊔ l)
  raise-lower-ℝ =
    cut-raise-lower-ℝ ,
    is-inhabited-cut-raise-lower-ℝ ,
    is-rounded-cut-raise-lower-ℝ
```

### Raising upper Dedekind real numbers

```agda
module _
  {l0 : Level} (l : Level) (x : upper-ℝ l0)
  where

  cut-raise-upper-ℝ : subtype (l0 ⊔ l) ℚ
  cut-raise-upper-ℝ = raise-subtype l (cut-upper-ℝ x)

  abstract
    is-inhabited-cut-raise-upper-ℝ : is-inhabited-subtype cut-raise-upper-ℝ
    is-inhabited-cut-raise-upper-ℝ =
      map-tot-exists (λ _ → map-raise) (is-inhabited-cut-upper-ℝ x)

    is-rounded-cut-raise-upper-ℝ :
      (q : ℚ) →
      is-in-subtype cut-raise-upper-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-raise-upper-ℝ p)
    pr1 (is-rounded-cut-raise-upper-ℝ q) (map-raise x<q) =
      map-tot-exists
        ( λ _ → map-product id map-raise)
        ( forward-implication (is-rounded-cut-upper-ℝ x q) x<q)
    pr2 (is-rounded-cut-raise-upper-ℝ q) ∃p =
      map-raise
        ( backward-implication
          ( is-rounded-cut-upper-ℝ x q)
          ( map-tot-exists (λ _ → map-product id map-inv-raise) ∃p))

  raise-upper-ℝ : upper-ℝ (l0 ⊔ l)
  raise-upper-ℝ =
    cut-raise-upper-ℝ ,
    is-inhabited-cut-raise-upper-ℝ ,
    is-rounded-cut-raise-upper-ℝ
```

### Raising Dedekind real numbers

```agda
module _
  {l0 : Level} (l : Level) (x : ℝ l0)
  where

  lower-real-raise-ℝ : lower-ℝ (l0 ⊔ l)
  lower-real-raise-ℝ = raise-lower-ℝ l (lower-real-ℝ x)

  upper-real-raise-ℝ : upper-ℝ (l0 ⊔ l)
  upper-real-raise-ℝ = raise-upper-ℝ l (upper-real-ℝ x)

  abstract
    is-disjoint-cut-raise-ℝ :
      (q : ℚ) →
      ¬
        ( is-in-cut-lower-ℝ lower-real-raise-ℝ q ×
          is-in-cut-upper-ℝ upper-real-raise-ℝ q)
    is-disjoint-cut-raise-ℝ q (map-raise q<x , map-raise x<q) =
      is-disjoint-cut-ℝ x q (q<x , x<q)

    is-located-lower-upper-cut-raise-ℝ :
      (p q : ℚ) → le-ℚ p q →
      type-disjunction-Prop
        ( cut-lower-ℝ lower-real-raise-ℝ p)
        ( cut-upper-ℝ upper-real-raise-ℝ q)
    is-located-lower-upper-cut-raise-ℝ p q p<q =
      elim-disjunction
        ( cut-lower-ℝ lower-real-raise-ℝ p ∨ cut-upper-ℝ upper-real-raise-ℝ q)
        ( inl-disjunction ∘ map-raise)
        ( inr-disjunction ∘ map-raise)
        ( is-located-lower-upper-cut-ℝ x p q p<q)

  raise-ℝ : ℝ (l0 ⊔ l)
  raise-ℝ =
    real-lower-upper-ℝ
      ( lower-real-raise-ℝ)
      ( upper-real-raise-ℝ)
      ( is-disjoint-cut-raise-ℝ)
      ( is-located-lower-upper-cut-raise-ℝ)
```

## Properties

### Reals are similar to their raised-universe equivalents

```agda
sim-raise-ℝ : {l0 : Level} → (l : Level) → (x : ℝ l0) → sim-ℝ x (raise-ℝ l x)
pr1 (sim-raise-ℝ l x) _ = map-raise
pr2 (sim-raise-ℝ l x) _ = map-inv-raise
```

### Raising a real to its own level is the identity

```agda
eq-raise-ℝ : {l : Level} → (x : ℝ l) → x ＝ raise-ℝ l x
eq-raise-ℝ {l} x = eq-sim-ℝ x (raise-ℝ l x) (sim-raise-ℝ l x)
```
