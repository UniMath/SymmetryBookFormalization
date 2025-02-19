# Decidable subtypes of the natural numbers

```agda
module elementary-number-theory.decidable-subtypes-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bounded-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.decidable-subtypes
```

</details>

## Idea

In this file we study [decidable subtypes](foundation.decidable-subtypes.md) of
the [natural numbers](elementary-number-theory.natural-numbers.md). The type of
all decidable subtypes of the natural numbers is the _decidable powerset of the
natural numbers_.

As a direct consequence of the
[well-ordering principle](elementary-number-theory.well-ordering-principle-natural-numbers.md)
of the natural numbers, which is formulated for decidable structures over the
natural numbers, it follows that every
[inhabited](foundation.inhabited-subtypes.md) decidable subtype of the natural
numbers has a least element. We also show that every finite decidable subtype
has a largest element.

## Properties

### Inhabited decidable subtypes of the natural numbers have a minimal element

```agda
module _
  {l : Level} (P : decidable-subtype l ℕ)
  where

  well-ordering-principle-decidable-subtype-ℕ :
    is-inhabited-subtype (subtype-decidable-subtype P) →
    minimal-element-ℕ (is-in-decidable-subtype P)
  well-ordering-principle-decidable-subtype-ℕ H =
    apply-universal-property-trunc-Prop H
      ( minimal-element-ℕ-Prop (subtype-decidable-subtype P))
      ( λ (n , p) →
        well-ordering-principle-ℕ
          ( is-in-decidable-subtype P)
          ( is-decidable-decidable-subtype P)
          ( p))
```

### Inhatbited finite decidable subtypes of the natural numbers have a maximal element

```agda
module _
  {l : Level} (P : decidable-subtype l ℕ)
  where

  nat-maximal-element-count-type-decidable-subtype-ℕ :
    count (type-decidable-subtype P) → ℕ
  nat-maximal-element-count-type-decidable-subtype-ℕ (n , e) =
    max-standard-finite-family-ℕ n
      ( inclusion-decidable-subtype P ∘ map-equiv e)

  is-in-subtype-maximal-element-count-type-decidable-subtype-ℕ :
    (e : count (type-decidable-subtype P)) →
    type-decidable-subtype P →
    is-in-decidable-subtype P
      ( nat-maximal-element-count-type-decidable-subtype-ℕ e)
  is-in-subtype-maximal-element-count-type-decidable-subtype-ℕ (zero-ℕ , e) x =
    ex-falso (map-inv-equiv e x)
  is-in-subtype-maximal-element-count-type-decidable-subtype-ℕ
    ( succ-ℕ n , e) x =
    tr
      ( is-in-decidable-subtype P)
      ( pr2
        ( is-attained-max-standard-finite-family-succ-ℕ n
          ( inclusion-decidable-subtype P ∘ map-equiv e)))
      ( pr2
        ( map-equiv e
          ( pr1
            ( is-attained-max-standard-finite-family-succ-ℕ n
              ( inclusion-decidable-subtype P ∘ map-equiv e)))))

  is-upper-bound-maximal-element-count-type-decidable-subtype-ℕ :
    (e : count (type-decidable-subtype P)) →
    (i : ℕ) → is-in-decidable-subtype P i →
    i ≤-ℕ nat-maximal-element-count-type-decidable-subtype-ℕ e
  is-upper-bound-maximal-element-count-type-decidable-subtype-ℕ
    (zero-ℕ , e) i p =
    ex-falso (map-inv-equiv e (i , p))
  is-upper-bound-maximal-element-count-type-decidable-subtype-ℕ
    (succ-ℕ n , e) i p =
    tr
      ( λ x → x ≤-ℕ _)
      ( ap pr1 (is-section-map-inv-equiv e (i , p)))
      ( is-upper-bound-max-standard-finite-family-ℕ
        ( succ-ℕ n)
        ( inclusion-decidable-subtype P ∘ map-equiv e)
        ( map-inv-equiv e (i , p)))

  maximal-element-count-type-decidable-subtype-ℕ :
    count (type-decidable-subtype P) →
    type-decidable-subtype P →
    maximal-element-ℕ (is-in-decidable-subtype P)
  pr1 (maximal-element-count-type-decidable-subtype-ℕ e K) =
    nat-maximal-element-count-type-decidable-subtype-ℕ e
  pr1 (pr2 (maximal-element-count-type-decidable-subtype-ℕ e K)) =
    is-in-subtype-maximal-element-count-type-decidable-subtype-ℕ e K
  pr2 (pr2 (maximal-element-count-type-decidable-subtype-ℕ e K)) i p =
    is-upper-bound-maximal-element-count-type-decidable-subtype-ℕ e i p

  maximal-element-is-finite-decidable-subtype-ℕ :
    is-finite (type-decidable-subtype P) →
    is-inhabited-subtype (subtype-decidable-subtype P) →
    maximal-element-ℕ (is-in-decidable-subtype P)
  maximal-element-is-finite-decidable-subtype-ℕ H K =
    apply-twice-universal-property-trunc-Prop H K
      ( maximal-element-ℕ-Prop (subtype-decidable-subtype P))
      ( maximal-element-count-type-decidable-subtype-ℕ)
```

### Decidable subtypes with a maximal element are finite

```agda
module _
  {l : Level} (P : decidable-subtype l ℕ)
  where

  is-finite-maximal-element-decidable-subtype-ℕ :
    maximal-element-ℕ (is-in-decidable-subtype P) →
    is-finite (type-decidable-subtype P)
  is-finite-maximal-element-decidable-subtype-ℕ (m , H , K) =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ (x , p) → is-proof-irrelevant-leq-ℕ x m (K x p))) ∘e
        ( equiv-right-swap-Σ))
      ( is-finite-type-decidable-subtype
        ( P ∘ pr1)
        ( is-finite-bounded-ℕ m))
```
