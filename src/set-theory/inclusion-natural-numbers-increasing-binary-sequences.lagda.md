# The canonical inclusion of natural numbers into increasing binary sequences

```agda
module set-theory.inclusion-natural-numbers-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import foundation-core.identity-types

open import logic.double-negation-dense-maps
open import logic.double-negation-eliminating-maps

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
open import set-theory.finite-elements-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
```

</details>

## Idea

The canonical map `ℕ → ℕ∞↑` defined by induction to send zero to zero, and the
successor of `n` to the successor of the map evaluated at `n` is the
{{#concept "canonical inclusion" Disambiguaiton="of the natural numbers into increasing binary sequences" Agda=inclusion-ℕ∞↑-ℕ}}.
This map is a [embedding](foundation-core.embeddings.md) of
[sets](foundation-core.sets.md) that is
non-[surjective](foundation.surjective-maps.md), as it does not hit the element
at infinity. We may extend this inclusion by adding a point at infinity

```text
  ℕ + {∞} ↪ ℕ∞↑
```

to obtain a [double negation dense](logic.double-negation-dense-maps.md)
embedding of sets. This map is surjective if and only if the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
holds.

## Definitions

### The canonical inclusion of natural numbers

```agda
inclusion-ℕ∞↑-ℕ : ℕ → ℕ∞↑
inclusion-ℕ∞↑-ℕ = rec-ℕ zero-ℕ∞↑ (λ _ → succ-ℕ∞↑)
```

### The canonical extended inclusion

```agda
inclusion-ℕ∞↑-Maybe-ℕ : Maybe ℕ → ℕ∞↑
inclusion-ℕ∞↑-Maybe-ℕ = rec-coproduct inclusion-ℕ∞↑-ℕ (point infinity-ℕ∞↑)
```

## Properties

### The canonical inclusion is an embedding

```agda
abstract
  is-injective-inclusion-ℕ∞↑-ℕ : is-injective inclusion-ℕ∞↑-ℕ
  is-injective-inclusion-ℕ∞↑-ℕ {zero-ℕ} {zero-ℕ} p =
    refl
  is-injective-inclusion-ℕ∞↑-ℕ {zero-ℕ} {succ-ℕ y} p =
    ex-falso (neq-zero-succ-ℕ∞↑ p)
  is-injective-inclusion-ℕ∞↑-ℕ {succ-ℕ x} {zero-ℕ} p =
    ex-falso (neq-succ-zero-ℕ∞↑ p)
  is-injective-inclusion-ℕ∞↑-ℕ {succ-ℕ x} {succ-ℕ y} p =
    ap succ-ℕ (is-injective-inclusion-ℕ∞↑-ℕ (is-injective-succ-ℕ∞↑ p))

abstract
  is-emb-inclusion-ℕ∞↑-ℕ : is-emb inclusion-ℕ∞↑-ℕ
  is-emb-inclusion-ℕ∞↑-ℕ =
    is-emb-is-injective is-set-ℕ∞↑ is-injective-inclusion-ℕ∞↑-ℕ
```

### The canonical inclusion preserves order

```agda
abstract
  preserves-order-inclusion-ℕ∞↑-ℕ :
    preserves-order-Poset ℕ-Poset ℕ∞↑-Poset inclusion-ℕ∞↑-ℕ
  preserves-order-inclusion-ℕ∞↑-ℕ zero-ℕ y p =
    leq-zero-ℕ∞↑ (inclusion-ℕ∞↑-ℕ y)
  preserves-order-inclusion-ℕ∞↑-ℕ
    ( succ-ℕ x) (succ-ℕ y) p =
    preserves-order-succ-ℕ∞↑
      ( inclusion-ℕ∞↑-ℕ x)
      ( inclusion-ℕ∞↑-ℕ y)
      ( preserves-order-inclusion-ℕ∞↑-ℕ x y p)
```

### The canonical inclusion is not surjective

```agda
abstract
  Neq-infinity-inclusion-ℕ∞↑-ℕ :
    (n : ℕ) → ¬ (sequence-ℕ∞↑ (inclusion-ℕ∞↑-ℕ n) ~ const ℕ false)
  Neq-infinity-inclusion-ℕ∞↑-ℕ zero-ℕ H = neq-true-false-bool (H 0)
  Neq-infinity-inclusion-ℕ∞↑-ℕ (succ-ℕ n) H =
    Neq-infinity-inclusion-ℕ∞↑-ℕ n (H ∘ succ-ℕ)

neq-infinity-inclusion-ℕ∞↑-ℕ :
    (n : ℕ) → inclusion-ℕ∞↑-ℕ n ≠ infinity-ℕ∞↑
neq-infinity-inclusion-ℕ∞↑-ℕ n =
  map-neg Eq-eq-ℕ∞↑ (Neq-infinity-inclusion-ℕ∞↑-ℕ n)

is-not-double-negation-dense-inclusion-ℕ∞↑-ℕ :
  ¬ (is-double-negation-dense-map inclusion-ℕ∞↑-ℕ)
is-not-double-negation-dense-inclusion-ℕ∞↑-ℕ H =
  H infinity-ℕ∞↑ (λ p → neq-infinity-inclusion-ℕ∞↑-ℕ (pr1 p) (pr2 p))

is-not-surjective-inclusion-ℕ∞↑-ℕ : ¬ (is-surjective inclusion-ℕ∞↑-ℕ)
is-not-surjective-inclusion-ℕ∞↑-ℕ =
  map-neg
    is-double-negation-dense-map-is-surjective
    is-not-double-negation-dense-inclusion-ℕ∞↑-ℕ
```

### The canonical extended inclusion is an embedding

```agda
abstract
  is-emb-inclusion-ℕ∞↑-Maybe-ℕ : is-emb inclusion-ℕ∞↑-Maybe-ℕ
  is-emb-inclusion-ℕ∞↑-Maybe-ℕ =
    is-emb-coproduct
      ( is-emb-inclusion-ℕ∞↑-ℕ)
      ( is-emb-is-injective is-set-ℕ∞↑ (is-injective-point infinity-ℕ∞↑))
      ( λ n * → neq-infinity-inclusion-ℕ∞↑-ℕ n)
```

#### Successor condition on the image of the natural numbers

If an increasing binary sequence `x` switches from `false` to `true` at `n + 1`,
then it is the image of `n + 1`.

```agda
abstract
  Eq-succ-criterion-ℕ∞↑ :
    {x : ℕ∞↑} {n : ℕ} →
    n <-ℕ-ℕ∞↑ x → x ≤-ℕ∞↑-ℕ (succ-ℕ n) → Eq-ℕ∞↑ x (inclusion-ℕ∞↑-ℕ (succ-ℕ n))
  Eq-succ-criterion-ℕ∞↑ {x} {0} r s 0 = r
  Eq-succ-criterion-ℕ∞↑ {x} {0} r s (succ-ℕ i) =
    leq-leq-zero-ℕ-ℕ∞↑ (shift-left-ℕ∞↑ x) i s
  Eq-succ-criterion-ℕ∞↑ {x} {succ-ℕ n} r s 0 =
    is-positive-le-ℕ∞↑-ℕ x (succ-ℕ n) r
  Eq-succ-criterion-ℕ∞↑ {x} {succ-ℕ n} r s (succ-ℕ i) =
    Eq-succ-criterion-ℕ∞↑ {shift-left-ℕ∞↑ x} {n} r s i

eq-succ-criterion-ℕ∞↑ :
  {x : ℕ∞↑} {n : ℕ} →
  n <-ℕ-ℕ∞↑ x → x ≤-ℕ∞↑-ℕ (succ-ℕ n) → x ＝ inclusion-ℕ∞↑-ℕ (succ-ℕ n)
eq-succ-criterion-ℕ∞↑ {x} {n} r s =
  is-injective-sequence-ℕ∞↑ (eq-htpy (Eq-succ-criterion-ℕ∞↑ {x} {n} r s))
```

### If an increasing binary sequence is not in the image of the natural numbers it is infinite

```agda
module _
  (x : ℕ∞↑)
  (H : (n : ℕ) → x ≠ inclusion-ℕ∞↑-ℕ n)
  where

  abstract
    Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ :
      sequence-ℕ∞↑ x ~ const ℕ false
    Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ zero-ℕ =
      is-false-is-not-true (sequence-ℕ∞↑ x 0) (H 0 ∘ eq-zero-is-zero-ℕ∞↑ x)
    Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ (succ-ℕ n) =
      is-false-is-not-true
        ( sequence-ℕ∞↑ x (succ-ℕ n))
        ( H (succ-ℕ n) ∘
          eq-succ-criterion-ℕ∞↑ (Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ n))

  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ : x ＝ infinity-ℕ∞↑
  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ =
    eq-Eq-ℕ∞↑ Eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ

  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ' : infinity-ℕ∞↑ ＝ x
  eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ' =
    inv eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ
```

### The extended inclusion is double negation dense

```agda
is-double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ :
  is-double-negation-dense-map inclusion-ℕ∞↑-Maybe-ℕ
is-double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ x H =
  H ( inr star ,
      eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ' x
        ( λ n p → H (inl n , inv p)))

double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ : Maybe ℕ ↠¬¬ ℕ∞↑
double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ =
  ( inclusion-ℕ∞↑-Maybe-ℕ , is-double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ)
```

```agda
module _
  {l : Level} {Y : ℕ∞↑ → UU l}
  {f g : (x : ℕ∞↑) → Y x}
  where

  htpy-ℕ∞↑-htpy-ℕ :
    (H : (x : ℕ∞↑) → has-double-negation-stable-equality (Y x)) →
    ((n : ℕ) → f (inclusion-ℕ∞↑-ℕ n) ＝ g (inclusion-ℕ∞↑-ℕ n)) →
    f infinity-ℕ∞↑ ＝ g infinity-ℕ∞↑ →
    f ~ g
  htpy-ℕ∞↑-htpy-ℕ H h h∞ =
    htpy-htpy-double-negation-dense-map
      ( double-negation-dense-inclusion-ℕ∞↑-Maybe-ℕ)
      ( H)
      ( ind-Maybe (h , h∞))
```

### The tight bounds on the image of natural numbers

```agda
refl-leq-ℕ-ℕ∞↑ : (n : ℕ) → inclusion-ℕ∞↑-ℕ n ≤-ℕ∞↑-ℕ n
refl-leq-ℕ-ℕ∞↑ zero-ℕ = refl
refl-leq-ℕ-ℕ∞↑ (succ-ℕ n) = refl-leq-ℕ-ℕ∞↑ n
```

```agda
le-succ-ℕ-ℕ∞↑ : (n : ℕ) → n <-ℕ-ℕ∞↑ (inclusion-ℕ∞↑-ℕ (succ-ℕ n))
le-succ-ℕ-ℕ∞↑ zero-ℕ = refl
le-succ-ℕ-ℕ∞↑ (succ-ℕ n) = le-succ-ℕ-ℕ∞↑ n
```

## References

- [`CoNaturals.GenericConvergentSequence`](https://martinescardo.github.io/TypeTopology/CoNaturals.GenericConvergentSequence.html)
  at TypeTopology {{#cite TypeTopology}}

{{#bibliography}}
