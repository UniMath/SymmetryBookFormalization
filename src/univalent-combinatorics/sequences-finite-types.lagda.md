# Sequences of elements in finite types

```agda
module univalent-combinatorics.sequences-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions-of-values
open import foundation.repetitions-sequences
open import foundation.sequences
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Sequences of elements in finite types must have repetitions. Furthermore, since
equality in finite types is decidable, there must be a first repetition in any
sequence of elements in a finite type.

## Properties

```agda
repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) → repetition-of-values f
repetition-of-values-sequence-Fin k f =
  repetition-of-values-left-factor
    ( is-emb-nat-Fin (succ-ℕ k))
    ( repetition-of-values-Fin-succ-to-Fin k (f ∘ nat-Fin (succ-ℕ k)))

pair-of-distinct-elements-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → pair-of-distinct-elements ℕ
pair-of-distinct-elements-repetition-of-values-sequence-Fin k f =
  pair-of-distinct-elements-repetition-of-values f
    ( repetition-of-values-sequence-Fin k f)

first-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → ℕ
first-repetition-of-values-sequence-Fin k f =
  first-repetition-of-values f (repetition-of-values-sequence-Fin k f)

second-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → ℕ
second-repetition-of-values-sequence-Fin k f =
  second-repetition-of-values f (repetition-of-values-sequence-Fin k f)

distinction-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  first-repetition-of-values-sequence-Fin k f ≠
  second-repetition-of-values-sequence-Fin k f
distinction-repetition-of-values-sequence-Fin k f =
  distinction-repetition-of-values f (repetition-of-values-sequence-Fin k f)

is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  is-repetition-of-values f
    ( pair-of-distinct-elements-repetition-of-values-sequence-Fin k f)
is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Fin k f =
  is-repetition-of-values-repetition-of-values f
    ( repetition-of-values-sequence-Fin k f)

le-first-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) →
  le-ℕ (first-repetition-of-values-sequence-Fin k f) (succ-ℕ k)
le-first-repetition-of-values-sequence-Fin k f =
  strict-upper-bound-nat-Fin
    ( succ-ℕ k)
    ( first-repetition-of-values
      ( f ∘ nat-Fin (succ-ℕ k))
      ( repetition-of-values-le-Fin
        ( succ-ℕ k)
        ( k)
        ( f ∘ nat-Fin (succ-ℕ k))
        ( succ-le-ℕ k)))
```

### Ordered repetitions of values of maps out of the natural numbers

```agda
repetition-of-values-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) → repetition-of-values f
repetition-of-values-nat-to-count e f =
  repetition-of-values-right-factor
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( repetition-of-values-sequence-Fin
      ( number-of-elements-count e)
      ( map-inv-equiv-count e ∘ f))

ordered-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) → ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-sequence-Fin k f =
  ordered-repetition-of-values-repetition-of-values-ℕ f
    (repetition-of-values-sequence-Fin k f)

ordered-repetition-of-values-nat-to-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) →
  ordered-repetition-of-values-ℕ f
ordered-repetition-of-values-nat-to-count e f =
  ordered-repetition-of-values-right-factor-ℕ
    ( is-emb-is-equiv (is-equiv-map-inv-equiv (equiv-count e)))
    ( ordered-repetition-of-values-sequence-Fin
      ( number-of-elements-count e)
      ( map-inv-equiv-count e ∘ f))

minimal-element-repetition-of-values-sequence-Fin :
  (k : ℕ) (f : ℕ → Fin k) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (f y ＝ f x)))
minimal-element-repetition-of-values-sequence-Fin k f =
  well-ordering-principle-ℕ
    ( λ x → Σ ℕ (λ y → (le-ℕ y x) × (Id (f y) (f x))))
    ( λ x →
      is-decidable-strictly-bounded-Σ-ℕ' x
        ( λ y → f y ＝ f x)
        ( λ y → has-decidable-equality-Fin k (f y) (f x)))
    ( u , H , p)
  where
  r = ordered-repetition-of-values-sequence-Fin k f
  u = pr1 (pr1 r)
  v = pr1 (pr2 (pr1 r))
  H = pr2 (pr2 (pr1 r))
  p = pr2 r

minimal-element-repetition-of-values-sequence-count :
  {l : Level} {A : UU l} (e : count A) (f : ℕ → A) →
  minimal-element-ℕ (λ x → Σ ℕ (λ y → (le-ℕ y x) × (f y ＝ f x)))
minimal-element-repetition-of-values-sequence-count (k , e) f =
  ( ( n) ,
    ( ( u) ,
      ( H) ,
      ( is-injective-is-emb (is-emb-is-equiv (is-equiv-map-inv-equiv e)) p)) ,
    ( λ t (v , K , q) → l t (v , K , ap (map-inv-equiv e) q)))
  where
  m = minimal-element-repetition-of-values-sequence-Fin k (map-inv-equiv e ∘ f)
  n = pr1 m
  u = pr1 (pr1 (pr2 m))
  H = pr1 (pr2 (pr1 (pr2 m)))
  p = pr2 (pr2 (pr1 (pr2 m)))
  l = pr2 (pr2 m)
```
