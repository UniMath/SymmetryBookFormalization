# Pisano periods

```agda
module elementary-number-theory.pisano-periods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.repetitions-sequences
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.sequences-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sequence `P : ℕ → ℕ` of **Pisano periods** is the sequence where `P n` is
the period of the Fibonacci sequence modulo `n`. This sequence is listed as
[A001175](https://oeis.org/A001175) in the OEIS.

## Definitions

### The Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
generating-map-fibonacci-pair-Fin k p =
  pair (pr2 p) (add-Fin (succ-ℕ k) (pr2 p) (pr1 p))

inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  pair (add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x)) x

is-section-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id
    ( generating-map-fibonacci-pair-Fin k
      ( inv-generating-map-fibonacci-pair-Fin k p))
    ( p)
is-section-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair refl
    ( ( commutative-add-Fin
        ( succ-ℕ k)
        ( x)
        ( add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x))) ∙
      ( ( associative-add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x) x) ∙
        ( ( ap (add-Fin (succ-ℕ k) y) (left-inverse-law-add-Fin k x)) ∙
          ( right-unit-law-add-Fin k y))))

is-retraction-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id
    ( inv-generating-map-fibonacci-pair-Fin k
      ( generating-map-fibonacci-pair-Fin k p))
    ( p)
is-retraction-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair
    ( ( commutative-add-Fin
        ( succ-ℕ k)
        ( add-Fin (succ-ℕ k) y x)
        ( neg-Fin (succ-ℕ k) y)) ∙
      ( ( inv (associative-add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) y) y x)) ∙
        ( ( ap (λ t → add-Fin (succ-ℕ k) t x) (left-inverse-law-add-Fin k y)) ∙
          ( left-unit-law-add-Fin k x))))
    ( refl)

is-equiv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → is-equiv (generating-map-fibonacci-pair-Fin k)
is-equiv-generating-map-fibonacci-pair-Fin k =
  is-equiv-is-invertible
    ( inv-generating-map-fibonacci-pair-Fin k)
    ( is-section-inv-generating-map-fibonacci-pair-Fin k)
    ( is-retraction-inv-generating-map-fibonacci-pair-Fin k)

fibonacci-pair-Fin :
  (k : ℕ) → ℕ → Fin (succ-ℕ k) × Fin (succ-ℕ k)
fibonacci-pair-Fin k zero-ℕ = pair (zero-Fin k) (one-Fin k)
fibonacci-pair-Fin k (succ-ℕ n) =
  generating-map-fibonacci-pair-Fin k (fibonacci-pair-Fin k n)

compute-fibonacci-pair-Fin :
  (k : ℕ) (n : ℕ) →
  Id
    ( fibonacci-pair-Fin k n)
    ( mod-succ-ℕ k (fibonacci-ℕ n) , mod-succ-ℕ k (fibonacci-ℕ (succ-ℕ n)))
compute-fibonacci-pair-Fin k zero-ℕ = refl
compute-fibonacci-pair-Fin k (succ-ℕ zero-ℕ) =
  ap-binary pair refl (right-unit-law-add-Fin k (one-Fin k))
compute-fibonacci-pair-Fin k (succ-ℕ (succ-ℕ n)) =
  ap-binary pair
    ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
    ( ( ap-binary
        ( add-Fin (succ-ℕ k))
        ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
        ( ap pr1 (compute-fibonacci-pair-Fin k (succ-ℕ n)))) ∙
      ( inv
        ( mod-succ-add-ℕ k
          ( fibonacci-ℕ (succ-ℕ (succ-ℕ n)))
          ( fibonacci-ℕ (succ-ℕ n)))))
```

### Repetitions in the Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
has-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → ordered-repetition-of-values-ℕ (fibonacci-pair-Fin k)
has-ordered-repetition-fibonacci-pair-Fin k =
  ordered-repetition-of-values-nat-to-count
    ( count-product (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
    ( fibonacci-pair-Fin k)

is-ordered-repetition-fibonacci-pair-Fin : ℕ → ℕ → UU lzero
is-ordered-repetition-fibonacci-pair-Fin k x =
  Σ ℕ (λ y → (le-ℕ y x) × (fibonacci-pair-Fin k y ＝ fibonacci-pair-Fin k x))

minimal-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → minimal-element-ℕ (is-ordered-repetition-fibonacci-pair-Fin k)
minimal-ordered-repetition-fibonacci-pair-Fin k =
  minimal-element-repetition-of-values-sequence-count
    ( count-product (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
    ( fibonacci-pair-Fin k)
```

### The Pisano periods

```agda
pisano-period : ℕ → ℕ
pisano-period k = pr1 (minimal-ordered-repetition-fibonacci-pair-Fin k)

is-ordered-repetition-pisano-period :
  (k : ℕ) → is-ordered-repetition-fibonacci-pair-Fin k (pisano-period k)
is-ordered-repetition-pisano-period k =
  pr1 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

is-lower-bound-pisano-period :
  (k : ℕ) →
  is-lower-bound-ℕ
    ( is-ordered-repetition-fibonacci-pair-Fin k)
    ( pisano-period k)
is-lower-bound-pisano-period k =
  pr2 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

cases-is-repetition-of-zero-pisano-period :
  (k x y : ℕ) → Id (pr1 (is-ordered-repetition-pisano-period k)) x →
  Id (pisano-period k) y → is-zero-ℕ x
cases-is-repetition-of-zero-pisano-period k zero-ℕ y p q = refl
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) zero-ℕ p q =
  ex-falso
    ( concatenate-eq-le-eq-ℕ
      ( succ-ℕ x)
      ( pr1 (is-ordered-repetition-pisano-period k))
      ( pisano-period k) zero-ℕ
      ( inv p)
      ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
      ( q))
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) (succ-ℕ y) p q =
  ex-falso
    ( contradiction-leq-ℕ y y (refl-leq-ℕ y)
      ( concatenate-eq-leq-ℕ y (inv q) (is-lower-bound-pisano-period k y R)))
  where
  R : is-ordered-repetition-fibonacci-pair-Fin k y
  R = triple x
        ( concatenate-eq-le-eq-ℕ
          ( succ-ℕ x)
          ( pr1 (is-ordered-repetition-pisano-period k))
          ( pisano-period k)
          ( succ-ℕ y)
          ( inv p)
          ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
          ( q))
        ( is-injective-is-equiv
          ( is-equiv-generating-map-fibonacci-pair-Fin k)
          ( ( ap (fibonacci-pair-Fin k) (inv p)) ∙
            ( ( pr2 (pr2 (is-ordered-repetition-pisano-period k))) ∙
              ( ap (fibonacci-pair-Fin k) q))))

is-repetition-of-zero-pisano-period :
  (k : ℕ) → is-zero-ℕ (pr1 (is-ordered-repetition-pisano-period k))
is-repetition-of-zero-pisano-period k =
  cases-is-repetition-of-zero-pisano-period k
    ( pr1 (is-ordered-repetition-pisano-period k))
    ( pisano-period k)
    ( refl)
    ( refl)

compute-fibonacci-pair-Fin-pisano-period :
  (k : ℕ) →
  Id (fibonacci-pair-Fin k (pisano-period k)) (fibonacci-pair-Fin k zero-ℕ)
compute-fibonacci-pair-Fin-pisano-period k =
  ( inv (pr2 (pr2 (is-ordered-repetition-pisano-period k)))) ∙
  ( ap (fibonacci-pair-Fin k) (is-repetition-of-zero-pisano-period k))
```

## Properties

### Pisano periods are nonzero

```agda
le-zero-pisano-period :
  (k : ℕ) → le-ℕ zero-ℕ (pisano-period k)
le-zero-pisano-period k =
  concatenate-eq-le-ℕ
    ( zero-ℕ)
    ( pr1 (is-ordered-repetition-pisano-period k))
    ( pisano-period k)
    ( inv (is-repetition-of-zero-pisano-period k))
    ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))

is-nonzero-pisano-period :
  (k : ℕ) → is-nonzero-ℕ (pisano-period k)
is-nonzero-pisano-period k p =
  ex-falso
    ( concatenate-le-eq-ℕ 0 (pisano-period k) 0 (le-zero-pisano-period k) p)
```

### `k + 1` divides the Fibonacci number at `pisano-period k`

```agda
div-fibonacci-pisano-period :
  (k : ℕ) → div-ℕ (succ-ℕ k) (fibonacci-ℕ (pisano-period k))
div-fibonacci-pisano-period k =
  div-is-zero-mod-succ-ℕ k
    ( fibonacci-ℕ (pisano-period k))
    ( ( ap pr1 (inv (compute-fibonacci-pair-Fin k (pisano-period k)))) ∙
      ( inv
        ( ap pr1
          { x = fibonacci-pair-Fin k zero-ℕ}
          { y = fibonacci-pair-Fin k (pisano-period k)}
          ( ( ap
              ( fibonacci-pair-Fin k)
              ( inv (is-repetition-of-zero-pisano-period k))) ∙
            ( pr2 (pr2 (is-ordered-repetition-pisano-period k)))))))
```
