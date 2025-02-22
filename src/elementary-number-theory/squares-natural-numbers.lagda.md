# Squares of natural numbers

```agda
module elementary-number-theory.squares-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.pronic-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "square" Disambiguation="natural number" Agda=square-ℕ}} `n²` of
a [natural number](elementary-number-theory.natural-numbers.md) `n` is the
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  n² := n * n
```

of `n` with itself.

## Definition

### Squares of natural numbers

```agda
square-ℕ : ℕ → ℕ
square-ℕ n = n *ℕ n
```

### The predicate of being a square of a natural number

```agda
is-square-ℕ : ℕ → UU lzero
is-square-ℕ n = Σ ℕ (λ x → n ＝ square-ℕ x)
```

### The square root of a square natural number

```agda
square-root-ℕ : (n : ℕ) → is-square-ℕ n → ℕ
square-root-ℕ _ (root , _) = root
```

## Properties

### Squares are second powers

The equality `square-ℕ n ＝ n ^ℕ 2` holds by definition.

```agda
compute-exp-2-ℕ :
  (n : ℕ) → square-ℕ n ＝ n ^ℕ 2
compute-exp-2-ℕ n = refl
```

### Squares of successors

For any `n` we have the equations

```text
  (n + 1)² ＝ (n + 2)n + 1
  (n + 1)² ＝ n² + 2n + 1.
```

```agda
square-succ-ℕ' :
  (n : ℕ) → square-ℕ (succ-ℕ n) ＝ (n +ℕ 2) *ℕ n +ℕ 1
square-succ-ℕ' n =
  right-successor-law-mul-ℕ (succ-ℕ n) n

square-succ-ℕ : (n : ℕ) → square-ℕ (succ-ℕ n) ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 1
square-succ-ℕ n =
  square-succ-ℕ' n ∙ ap succ-ℕ (right-distributive-mul-add-ℕ n 2 n)
```

### Squares of nonzero numbers are nonzero

```agda
is-nonzero-square-is-successor-ℕ :
  (n : ℕ) → is-successor-ℕ n → is-nonzero-ℕ (square-ℕ n)
is-nonzero-square-is-successor-ℕ ._ (n , refl) =
  is-nonzero-is-successor-ℕ ((n +ℕ 2) *ℕ n , square-succ-ℕ' n)

is-nonzero-square-is-nonzero-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-nonzero-ℕ (square-ℕ n)
is-nonzero-square-is-nonzero-ℕ n H =
  is-nonzero-square-is-successor-ℕ n (is-successor-is-nonzero-ℕ H)
```

### Squares of double successors

For any `n` we have `(n + 2)² ＝ n² + 4n + 4`

```agda
square-succ-succ-ℕ :
  (n : ℕ) →
  square-ℕ (succ-ℕ (succ-ℕ n)) ＝ square-ℕ n +ℕ 4 *ℕ n +ℕ 4
square-succ-succ-ℕ n =
  equational-reasoning
  square-ℕ (n +ℕ 2)
  ＝ (n +ℕ 2) *ℕ n +ℕ (n +ℕ 2) *ℕ 2
    by (left-distributive-mul-add-ℕ (n +ℕ 2) n 2)
  ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ (n +ℕ 2)
    by
      ( ap-add-ℕ {(n +ℕ 2) *ℕ n} {(n +ℕ 2) *ℕ 2}
        ( right-distributive-mul-add-ℕ n 2 n)
        ( commutative-mul-ℕ (n +ℕ 2) 2))
  ＝ square-ℕ n +ℕ 2 *ℕ n +ℕ 2 *ℕ n +ℕ 4
    by
      ( ap-add-ℕ {square-ℕ n +ℕ 2 *ℕ n} {2 *ℕ (n +ℕ 2)}
        ( refl)
        ( left-distributive-mul-add-ℕ 2 n 2))
  ＝ square-ℕ n +ℕ (2 *ℕ n +ℕ 2 *ℕ n +ℕ 4)
    by
      associative-add-ℕ (square-ℕ n) (2 *ℕ n) (2 *ℕ n +ℕ 4)
  ＝ square-ℕ n +ℕ 4 *ℕ n +ℕ 4
    by
      ap
        ( add-ℕ (square-ℕ n))
        ( ap
          ( add-ℕ' 4)
          ( ( inv (associative-add-ℕ (2 *ℕ n) (0 +ℕ n) n)) ∙
            ( inv (ap (add-ℕ' n) (associative-add-ℕ (2 *ℕ n) 0 n)))))

square-succ-succ-ℕ' :
  (n : ℕ) → square-ℕ (succ-ℕ (succ-ℕ n)) ＝ square-ℕ n +ℕ 4 *ℕ (n +ℕ 1)
square-succ-succ-ℕ' n =
  square-succ-succ-ℕ n ∙
  ap (square-ℕ n +ℕ_) (inv (left-distributive-mul-add-ℕ 4 n 1))
```

### The square function is order preserving

```agda
preserves-order-square-ℕ :
  (m n : ℕ) → m ≤-ℕ n → square-ℕ m ≤-ℕ square-ℕ n
preserves-order-square-ℕ m n H =
  preserves-order-mul-ℕ m n m n H H

preserves-strict-order-square-ℕ :
  (m n : ℕ) → m <-ℕ n → square-ℕ m <-ℕ square-ℕ n
preserves-strict-order-square-ℕ m n H =
  preserves-strict-order-mul-ℕ m n m n H H
```

### The square function reflects the order on the natural numbers

For any two natural numbers `m` and `n` we have `m² ≤ n² → m ≤ n` and
`m² < n² → m < n`.

```agda
reflects-order-square-ℕ :
  (m n : ℕ) → square-ℕ m ≤-ℕ square-ℕ n → m ≤-ℕ n
reflects-order-square-ℕ m n H =
  leq-not-le-ℕ n m
    ( λ K →
      contradiction-le-ℕ
        ( square-ℕ n)
        ( square-ℕ m)
        ( preserves-strict-order-square-ℕ n m K)
        ( H))

reflects-strict-order-square-ℕ :
  (m n : ℕ) → square-ℕ m <-ℕ square-ℕ n → m <-ℕ n
reflects-strict-order-square-ℕ m n H =
  le-not-leq-ℕ n m
    ( λ K →
      contradiction-le-ℕ
        ( square-ℕ m)
        ( square-ℕ n)
        ( H)
        ( preserves-order-square-ℕ n m K))

le-zero-le-zero-square-ℕ :
  (n : ℕ) → 0 <-ℕ square-ℕ n → 0 <-ℕ n
le-zero-le-zero-square-ℕ n =
  reflects-strict-order-square-ℕ 0 n
```

### The square function is injective

```agda
is-injective-square-ℕ : is-injective square-ℕ
is-injective-square-ℕ {x} {y} p =
  antisymmetric-leq-ℕ x y
    ( reflects-order-square-ℕ x y (leq-eq-ℕ (square-ℕ x) (square-ℕ y) p))
    ( reflects-order-square-ℕ y x (leq-eq-ℕ (square-ℕ y) (square-ℕ x) (inv p)))
```

### Squares distribute over multiplication

```agda
distributive-square-mul-ℕ :
  (m n : ℕ) → square-ℕ (m *ℕ n) ＝ square-ℕ m *ℕ square-ℕ n
distributive-square-mul-ℕ m n =
  interchange-law-mul-mul-ℕ m n m n
```

### The square function is inflationary

```agda
is-inflationary-square-ℕ :
  (n : ℕ) → n ≤-ℕ square-ℕ n
is-inflationary-square-ℕ zero-ℕ =
  star
is-inflationary-square-ℕ (succ-ℕ n) =
  concatenate-eq-leq-ℕ
    ( square-ℕ (succ-ℕ n))
    ( inv (right-unit-law-mul-ℕ (succ-ℕ n)))
    ( preserves-order-right-mul-ℕ (succ-ℕ n) 1 (succ-ℕ n) star)
```

### If a number `n` has a square root, then the square root is at most `n`

```agda
upper-bound-square-root-ℕ :
  (n : ℕ) (H : is-square-ℕ n) → square-root-ℕ n H ≤-ℕ n
upper-bound-square-root-ℕ .(square-ℕ x) (x , refl) =
  is-inflationary-square-ℕ x
```

### Any number greater than 1 is strictly less than its square

```agda
strict-is-inflationary-square-ℕ :
  (n : ℕ) → 1 <-ℕ n → n <-ℕ square-ℕ n
strict-is-inflationary-square-ℕ (succ-ℕ (succ-ℕ zero-ℕ)) H = star
strict-is-inflationary-square-ℕ (succ-ℕ (succ-ℕ (succ-ℕ n))) H =
  concatenate-le-eq-ℕ
    ( n +ℕ 3)
    ( (n +ℕ 4) *ℕ (n +ℕ 2) +ℕ 1)
    ( square-ℕ (n +ℕ 3))
    ( transitive-le-ℕ
      ( n +ℕ 2)
      ( square-ℕ (n +ℕ 2))
      ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
      ( transitive-le-ℕ
        ( square-ℕ (n +ℕ 2))
        ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
        ( square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2) +ℕ (n +ℕ 2))
        ( le-add-succ-ℕ (square-ℕ (n +ℕ 2) +ℕ (n +ℕ 2)) (n +ℕ 1))
        ( le-add-succ-ℕ (square-ℕ (n +ℕ 2)) (n +ℕ 1)))
      ( strict-is-inflationary-square-ℕ (succ-ℕ (succ-ℕ n)) star))
    ( inv (square-succ-ℕ' (n +ℕ 2)))
```

### If a number `n` greater than 1 has a square root, then its square root is strictly smaller than `n`

```agda
strict-upper-bound-square-root-ℕ :
  (n : ℕ) → 1 <-ℕ n → (H : is-square-ℕ n) → square-root-ℕ n H <-ℕ n
strict-upper-bound-square-root-ℕ ._ B (succ-ℕ (succ-ℕ x) , refl) =
  strict-is-inflationary-square-ℕ (x +ℕ 2) star
```

### If `n² ≤ n`, then `n ≤ 1`

```agda
leq-one-leq-square-ℕ :
  (n : ℕ) → square-ℕ n ≤-ℕ n → n ≤-ℕ 1
leq-one-leq-square-ℕ zero-ℕ H = star
leq-one-leq-square-ℕ (succ-ℕ zero-ℕ) H = star
leq-one-leq-square-ℕ (succ-ℕ (succ-ℕ n)) H =
  ex-falso
    ( contradiction-le-ℕ
      ( n +ℕ 2)
      ( square-ℕ (n +ℕ 2))
      ( strict-is-inflationary-square-ℕ (n +ℕ 2) star)
      ( H))
```

### If the square root of a perfect square `n` is greater than or equal to `n`, then `n ≤ 1`

```agda
leq-one-leq-square-root-ℕ :
  (n : ℕ) (H : is-square-ℕ n) → n ≤-ℕ square-root-ℕ n H → n ≤-ℕ 1
leq-one-leq-square-root-ℕ ._ (x , refl) H =
  leq-one-leq-square-ℕ (square-ℕ x) (preserves-order-square-ℕ (square-ℕ x) x H)
```

### The strict inequality `n² < n` never holds

```agda
not-le-square-ℕ :
  (n : ℕ) → ¬ (square-ℕ n <-ℕ n)
not-le-square-ℕ n H =
  contradiction-le-ℕ
    ( square-ℕ n)
    ( n)
    ( H)
    ( is-inflationary-square-ℕ n)
```

### Being a square natural number is decidable

```agda
has-greater-root-ℕ : (n : ℕ) → UU lzero
has-greater-root-ℕ n = Σ ℕ (λ x → (n ≤-ℕ x) × (n ＝ square-ℕ x))

is-decidable-has-greater-root-ℕ :
  (n : ℕ) → is-decidable (has-greater-root-ℕ n)
is-decidable-has-greater-root-ℕ 0 = inl (0 , star , refl)
is-decidable-has-greater-root-ℕ 1 = inl (1 , star , refl)
is-decidable-has-greater-root-ℕ (succ-ℕ (succ-ℕ n)) =
  inr ( λ (x , b , p) → leq-one-leq-square-root-ℕ (n +ℕ 2) (x , p) b)

is-decidable-is-square-ℕ : (n : ℕ) → is-decidable (is-square-ℕ n)
is-decidable-is-square-ℕ n =
  is-decidable-Σ-ℕ n
    ( λ x → n ＝ square-ℕ x)
    ( λ x → has-decidable-equality-ℕ n (square-ℕ x))
    ( is-decidable-has-greater-root-ℕ n)
```

### Any number divides its own square

In other words, the squaring function is inflationary with respect to
divisibility.

```agda
is-inflationary-bounded-div-square-ℕ :
  (n : ℕ) → bounded-div-ℕ n (square-ℕ n)
pr1 (is-inflationary-bounded-div-square-ℕ n) = n
pr1 (pr2 (is-inflationary-bounded-div-square-ℕ n)) = is-inflationary-square-ℕ n
pr2 (pr2 (is-inflationary-bounded-div-square-ℕ n)) = refl

is-inflationary-div-square-ℕ :
  (n : ℕ) → div-ℕ n (square-ℕ n)
is-inflationary-div-square-ℕ n =
  div-bounded-div-ℕ n (square-ℕ n) (is-inflationary-bounded-div-square-ℕ n)
```

### Equivalent characterizations of a number being even in terms of its square

Consider a natural number `n`. The following are equivalent:

- The number `n` is even.
- Its square is even.
- Its square is divisible by 4.

```agda
compute-square-even-number-ℕ :
  (n : ℕ) → square-ℕ (even-number-ℕ n) ＝ 4 *ℕ square-ℕ n
compute-square-even-number-ℕ n =
  distributive-square-mul-ℕ 2 n

div-four-square-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → div-ℕ 4 (square-ℕ n)
pr1 (div-four-square-is-even-ℕ .(m *ℕ 2) (m , refl)) =
  square-ℕ m
pr2 (div-four-square-is-even-ℕ .(m *ℕ 2) (m , refl)) =
  inv (distributive-square-mul-ℕ m 2)

is-even-square-is-even-ℕ :
  (n : ℕ) → is-even-ℕ n → is-even-ℕ (square-ℕ n)
is-even-square-is-even-ℕ .(m *ℕ 2) (m , refl) =
  is-even-div-4-ℕ _ (div-four-square-is-even-ℕ (m *ℕ 2) (m , refl))

is-even-is-even-square-ℕ :
  (n : ℕ) → is-even-ℕ (square-ℕ n) → is-even-ℕ n
is-even-is-even-square-ℕ zero-ℕ H = is-even-zero-ℕ
is-even-is-even-square-ℕ (succ-ℕ zero-ℕ) (zero-ℕ , ())
is-even-is-even-square-ℕ (succ-ℕ zero-ℕ) (succ-ℕ k , ())
is-even-is-even-square-ℕ (succ-ℕ (succ-ℕ n)) (m , p) =
  is-even-succ-succ-is-even-ℕ n
    ( is-even-is-even-square-ℕ n
      ( is-even-left-summand-ℕ
        ( square-ℕ n)
        ( 4 *ℕ n)
        ( is-even-div-4-ℕ (4 *ℕ n) (n , commutative-mul-ℕ n 4))
        ( is-even-left-summand-ℕ
          ( square-ℕ n +ℕ 4 *ℕ n)
          ( 4)
          ( 2 , refl)
          ( m , p ∙ square-succ-succ-ℕ n))))

is-even-div-four-square-ℕ :
  (n : ℕ) → div-ℕ 4 (square-ℕ n) → is-even-ℕ n
is-even-div-four-square-ℕ n H =
  is-even-is-even-square-ℕ n (is-even-div-4-ℕ (square-ℕ n) H)
```

### Equivalent characterizations of a number being odd in terms of its square

Consider a natural number `n`. The following are equivalent:

- The number `n` is odd.
- Its square is odd.
- Its square is congruent to `1` modulo `4`.
- Its square is congruent to `1` modulo `8`.

**Proof.** If `n` is of the form `2k + 1`, then its square is of the form
`4k(k+1) + 1`. Since the number `k(k + 1)` is even, it follows that the square
of an odd number is congruent to `1` modulo `8`. Further more, since squares of
even numbers are even, and hence not congruent to `1` modulo `8`, we get a
logical equivalence.

```agda
square-odd-number-ℕ : ℕ → ℕ
square-odd-number-ℕ n = 4 *ℕ square-ℕ n +ℕ 4 *ℕ n +ℕ 1

square-odd-number-ℕ' : ℕ → ℕ
square-odd-number-ℕ' n = 4 *ℕ (n *ℕ (n +ℕ 1)) +ℕ 1

compute-square-odd-number-ℕ :
  (n : ℕ) → square-ℕ (odd-number-ℕ n) ＝ square-odd-number-ℕ n
compute-square-odd-number-ℕ n =
  square-succ-ℕ (2 *ℕ n) ∙
  ap
    ( succ-ℕ)
    ( ap-add-ℕ
      ( compute-square-even-number-ℕ n)
      ( inv (associative-mul-ℕ 2 2 n)))

compute-square-odd-number-ℕ' :
  (n : ℕ) → square-ℕ (odd-number-ℕ n) ＝ square-odd-number-ℕ' n
compute-square-odd-number-ℕ' n =
  compute-square-odd-number-ℕ n ∙
  inv
    ( ap
      ( succ-ℕ)
      ( ( ap (4 *ℕ_) ( right-successor-law-mul-ℕ n n)) ∙
        ( left-distributive-mul-add-ℕ 4 (square-ℕ n) n)))

compute-distance-to-1-square-odd-number-ℕ :
  (n : ℕ) → dist-ℕ (square-ℕ (odd-number-ℕ n)) 1 ＝ 4 *ℕ (n *ℕ (n +ℕ 1))
compute-distance-to-1-square-odd-number-ℕ n =
  ( ap (λ x → dist-ℕ x 1) (compute-square-odd-number-ℕ' n)) ∙
  ( right-unit-law-dist-ℕ _)

has-odd-expansion-square-has-odd-expansion-ℕ :
  (n : ℕ) → has-odd-expansion-ℕ n → has-odd-expansion-ℕ (square-ℕ n)
pr1 (has-odd-expansion-square-has-odd-expansion-ℕ ._ (k , refl)) =
  2 *ℕ (k *ℕ (k +ℕ 1))
pr2 (has-odd-expansion-square-has-odd-expansion-ℕ ._ (k , refl)) =
  inv
    ( ( compute-square-odd-number-ℕ' k) ∙
      ( ap succ-ℕ (associative-mul-ℕ 2 2 (k *ℕ (k +ℕ 1)))))

is-odd-square-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → is-odd-ℕ (square-ℕ n)
is-odd-square-is-odd-ℕ n H =
  is-odd-has-odd-expansion-ℕ
    ( square-ℕ n)
    ( has-odd-expansion-square-has-odd-expansion-ℕ n
      ( has-odd-expansion-is-odd-ℕ n H))

is-odd-is-odd-square-ℕ :
  (n : ℕ) → is-odd-ℕ (square-ℕ n) → is-odd-ℕ n
is-odd-is-odd-square-ℕ n =
  map-neg (is-even-square-is-even-ℕ n)

is-1-mod-4-square-has-odd-expansion-ℕ :
  (n : ℕ) → has-odd-expansion-ℕ n → square-ℕ n ≡ 1 mod-ℕ 4
is-1-mod-4-square-has-odd-expansion-ℕ ._ (k , refl) =
  tr
    ( div-ℕ 4)
    ( inv (compute-distance-to-1-square-odd-number-ℕ k))
    ( div-mul-ℕ' (k *ℕ (k +ℕ 1)) 4 4 (refl-div-ℕ 4))

is-1-mod-8-square-has-odd-expansion-ℕ :
  (n : ℕ) → has-odd-expansion-ℕ n → square-ℕ n ≡ 1 mod-ℕ 8
is-1-mod-8-square-has-odd-expansion-ℕ ._ (k , refl) =
  tr
    ( div-ℕ 8)
    ( inv (compute-distance-to-1-square-odd-number-ℕ k))
    ( preserves-div-mul-ℕ 4 2 4
      ( k *ℕ (k +ℕ 1))
      ( refl-div-ℕ 4)
      ( is-even-pronic-number-ℕ k))

is-1-mod-8-square-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → square-ℕ n ≡ 1 mod-ℕ 8
is-1-mod-8-square-is-odd-ℕ n H =
  is-1-mod-8-square-has-odd-expansion-ℕ n (has-odd-expansion-is-odd-ℕ n H)
```

### Any two odd squares are congruent modulo `8`

This solves exercise 6 of section 2.1 in {{#cite Andrews94}}.

```agda
cong-8-square-odd-number-ℕ :
  (m n : ℕ) → is-odd-ℕ m → is-odd-ℕ n → square-ℕ m ≡ square-ℕ n mod-ℕ 8
cong-8-square-odd-number-ℕ m n H K =
  transitive-cong-ℕ 8
    ( square-ℕ m)
    ( 1)
    ( square-ℕ n)
    ( symmetric-cong-ℕ 8 (square-ℕ n) 1 (is-1-mod-8-square-is-odd-ℕ n K))
    ( is-1-mod-8-square-is-odd-ℕ m H)
```

### Squaring preserves divisibility

```agda
module _
  (m n : ℕ) (H : div-ℕ m n)
  where

  quotient-div-square-ℕ : ℕ
  quotient-div-square-ℕ = square-ℕ (quotient-div-ℕ m n H)

  upper-bound-quotient-div-square-ℕ :
    quotient-div-square-ℕ ≤-ℕ square-ℕ n
  upper-bound-quotient-div-square-ℕ =
    preserves-order-square-ℕ
      ( quotient-div-ℕ m n H)
      ( n)
      ( upper-bound-quotient-div-ℕ m n H)

  eq-quotient-div-square-ℕ :
    quotient-div-square-ℕ *ℕ square-ℕ m ＝ square-ℕ n
  eq-quotient-div-square-ℕ =
    inv (distributive-square-mul-ℕ (quotient-div-ℕ m n H) m) ∙
    ap square-ℕ (eq-quotient-div-ℕ m n H)

  bounded-div-square-ℕ : bounded-div-ℕ (square-ℕ m) (square-ℕ n)
  pr1 bounded-div-square-ℕ = quotient-div-square-ℕ
  pr1 (pr2 bounded-div-square-ℕ) = upper-bound-quotient-div-square-ℕ
  pr2 (pr2 bounded-div-square-ℕ) = eq-quotient-div-square-ℕ

  preserves-div-square-ℕ : div-ℕ (square-ℕ m) (square-ℕ n)
  pr1 preserves-div-square-ℕ = quotient-div-square-ℕ
  pr2 preserves-div-square-ℕ = eq-quotient-div-square-ℕ

  compute-quotient-div-square-ℕ :
    (K : div-ℕ (square-ℕ m) (square-ℕ n)) →
    quotient-div-ℕ (square-ℕ m) (square-ℕ n) K ＝ quotient-div-square-ℕ
  compute-quotient-div-square-ℕ K =
    compute-quotient-bounded-div-ℕ
      ( refl)
      ( refl)
      ( bounded-div-div-ℕ (square-ℕ m) (square-ℕ n) K)
      ( bounded-div-square-ℕ)
```

### Squares of sums of natural numbers

```agda
square-add-ℕ :
  (m n : ℕ) → square-ℕ (m +ℕ n) ＝ square-ℕ m +ℕ 2 *ℕ (m *ℕ n) +ℕ square-ℕ n
square-add-ℕ m n =
  ( double-distributive-mul-add-ℕ m n m n) ∙
  ( ap
    ( _+ℕ square-ℕ n)
    ( ( associative-add-ℕ (square-ℕ m) (m *ℕ n) (n *ℕ m)) ∙
      ( ap
        ( square-ℕ m +ℕ_)
        ( ( ap (m *ℕ n +ℕ_) (commutative-mul-ℕ n m)) ∙
          ( inv (left-two-law-mul-ℕ (m *ℕ n)))))))
```

### The formula for the distance between squares

The formula for the distance between squares is more commonly known as the
formula for the difference of squares. However, since we prefer using the
distance operation on the natural numbers over the partial difference operation,
we will state and prove the analogous formula using the distance function.

The formula for the difference of squares of integers is formalized in its usual
form.

```agda
distance-of-squares-ℕ' :
  (m n k : ℕ) → m +ℕ k ＝ n →
  dist-ℕ (square-ℕ m) (square-ℕ n) ＝ dist-ℕ m n *ℕ (m +ℕ n)
distance-of-squares-ℕ' m ._ k refl =
  ( ap
    ( dist-ℕ (square-ℕ m))
    ( ( square-add-ℕ m k) ∙
      ( associative-add-ℕ (square-ℕ m) (2 *ℕ (m *ℕ k)) (square-ℕ k)))) ∙
  ( dist-add-ℕ (square-ℕ m) (2 *ℕ (m *ℕ k) +ℕ square-ℕ k)) ∙
  ( ap
    ( _+ℕ square-ℕ k)
    ( inv (associative-mul-ℕ 2 m k) ∙ ap (_*ℕ k) (left-two-law-mul-ℕ m))) ∙
  ( inv (right-distributive-mul-add-ℕ (m +ℕ m) k k)) ∙
  ( ap (_*ℕ k) (associative-add-ℕ m m k)) ∙
  ( commutative-mul-ℕ (m +ℕ (m +ℕ k)) k) ∙
  ( ap (_*ℕ (m +ℕ (m +ℕ k))) (inv (dist-add-ℕ m k)))

abstract
  distance-of-squares-ℕ :
    (m n : ℕ) → dist-ℕ (square-ℕ m) (square-ℕ n) ＝ dist-ℕ m n *ℕ (m +ℕ n)
  distance-of-squares-ℕ m n
    with
    linear-leq-ℕ m n
  ... | inl H =
    distance-of-squares-ℕ' m n
      ( pr1 (subtraction-leq-ℕ m n H))
      ( commutative-add-ℕ m _ ∙ pr2 (subtraction-leq-ℕ m n H))
  ... | inr H =
    ( symmetric-dist-ℕ (square-ℕ m) (square-ℕ n)) ∙
    ( distance-of-squares-ℕ' n m
      ( pr1 (subtraction-leq-ℕ n m H))
      ( commutative-add-ℕ n _ ∙ pr2 (subtraction-leq-ℕ n m H))) ∙
    ( ap-mul-ℕ (symmetric-dist-ℕ n m) (commutative-add-ℕ n m))
```

### The $n$th square is the sum of the first $n$ odd numbers

We show that

$$
  1 + 3 + \cdots + (2n+1) = n^2.
$$

This solves exercise 5 in section 1.2 of {{#cite Andrews94}}.

```agda
sum-of-odd-numbers-ℕ : ℕ → ℕ
sum-of-odd-numbers-ℕ n =
  sum-Fin-ℕ n (λ i → odd-number-ℕ (nat-Fin n i))

compute-sum-of-odd-numbers-ℕ :
  (n : ℕ) → sum-of-odd-numbers-ℕ n ＝ square-ℕ n
compute-sum-of-odd-numbers-ℕ zero-ℕ = refl
compute-sum-of-odd-numbers-ℕ (succ-ℕ zero-ℕ) = refl
compute-sum-of-odd-numbers-ℕ (succ-ℕ (succ-ℕ n)) =
  ( ap
    ( _+ℕ odd-number-ℕ (succ-ℕ n))
    ( compute-sum-of-odd-numbers-ℕ (succ-ℕ n))) ∙
  ( inv (square-succ-ℕ (succ-ℕ n)))
```

## See also

- [Cubes of natural numbers](elementary-number-theory.cubes-natural-numbers.md)
- [Square pyramidal numbers](elementary-number-theory.square-pyramidal-numbers.md)
- [Squares of integers](elementary-number-theory.squares-integers.md)

## References

{{#bibliography}}
