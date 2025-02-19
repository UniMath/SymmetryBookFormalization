# The number of divisors function

```agda
module elementary-number-theory.number-of-divisors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.bounded-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.fixed-points-endofunctions
open import foundation.function-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "number of divisors" Agda=number-of-divisors-ℕ OEIS=A000005 WDID=Q12890701 WD="number of divisors"}}
$\tau(n)$ of a [natural number](elementary-number-theory.natural-numbers.md) $n$
is the number of natural numbers $d \leq n$ that
[divide](elementary-number-theory.divisibility.natural-numbers.md) the number
$n$, i.e.,

$$
  \tau(n) := |\{d \in \mathbb{N} \mid d|n\}|.
$$

The number of divisors function is listed as A000005 in the
[OEIS](literature.oeis.md) {{#cite oeis}}.

## Definitions

### The type of divisors

```agda
decidable-subtype-of-divisors-ℕ :
  (n : ℕ) → decidable-subtype lzero (bounded-ℕ n)
decidable-subtype-of-divisors-ℕ n i =
  bounded-div-ℕ-Decidable-Prop (nat-bounded-ℕ n i) n

divisor-ℕ :
  ℕ → UU lzero
divisor-ℕ n =
  type-decidable-subtype (decidable-subtype-of-divisors-ℕ n)

nat-divisor-ℕ :
  (n : ℕ) → divisor-ℕ n → ℕ
nat-divisor-ℕ n =
  nat-bounded-ℕ n ∘ pr1

bounded-div-divisor-ℕ :
  (n : ℕ) (d : divisor-ℕ n) → bounded-div-ℕ (nat-divisor-ℕ n d) n
bounded-div-divisor-ℕ n =
  pr2

div-divisor-ℕ :
  (n : ℕ) (d : divisor-ℕ n) → div-ℕ (nat-divisor-ℕ n d) n
div-divisor-ℕ n d =
  div-bounded-div-ℕ (nat-divisor-ℕ n d) n (bounded-div-divisor-ℕ n d)

eq-divisor-ℕ :
  (n : ℕ) (x y : divisor-ℕ n) →
  nat-divisor-ℕ n x ＝ nat-divisor-ℕ n y → x ＝ y
eq-divisor-ℕ n x y p =
  eq-type-subtype
    ( λ i → bounded-div-ℕ-Prop (nat-bounded-ℕ n i) n)
    ( eq-type-subtype
      ( λ x → leq-ℕ-Prop x n)
      ( p))

is-set-divisor-ℕ :
  (n : ℕ) → is-set (divisor-ℕ n)
is-set-divisor-ℕ n =
  is-set-type-subtype
    ( λ i → bounded-div-ℕ-Prop (nat-bounded-ℕ n i) n)
    ( is-set-bounded-ℕ n)

divisor-ℕ-Set :
  (n : ℕ) → Set lzero
pr1 (divisor-ℕ-Set n) = divisor-ℕ n
pr2 (divisor-ℕ-Set n) = is-set-divisor-ℕ n

upper-bound-divisor-ℕ :
  (n : ℕ) (d : divisor-ℕ n) → nat-divisor-ℕ n d ≤-ℕ n
upper-bound-divisor-ℕ n =
  upper-bound-nat-bounded-ℕ n ∘ pr1

nat-quotient-divisor-ℕ :
  (n : ℕ) → divisor-ℕ n → ℕ
nat-quotient-divisor-ℕ n (d , H) =
  quotient-bounded-div-ℕ (nat-bounded-ℕ n d) n H

upper-bound-quotient-divisor-ℕ :
  (n : ℕ) (d : divisor-ℕ n) → nat-quotient-divisor-ℕ n d ≤-ℕ n
upper-bound-quotient-divisor-ℕ n (d , H) =
  upper-bound-quotient-bounded-div-ℕ (nat-bounded-ℕ n d) n H

eq-quotient-divisor-ℕ :
  (n : ℕ) (d : divisor-ℕ n) →
  nat-quotient-divisor-ℕ n d *ℕ nat-divisor-ℕ n d ＝ n
eq-quotient-divisor-ℕ n d =
  eq-quotient-bounded-div-ℕ (nat-divisor-ℕ n d) n (bounded-div-divisor-ℕ n d)

eq-quotient-divisor-ℕ' :
  (n : ℕ) (d : divisor-ℕ n) →
  nat-divisor-ℕ n d *ℕ nat-quotient-divisor-ℕ n d ＝ n
eq-quotient-divisor-ℕ' n d =
  eq-quotient-bounded-div-ℕ' (nat-divisor-ℕ n d) n (bounded-div-divisor-ℕ n d)

quotient-divisor-ℕ :
  (n : ℕ) → divisor-ℕ n → divisor-ℕ n
pr1 (pr1 (quotient-divisor-ℕ n d)) =
  nat-quotient-divisor-ℕ n d
pr2 (pr1 (quotient-divisor-ℕ n d)) =
  upper-bound-quotient-divisor-ℕ n d
pr1 (pr2 (quotient-divisor-ℕ n d)) =
  nat-divisor-ℕ n d
pr1 (pr2 (pr2 (quotient-divisor-ℕ n d))) =
  upper-bound-divisor-ℕ n d
pr2 (pr2 (pr2 (quotient-divisor-ℕ n d))) =
  eq-quotient-divisor-ℕ' n d
```

### The number of divisors function

Note that the entry `number-of-elements-decidable-subtype` refers to
`count-decidable-subtype'`, which is `abstract` and therefore doesn't compute.

```agda
count-divisor-ℕ :
  (n : ℕ) → count (divisor-ℕ n)
count-divisor-ℕ n =
  count-decidable-subtype
    ( decidable-subtype-of-divisors-ℕ n)
    ( count-bounded-ℕ n)

number-of-divisors-ℕ : ℕ → ℕ
number-of-divisors-ℕ n =
  number-of-elements-decidable-subtype
    ( decidable-subtype-of-divisors-ℕ n)
    ( count-bounded-ℕ n)
```

### Involution on the type of divisors

For every natural number `n : ℕ`, the map `d ↦ n/d` mapping a divisor of `n` to
its quotient is an involution. This operation has a fixed point precisely when
`n` is a [square number](elementary-number-theory.square-natural-numbers.md).

```agda
is-involution-quotient-divisor-ℕ :
  (n : ℕ) → is-involution (quotient-divisor-ℕ n)
is-involution-quotient-divisor-ℕ n d =
  eq-divisor-ℕ n (quotient-divisor-ℕ n (quotient-divisor-ℕ n d)) d refl
```

### The involution on the type of divisors of `n` has a fixed point if and only if `n` is a square number

```agda
is-square-has-fixed-point-quotient-divisor-ℕ :
  (n : ℕ) → fixed-point (quotient-divisor-ℕ n) → is-square-ℕ n
pr1 (is-square-has-fixed-point-quotient-divisor-ℕ n (d , p)) =
  nat-divisor-ℕ n d
pr2 (is-square-has-fixed-point-quotient-divisor-ℕ n (d , p)) =
  ( inv (eq-quotient-divisor-ℕ n d)) ∙
  ( ap (_*ℕ nat-divisor-ℕ n d) (ap (nat-divisor-ℕ n) p))

square-root-divisor-is-square-ℕ :
  (n : ℕ) (H : is-square-ℕ n) → divisor-ℕ n
square-root-divisor-is-square-ℕ ._ (n , refl) =
  ( ( n , is-inflationary-square-ℕ n) ,
    ( is-inflationary-bounded-div-square-ℕ n))

is-fixed-point-square-root-divisor-is-square-ℕ :
  (n : ℕ) (H : is-square-ℕ n) →
  quotient-divisor-ℕ n (square-root-divisor-is-square-ℕ n H) ＝
  square-root-divisor-is-square-ℕ n H
is-fixed-point-square-root-divisor-is-square-ℕ ._ H@(n , refl) =
  eq-divisor-ℕ
    ( square-ℕ n)
    ( quotient-divisor-ℕ _ (square-root-divisor-is-square-ℕ _ H))
    ( square-root-divisor-is-square-ℕ _ H)
    ( refl)

has-fixed-point-quotient-divisor-is-square-ℕ :
  (n : ℕ) → is-square-ℕ n → fixed-point (quotient-divisor-ℕ n)
pr1 (has-fixed-point-quotient-divisor-is-square-ℕ n H) =
  square-root-divisor-is-square-ℕ n H
pr2 (has-fixed-point-quotient-divisor-is-square-ℕ n H) =
  is-fixed-point-square-root-divisor-is-square-ℕ n H
```

### The type of fixed points of the involution on the type of divisors is a proposition

This essentially claims that only the square root of a square can be the fixed
point of the involution on the type of divisors.

```agda
all-elements-equal-fixed-point-quotient-divisor-ℕ :
  (n : ℕ) → all-elements-equal (fixed-point (quotient-divisor-ℕ n))
all-elements-equal-fixed-point-quotient-divisor-ℕ n (x , p) (y , q) =
  eq-type-subtype
    ( λ d → Id-Prop (divisor-ℕ-Set n) (quotient-divisor-ℕ n d) d)
    ( eq-divisor-ℕ n x y
      ( is-injective-square-ℕ
        ( ( ap (nat-divisor-ℕ n x *ℕ_) (ap (nat-divisor-ℕ n) (inv p))) ∙
          ( eq-quotient-divisor-ℕ' n x) ∙
          ( inv (eq-quotient-divisor-ℕ' n y)) ∙
          ( ap (nat-divisor-ℕ n y *ℕ_) (ap (nat-divisor-ℕ n) q)))))

is-prop-fixed-point-quotient-divisor-ℕ :
  (n : ℕ) → is-prop (fixed-point (quotient-divisor-ℕ n))
is-prop-fixed-point-quotient-divisor-ℕ n =
  is-prop-all-elements-equal
    ( all-elements-equal-fixed-point-quotient-divisor-ℕ n)
```

## Remarks

In the properties above we have shown that the quotient operation on the type of
divisors of any natural number $n$ is an involution with at most one fixed
point, and it has a fixed point if and only if $n$ is square. This implies that
the number of divisors is odd if and only if $n$ is a square. However, in the
agda-unimath library we don't have the appropriate infrastructure yet for
counting the elements of types with involutions. The conclusion that the number
of divisors of $n$ is odd if and only if $n$ is a square will be formalized in
the future.
