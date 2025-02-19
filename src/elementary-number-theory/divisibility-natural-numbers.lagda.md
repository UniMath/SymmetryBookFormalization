# Divisibility of natural numbers

```agda
module elementary-number-theory.divisibility-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.decidable-types
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

On this page we define the
{{#concept "divisibility" Disambiguation="natural numbers" Agda=div-ℕ WD="divisibility" WDID=Q5284415}}
relation on the [natural numbers](elementary-number-theory.natural-numbers.md).
A natural number `m` is said to **divide** a natural number `n` if there exists
a natural number `k` equipped with an
[identification](foundation-core.identifications.md) `km ＝ n`. Using the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory, we express divisibility as follows:

```text
  div-ℕ m n := Σ (k : ℕ), k *ℕ m ＝ n.
```

If `n` is a
[nonzero natural number](elementary-number-theory.nonzero-natural-numbers.md),
then the type `div-ℕ m n` is always a
[proposition](foundation-core.propositions.md) in the sense that the type
`div-ℕ m n` contains at most one element.

The divisibility relation is
[logically equivalent](foundation.logical-equivalences.md), though not
[equivalent](foundation-core.equivalences.md), to the
[bounded divisibility relation](elementary-number-theory.bounded-divisibility-natural-numbers.md),
which is defined by

```text
  bounded-div-ℕ m n := Σ (k : ℕ), (k ≤ n) × (k *ℕ m ＝ n).
```

The discrepancy between divisibility and bounded divisibility is manifested at
`(0 , 0)`. Note that `div-ℕ 0 0 ≃ ℕ`, while `bounded-div-ℕ 0 0` is
[contractible](foundation-core.contractible-types.md). For all other values we
have `div-ℕ m n ≃ bounded-div-ℕ m n`.

When a natural number
`n is divisible by a natural number `m`, with an element `H : div-ℕ m
n`, then we define the {{#concept "quotient" Disambiguation="divisibility of natural numbers" Agda=quotient-div-ℕ}} to be the unique number `q
≤ n`such that`q \* m ＝ n`.

## Definitions

### The divisibility relation on the natural numbers

We introduce the divisibility relation on the natural numbers, and some
infrastructure.

**Note:** Perhaps a more natural name for `pr1-div-ℕ`, the number `q` such that
`q * d ＝ n`, would be `quotient-div-ℕ`. However, since the divisibility
relation is not always a proposition, the quotient could have some undesirable
properties. Later in this file, we will define `quotient-div-ℕ` to the the
quotient of the bounded divisibility relation, which is logically equivalent to
the divisibility relation.

```agda
module _
  (m n : ℕ)
  where

  div-ℕ : UU lzero
  div-ℕ = Σ ℕ (λ k → k *ℕ m ＝ n)

  pr1-div-ℕ : div-ℕ → ℕ
  pr1-div-ℕ = pr1

  eq-pr1-div-ℕ : (H : div-ℕ) → pr1-div-ℕ H *ℕ m ＝ n
  eq-pr1-div-ℕ = pr2

  eq-pr1-div-ℕ' : (H : div-ℕ) → m *ℕ pr1-div-ℕ H ＝ n
  eq-pr1-div-ℕ' H =
    commutative-mul-ℕ m (pr1-div-ℕ H) ∙ eq-pr1-div-ℕ H

  div-bounded-div-ℕ : bounded-div-ℕ m n → div-ℕ
  pr1 (div-bounded-div-ℕ H) = quotient-bounded-div-ℕ m n H
  pr2 (div-bounded-div-ℕ H) = eq-quotient-bounded-div-ℕ m n H

concatenate-eq-div-ℕ :
  {x y z : ℕ} → x ＝ y → div-ℕ y z → div-ℕ x z
concatenate-eq-div-ℕ refl p = p

concatenate-div-eq-ℕ :
  {x y z : ℕ} → div-ℕ x y → y ＝ z → div-ℕ x z
concatenate-div-eq-ℕ p refl = p

concatenate-eq-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → div-ℕ y z → z ＝ w → div-ℕ x w
concatenate-eq-div-eq-ℕ refl p refl = p
```

### The predicate of being a divisor of a natural number

```agda
is-divisor-ℕ : ℕ → ℕ → UU lzero
is-divisor-ℕ n x = div-ℕ x n
```

## Properties

### Divisibility and bounded divisibility are logically equivalent

#### If `n` is divisible by a number `m` with proof of divisibility `(q , p)`, then `n` is divisible by the number `q`.

```agda
div-pr1-div-ℕ :
  (m n : ℕ) (H : div-ℕ m n) → div-ℕ (pr1-div-ℕ m n H) n
pr1 (div-pr1-div-ℕ m n (u , p)) = m
pr2 (div-pr1-div-ℕ m n (u , p)) = commutative-mul-ℕ m u ∙ p
```

#### If `x` is nonzero and `d | x`, then `d ≤ x`

```agda
leq-div-succ-ℕ : (d x : ℕ) → div-ℕ d (succ-ℕ x) → leq-ℕ d (succ-ℕ x)
leq-div-succ-ℕ d x (succ-ℕ k , p) =
  concatenate-leq-eq-ℕ d (leq-mul-ℕ' k d) p

leq-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → leq-ℕ d x
leq-div-ℕ d x f H with is-successor-is-nonzero-ℕ f
... | (y , refl) = leq-div-succ-ℕ d y H

leq-pr1-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → leq-ℕ (pr1-div-ℕ d x H) x
leq-pr1-div-ℕ d x f H =
  leq-div-ℕ (pr1-div-ℕ d x H) x f (div-pr1-div-ℕ d x H)
```

#### The logical equivalence of divisibility and bounded divisibility

```agda
bounded-div-div-ℕ : (m n : ℕ) → div-ℕ m n → bounded-div-ℕ m n
bounded-div-div-ℕ m zero-ℕ (q , p) = (0 , refl-leq-ℕ 0 , left-zero-law-mul-ℕ m)
bounded-div-div-ℕ m (succ-ℕ n) (q , p) =
  ( q , leq-pr1-div-ℕ m (succ-ℕ n) (is-nonzero-succ-ℕ n) (q , p) , p)

logical-equivalence-bounded-div-div-ℕ :
  (m n : ℕ) → bounded-div-ℕ m n ↔ div-ℕ m n
pr1 (logical-equivalence-bounded-div-div-ℕ m n) =
  div-bounded-div-ℕ m n
pr2 (logical-equivalence-bounded-div-div-ℕ m n) =
  bounded-div-div-ℕ m n
```

#### The quotient of a natural number by a number it is divisible by

```agda
module _
  (m n : ℕ)
  where

  quotient-div-ℕ : div-ℕ m n → ℕ
  quotient-div-ℕ H =
    quotient-bounded-div-ℕ m n (bounded-div-div-ℕ m n H)

  eq-quotient-div-ℕ : (H : div-ℕ m n) → quotient-div-ℕ H *ℕ m ＝ n
  eq-quotient-div-ℕ H =
    eq-quotient-bounded-div-ℕ m n (bounded-div-div-ℕ m n H)

  eq-quotient-div-ℕ' : (H : div-ℕ m n) → m *ℕ quotient-div-ℕ H ＝ n
  eq-quotient-div-ℕ' H =
    eq-quotient-bounded-div-ℕ' m n (bounded-div-div-ℕ m n H)

  upper-bound-quotient-div-ℕ :
    (H : div-ℕ m n) → quotient-div-ℕ H ≤-ℕ n
  upper-bound-quotient-div-ℕ H =
    upper-bound-quotient-bounded-div-ℕ m n (bounded-div-div-ℕ m n H)

  div-quotient-div-ℕ :
    (H : div-ℕ m n) → div-ℕ (quotient-div-ℕ H) n
  div-quotient-div-ℕ H =
    div-bounded-div-ℕ
      ( quotient-div-ℕ H)
      ( n)
      ( bounded-div-quotient-bounded-div-ℕ m n (bounded-div-div-ℕ m n H))
```

### The quotient by divisibility of two equal dividends by two equal divisors are equal

```agda
compute-quotient-div-ℕ :
  {m m' n n' : ℕ} (q : m ＝ m') (p : n ＝ n')
  (H : div-ℕ m n) (K : div-ℕ m' n') →
  quotient-div-ℕ m n H ＝ quotient-div-ℕ m' n' K
compute-quotient-div-ℕ q p H K =
  compute-quotient-bounded-div-ℕ q p
    ( bounded-div-div-ℕ _ _ H)
    ( bounded-div-div-ℕ _ _ K)

compute-quotient-div-is-nonzero-dividend-ℕ :
  {m m' n n' : ℕ} (q : m ＝ m') (p : n ＝ n')
  (H : div-ℕ m n) (K : div-ℕ m' n') →
  is-nonzero-ℕ n' → quotient-div-ℕ m n H ＝ pr1 K
compute-quotient-div-is-nonzero-dividend-ℕ {m} {m'} {n} {zero-ℕ} q p H K f =
  ex-falso (f refl)
compute-quotient-div-is-nonzero-dividend-ℕ {m} {m'} {n} {succ-ℕ n'} q p H K f =
  compute-quotient-div-ℕ q p H K

compute-quotient-div-is-nonzero-divisor-ℕ :
  {m m' n n' : ℕ} (q : m ＝ m') (p : n ＝ n')
  (H : div-ℕ m n) (K : div-ℕ m' n') →
  is-nonzero-ℕ m' → quotient-div-ℕ m n H ＝ pr1 K
compute-quotient-div-is-nonzero-divisor-ℕ {m} {zero-ℕ} {n} {n'} q p H K f =
  ex-falso (f refl)
compute-quotient-div-is-nonzero-divisor-ℕ
  {m} {succ-ℕ m'} {n} {zero-ℕ} q p H (zero-ℕ , K) f =
  is-zero-leq-zero-ℕ
    ( quotient-div-ℕ m n H)
    ( concatenate-leq-eq-ℕ
      ( quotient-div-ℕ m n H)
      ( upper-bound-quotient-div-ℕ m n H)
      ( p))
compute-quotient-div-is-nonzero-divisor-ℕ
  {m} {succ-ℕ m'} {n} {succ-ℕ n'} q p H K f =
  compute-quotient-div-is-nonzero-dividend-ℕ q p H K (is-nonzero-succ-ℕ n')
```

### The quotients of a natural number `n` by two natural numbers `c` and `d` are equal if `c` and `d` are equal

Since the quotient is defined in terms of explicit proofs of divisibility, we
assume arbitrary proofs of dibisibility on both sides.

```agda
eq-quotient-div-eq-divisor-ℕ :
  (c d n : ℕ) → is-nonzero-ℕ c → c ＝ d → (H : div-ℕ c n) (I : div-ℕ d n) →
  pr1-div-ℕ c n H ＝ pr1-div-ℕ d n I
eq-quotient-div-eq-divisor-ℕ c d n N p H I =
  is-injective-left-mul-ℕ c N
    ( tr
      ( λ x → c *ℕ pr1-div-ℕ c n H ＝ x *ℕ pr1-div-ℕ d n I)
      ( inv p)
      ( commutative-mul-ℕ c (pr1-div-ℕ c n H) ∙
        eq-pr1-div-ℕ c n H ∙
        inv (eq-pr1-div-ℕ d n I) ∙
        commutative-mul-ℕ (pr1-div-ℕ d n I) d))
```

### If two natural numbers are equal and one is divisible by a number `d`, then the other is divisible by `d` and their quotients are the same

The first part of the claim was proven above. Since the quotient is defined in
terms of explicit proofs of divisibility, we assume arbitrary proofs of
dibisibility on both sides.

```agda
eq-quotient-div-eq-is-nonzero-divisor-ℕ :
  {d m n : ℕ} → is-nonzero-ℕ d → m ＝ n → (H : div-ℕ d m) (K : div-ℕ d n) →
  quotient-div-ℕ d m H ＝ quotient-div-ℕ d n K
eq-quotient-div-eq-is-nonzero-divisor-ℕ N refl H K =
  is-injective-right-mul-ℕ _ N
    ( eq-quotient-div-ℕ _ _ H ∙ inv (eq-quotient-div-ℕ _ _ K))

eq-quotient-div-eq-is-nonzero-ℕ :
  {d m n : ℕ} → is-nonzero-ℕ m → m ＝ n → (H : div-ℕ d m) (K : div-ℕ d n) →
  quotient-div-ℕ d m H ＝ quotient-div-ℕ d n K
eq-quotient-div-eq-is-nonzero-ℕ {zero-ℕ} N refl H K =
  ex-falso
    ( N
      ( inv (eq-quotient-div-ℕ _ _ H) ∙
        right-zero-law-mul-ℕ (quotient-div-ℕ _ _ H)))
eq-quotient-div-eq-is-nonzero-ℕ {succ-ℕ d} N refl H K =
  eq-quotient-div-eq-is-nonzero-divisor-ℕ
    ( is-nonzero-succ-ℕ d) refl H K
```

### The divisibility relation is a partial order on the natural numbers

The [poset](order-theory.posets.md) of natural numbers ordered by divisibility
is defined in
[`elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility`](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

```agda
refl-div-ℕ : is-reflexive div-ℕ
pr1 (refl-div-ℕ x) = 1
pr2 (refl-div-ℕ x) = left-unit-law-mul-ℕ x

div-eq-ℕ : (x y : ℕ) → x ＝ y → div-ℕ x y
div-eq-ℕ x .x refl = refl-div-ℕ x

neq-neg-div-ℕ : (x y : ℕ) → ¬ div-ℕ x y → x ≠ y
neq-neg-div-ℕ x y H p = H (div-eq-ℕ x y p)

antisymmetric-div-ℕ : is-antisymmetric div-ℕ
antisymmetric-div-ℕ zero-ℕ zero-ℕ H K = refl
antisymmetric-div-ℕ zero-ℕ (succ-ℕ y) (k , p) K =
  inv (right-zero-law-mul-ℕ k) ∙ p
antisymmetric-div-ℕ (succ-ℕ x) zero-ℕ H (l , q) =
  inv q ∙ right-zero-law-mul-ℕ l
antisymmetric-div-ℕ (succ-ℕ x) (succ-ℕ y) (k , p) (l , q) =
  ( inv (left-unit-law-mul-ℕ (succ-ℕ x))) ∙
  ( ( ap
      ( _*ℕ (succ-ℕ x))
      ( inv
        ( is-one-right-is-one-mul-ℕ l k
          ( is-one-is-left-unit-mul-ℕ (l *ℕ k) x
            ( ( associative-mul-ℕ l k (succ-ℕ x)) ∙
              ( ap (l *ℕ_) p ∙ q)))))) ∙
    ( p))

transitive-div-ℕ : is-transitive div-ℕ
pr1 (transitive-div-ℕ x y z (l , q) (k , p)) = l *ℕ k
pr2 (transitive-div-ℕ x y z (l , q) (k , p)) =
  associative-mul-ℕ l k x ∙ (ap (l *ℕ_) p ∙ q)
```

### `1` divides any number

```agda
div-one-ℕ :
  (x : ℕ) → div-ℕ 1 x
pr1 (div-one-ℕ x) = x
pr2 (div-one-ℕ x) = right-unit-law-mul-ℕ x

div-is-one-ℕ :
  (k x : ℕ) → is-one-ℕ k → div-ℕ k x
div-is-one-ℕ .1 x refl = div-one-ℕ x
```

### `x | 1` implies `x ＝ 1`

```agda
is-one-div-one-ℕ : (x : ℕ) → div-ℕ x 1 → is-one-ℕ x
is-one-div-one-ℕ x H = antisymmetric-div-ℕ x 1 H (div-one-ℕ x)
```

### Any number divides `0`

```agda
div-zero-ℕ :
  (k : ℕ) → div-ℕ k 0
pr1 (div-zero-ℕ k) = 0
pr2 (div-zero-ℕ k) = left-zero-law-mul-ℕ k

div-is-zero-ℕ :
  (k x : ℕ) → is-zero-ℕ x → div-ℕ k x
div-is-zero-ℕ k .zero-ℕ refl = div-zero-ℕ k
```

### `0 | x` implies `x = 0`

```agda
is-zero-div-zero-ℕ : (x : ℕ) → div-ℕ zero-ℕ x → is-zero-ℕ x
is-zero-div-zero-ℕ x H = antisymmetric-div-ℕ x zero-ℕ (div-zero-ℕ x) H

is-zero-is-zero-div-ℕ : (x y : ℕ) → div-ℕ x y → is-zero-ℕ x → is-zero-ℕ y
is-zero-is-zero-div-ℕ .zero-ℕ y d refl = is-zero-div-zero-ℕ y d

is-zero-quotient-div-is-zero-dividend-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → is-zero-ℕ y → is-zero-ℕ (quotient-div-ℕ x y H)
is-zero-quotient-div-is-zero-dividend-ℕ x ._ H refl =
  is-zero-leq-zero-ℕ
    ( quotient-div-ℕ x 0 H)
    ( upper-bound-quotient-div-ℕ x 0 H)

is-zero-quotient-div-is-zero-divisor-ℕ :
  (x y : ℕ) (H : div-ℕ x y) → is-zero-ℕ x → is-zero-ℕ (quotient-div-ℕ x y H)
is-zero-quotient-div-is-zero-divisor-ℕ x y H p =
  is-zero-quotient-div-is-zero-dividend-ℕ x y H
    ( ( inv (eq-quotient-div-ℕ x y H)) ∙
      ( ap (quotient-div-ℕ x y H *ℕ_) p) ∙
      ( right-zero-law-mul-ℕ (quotient-div-ℕ x y H)))
```

### Any divisor of a nonzero number is nonzero

```agda
is-nonzero-div-ℕ :
  (d x : ℕ) → div-ℕ d x → is-nonzero-ℕ x → is-nonzero-ℕ d
is-nonzero-div-ℕ .zero-ℕ x H K refl = K (is-zero-div-zero-ℕ x H)
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕ :
  {d x : ℕ} (H : div-ℕ d x) →
  is-nonzero-ℕ x → is-nonzero-ℕ (quotient-div-ℕ d x H)
is-nonzero-quotient-div-ℕ {d} {x} H K =
  is-nonzero-quotient-bounded-div-ℕ d x K (bounded-div-div-ℕ d x H)
```

### Any divisor of a number at least `1` is at least `1`

```agda
leq-one-div-ℕ :
  (d x : ℕ) → div-ℕ d x → leq-ℕ 1 x → leq-ℕ 1 d
leq-one-div-ℕ d x H L =
  leq-one-is-nonzero-ℕ d (is-nonzero-div-ℕ d x H (is-nonzero-leq-one-ℕ x L))
```

### If `d` divides a number `1 ≤ x`, then `1 ≤ x/d`

```agda
leq-one-quotient-div-ℕ :
  (d x : ℕ) (H : div-ℕ d x) → leq-ℕ 1 x → leq-ℕ 1 (quotient-div-ℕ d x H)
leq-one-quotient-div-ℕ d x H K =
  leq-one-div-ℕ
    ( quotient-div-ℕ d x H)
    ( x)
    ( div-quotient-div-ℕ d x H)
    ( K)

leq-one-quotient-div-is-nonzero-ℕ :
  (d x : ℕ) (H : div-ℕ d x) → is-nonzero-ℕ x → leq-ℕ 1 (quotient-div-ℕ d x H)
leq-one-quotient-div-is-nonzero-ℕ d x H N =
  leq-one-quotient-div-ℕ d x H (leq-one-is-nonzero-ℕ x N)
```

### If `x < d` and `d | x`, then `x` must be `0`

```agda
is-zero-div-ℕ :
  (d x : ℕ) → le-ℕ x d → div-ℕ d x → is-zero-ℕ x
is-zero-div-ℕ d zero-ℕ H D = refl
is-zero-div-ℕ d (succ-ℕ x) H (succ-ℕ k , p) =
  ex-falso
    ( contradiction-le-ℕ
      ( succ-ℕ x) d H
      ( concatenate-leq-eq-ℕ d
        ( leq-add-ℕ' d (k *ℕ d)) p))
```

### `a/a ＝ 1`

```agda
is-idempotent-quotient-div-ℕ :
  (a : ℕ) → is-nonzero-ℕ a → (H : div-ℕ a a) → is-one-ℕ (quotient-div-ℕ a a H)
is-idempotent-quotient-div-ℕ zero-ℕ nz (u , p) = ex-falso (nz refl)
is-idempotent-quotient-div-ℕ (succ-ℕ a) nz (u , p) =
  is-one-is-left-unit-mul-ℕ u a p
```

### If `x` is nonzero, if `d | x` and `d ≠ x`, then `d < x`

```agda
le-div-succ-ℕ :
  (d x : ℕ) → div-ℕ d (succ-ℕ x) → d ≠ succ-ℕ x → le-ℕ d (succ-ℕ x)
le-div-succ-ℕ d x H f = le-leq-neq-ℕ (leq-div-succ-ℕ d x H) f

le-div-ℕ : (d x : ℕ) → is-nonzero-ℕ x → div-ℕ d x → d ≠ x → le-ℕ d x
le-div-ℕ d x H K f = le-leq-neq-ℕ (leq-div-ℕ d x H K) f
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (k *ℕ y)
pr1 (div-mul-ℕ k x y H) = k *ℕ quotient-div-ℕ x y H
pr2 (div-mul-ℕ k x y H) =
  associative-mul-ℕ k (quotient-div-ℕ x y H) x ∙
  ap (k *ℕ_) (eq-quotient-div-ℕ x y H)

div-mul-ℕ' :
  (k x y : ℕ) → div-ℕ x y → div-ℕ x (y *ℕ k)
div-mul-ℕ' k x y H =
  tr (div-ℕ x) (commutative-mul-ℕ k y) (div-mul-ℕ k x y H)

compute-quotient-div-mul-ℕ :
  (k x y : ℕ) (H : div-ℕ x y) (K : div-ℕ x (k *ℕ y)) →
  quotient-div-ℕ x (k *ℕ y) K ＝ k *ℕ quotient-div-ℕ x y H
compute-quotient-div-mul-ℕ k zero-ℕ y H K =
  is-zero-quotient-div-is-zero-divisor-ℕ 0 (k *ℕ y) K refl ∙
  inv (right-zero-law-mul-ℕ k) ∙
  ap (k *ℕ_) (inv (is-zero-quotient-div-is-zero-divisor-ℕ 0 y H refl))
compute-quotient-div-mul-ℕ k (succ-ℕ x) y H K =
  compute-quotient-div-is-nonzero-divisor-ℕ
    ( refl)
    ( refl)
    ( K)
    ( div-mul-ℕ k (succ-ℕ x) y H)
    ( is-nonzero-succ-ℕ x)

compute-quotient-div-mul-ℕ' :
  (k x y : ℕ) (H : div-ℕ x y) (K : div-ℕ x (y *ℕ k)) →
  quotient-div-ℕ x (y *ℕ k) K ＝ quotient-div-ℕ x y H *ℕ k
compute-quotient-div-mul-ℕ' k x y H K =
  ( compute-quotient-div-ℕ refl
    ( commutative-mul-ℕ y k)
    ( K)
    ( concatenate-div-eq-ℕ K (commutative-mul-ℕ y k))) ∙
  ( compute-quotient-div-mul-ℕ k x y H
    ( concatenate-div-eq-ℕ K (commutative-mul-ℕ y k))) ∙
  ( commutative-mul-ℕ k (quotient-div-ℕ x y H))
```

### Divisibility is decidable

```agda
is-decidable-div-ℕ :
  (m n : ℕ) → is-decidable (div-ℕ m n)
is-decidable-div-ℕ m n =
  is-decidable-iff
    ( div-bounded-div-ℕ m n)
    ( bounded-div-div-ℕ m n)
    ( is-decidable-bounded-div-ℕ m n)
```

### Divisibility is a property except at `(0,0)`

```agda
is-prop-div-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k + is-nonzero-ℕ x → is-prop (div-ℕ k x)
is-prop-div-ℕ k x (inl H) = is-prop-map-is-emb (is-emb-right-mul-ℕ k H) x
is-prop-div-ℕ zero-ℕ x (inr H) =
  is-prop-is-proof-irrelevant
    ( λ (q , p) → ex-falso (H (inv p ∙ right-zero-law-mul-ℕ q)))
is-prop-div-ℕ (succ-ℕ k) x (inr H) =
  is-prop-map-is-emb (is-emb-right-mul-ℕ (succ-ℕ k) (is-nonzero-succ-ℕ k)) x

div-ℕ-Decidable-Prop : (d x : ℕ) → is-nonzero-ℕ d → Decidable-Prop lzero
pr1 (div-ℕ-Decidable-Prop d x H) = div-ℕ d x
pr1 (pr2 (div-ℕ-Decidable-Prop d x H)) = is-prop-div-ℕ d x (inl H)
pr2 (pr2 (div-ℕ-Decidable-Prop d x H)) = is-decidable-div-ℕ d x
```

### If `b` divides `a` and `c` divides `b`, then `a/b · b/c ＝ a/c`

We use our convention that $0/0 = 0$ to avoid the hypothesis that $c$ is nonzero.

```agda
simplify-mul-quotient-div-ℕ :
  (a b c : ℕ) →
  (H : div-ℕ b a) (K : div-ℕ c b) (L : div-ℕ c a) →
  quotient-div-ℕ b a H *ℕ quotient-div-ℕ c b K ＝ quotient-div-ℕ c a L
simplify-mul-quotient-div-ℕ a b zero-ℕ H K L =
  ( ap
    ( quotient-div-ℕ b a H *ℕ_)
    ( is-zero-quotient-div-is-zero-divisor-ℕ 0 b K refl)) ∙
  ( right-zero-law-mul-ℕ (quotient-div-ℕ b a H)) ∙
  ( inv (is-zero-quotient-div-is-zero-divisor-ℕ 0 a L refl))
simplify-mul-quotient-div-ℕ a b (succ-ℕ c) H K L =
  is-injective-right-mul-ℕ (succ-ℕ c) (is-nonzero-succ-ℕ c)
    ( equational-reasoning
      (a/b *ℕ b/c+1) *ℕ succ-ℕ c
      ＝ a/b *ℕ (b/c+1 *ℕ succ-ℕ c)
        by associative-mul-ℕ a/b b/c+1 (succ-ℕ c)
      ＝ a/b *ℕ b
        by ap (a/b *ℕ_) (eq-quotient-div-ℕ (succ-ℕ c) b K)
      ＝ a
        by eq-quotient-div-ℕ b a H
      ＝ a/c+1 *ℕ succ-ℕ c
        by inv (eq-quotient-div-ℕ (succ-ℕ c) a L))
  where
  a/b : ℕ
  a/b = quotient-div-ℕ b a H
  b/c+1 : ℕ
  b/c+1 = quotient-div-ℕ (succ-ℕ c) b K
  a/c+1 : ℕ
  a/c+1 = quotient-div-ℕ (succ-ℕ c) a L
```

### Suppose `b | a` and `c | b`. If `d` divides `b/c` then `d` divides `a/c`

```agda
div-quotient-div-div-quotient-div-ℕ :
  {a b c d : ℕ} (H : div-ℕ b a) (K : div-ℕ c b) (L : div-ℕ c a) →
  div-ℕ d (quotient-div-ℕ c b K) → div-ℕ d (quotient-div-ℕ c a L)
div-quotient-div-div-quotient-div-ℕ {a} {b} {c} {d} H K L M =
  tr
    ( div-ℕ d)
    ( simplify-mul-quotient-div-ℕ a b c H K L)
    ( div-mul-ℕ
      ( quotient-div-ℕ b a H)
      ( d)
      ( quotient-div-ℕ c b K)
      ( M))
```

### A 3-for-2 property of division with respect to addition

```agda
div-add-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d y → div-ℕ d (x +ℕ y)
pr1 (div-add-ℕ d x y (n , p) (m , q)) = n +ℕ m
pr2 (div-add-ℕ d x y (n , p) (m , q)) =
  ( right-distributive-mul-add-ℕ n m d) ∙
  ( ap-add-ℕ p q)

div-left-summand-ℕ :
  (d x y : ℕ) → div-ℕ d y → div-ℕ d (x +ℕ y) → div-ℕ d x
div-left-summand-ℕ zero-ℕ x y (m , q) (n , p) =
  pair
    ( zero-ℕ)
    ( ( inv (right-zero-law-mul-ℕ n)) ∙
      ( p ∙ (ap (x +ℕ_) ((inv q) ∙ (right-zero-law-mul-ℕ m)))))
pr1 (div-left-summand-ℕ (succ-ℕ d) x y (m , q) (n , p)) = dist-ℕ m n
pr2 (div-left-summand-ℕ (succ-ℕ d) x y (m , q) (n , p)) =
  is-injective-right-add-ℕ (m *ℕ (succ-ℕ d))
    ( ( inv
        ( ( right-distributive-mul-add-ℕ m (dist-ℕ m n) (succ-ℕ d)) ∙
          ( commutative-add-ℕ
            ( m *ℕ (succ-ℕ d))
            ( (dist-ℕ m n) *ℕ (succ-ℕ d))))) ∙
      ( ( ap
          ( _*ℕ (succ-ℕ d))
          ( is-additive-right-inverse-dist-ℕ m n
            ( reflects-order-mul-succ-ℕ d m n
              ( concatenate-eq-leq-eq-ℕ q
                ( leq-add-ℕ' y x)
                ( inv p))))) ∙
        ( p ∙ (ap (x +ℕ_) (inv q)))))

div-right-summand-ℕ :
  (d x y : ℕ) → div-ℕ d x → div-ℕ d (x +ℕ y) → div-ℕ d y
div-right-summand-ℕ d x y H1 H2 =
  div-left-summand-ℕ d y x H1 (concatenate-div-eq-ℕ H2 (commutative-add-ℕ x y))
```

### If `d` divides both `x` and `x + 1`, then `d ＝ 1`

```agda
is-one-div-ℕ : (x y : ℕ) → div-ℕ x y → div-ℕ x (succ-ℕ y) → is-one-ℕ x
is-one-div-ℕ x y H K = is-one-div-one-ℕ x (div-right-summand-ℕ x y 1 H K)
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕ :
  (k l x y : ℕ) → div-ℕ k x → div-ℕ l y → div-ℕ (k *ℕ l) (x *ℕ y)
pr1 (preserves-div-mul-ℕ k l x y (q , α) (p , β)) = q *ℕ p
pr2 (preserves-div-mul-ℕ k l x y (q , α) (p , β)) =
  interchange-law-mul-mul-ℕ q p k l ∙ ap-mul-ℕ α β

preserves-div-left-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (k *ℕ x) (k *ℕ y)
preserves-div-left-mul-ℕ k x y =
  preserves-div-mul-ℕ k x k y (refl-div-ℕ k)

preserves-div-right-mul-ℕ :
  (k x y : ℕ) → div-ℕ x y → div-ℕ (x *ℕ k) (y *ℕ k)
preserves-div-right-mul-ℕ k x y H =
  preserves-div-mul-ℕ x k y k H (refl-div-ℕ k)
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-left-mul-ℕ :
  (m a b : ℕ) → is-nonzero-ℕ m → div-ℕ (m *ℕ a) (m *ℕ b) → div-ℕ a b
pr1 (reflects-div-left-mul-ℕ m a b H K) = quotient-div-ℕ (m *ℕ a) (m *ℕ b) K
pr2 (reflects-div-left-mul-ℕ m a b H K) =
  is-injective-left-mul-ℕ m H
    ( ( left-swap-mul-ℕ m
        ( quotient-div-ℕ (m *ℕ a) (m *ℕ b) K)
        ( a)) ∙
      ( eq-quotient-div-ℕ (m *ℕ a) (m *ℕ b) K))

reflects-div-right-mul-ℕ :
  (m a b : ℕ) → is-nonzero-ℕ m → div-ℕ (a *ℕ m) (b *ℕ m) → div-ℕ a b
reflects-div-right-mul-ℕ m a b H K =
  reflects-div-left-mul-ℕ m a b H
    ( concatenate-eq-div-eq-ℕ
      ( commutative-mul-ℕ m a)
      ( K)
      ( commutative-mul-ℕ b m))
```

### If `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

This logical equivalence holds for all integers, using the convention that `0/0 = 0`.

```agda
div-quotient-div-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ (d *ℕ x) y → div-ℕ x (quotient-div-ℕ d y H)
div-quotient-div-div-ℕ x y zero-ℕ H K =
  div-is-zero-ℕ x
    ( quotient-div-ℕ 0 y H)
    ( is-zero-quotient-div-is-zero-divisor-ℕ 0 y H refl)
div-quotient-div-div-ℕ x y (succ-ℕ d) H K =
  reflects-div-left-mul-ℕ (succ-ℕ d) x
    ( quotient-div-ℕ (succ-ℕ d) y H)
    ( is-nonzero-succ-ℕ d)
    ( tr (div-ℕ (succ-ℕ d *ℕ x)) (inv (eq-quotient-div-ℕ' (succ-ℕ d) y H)) K)

div-div-quotient-div-ℕ :
  (x y d : ℕ) (H : div-ℕ d y) →
  div-ℕ x (quotient-div-ℕ d y H) → div-ℕ (d *ℕ x) y
div-div-quotient-div-ℕ x y d H K =
  tr
    ( div-ℕ (d *ℕ x))
    ( eq-quotient-div-ℕ' d y H)
    ( preserves-div-left-mul-ℕ d x (quotient-div-ℕ d y H) K)

div-div-quotient-div-ℕ' :
  (x y d : ℕ) (H : div-ℕ d y) →
  ((K : div-ℕ d y) → div-ℕ x (quotient-div-ℕ d y K)) → div-ℕ (d *ℕ x) y
div-div-quotient-div-ℕ' x y d H K =
  div-div-quotient-div-ℕ x y d H (K H)

simplify-div-quotient-div-ℕ :
  {a d x : ℕ} (H : div-ℕ d a) →
  div-ℕ x (quotient-div-ℕ d a H) ↔ div-ℕ (d *ℕ x) a
pr1 (simplify-div-quotient-div-ℕ {a} {d} {x} H) =
  div-div-quotient-div-ℕ x a d H
pr2 (simplify-div-quotient-div-ℕ {a} {d} {x} H) =
  div-quotient-div-div-ℕ x a d H

simplify-div-quotient-div-ℕ' :
  {a d x : ℕ} (H : div-ℕ d a) →
  div-ℕ x (quotient-div-ℕ d a H) ↔ div-ℕ (x *ℕ d) a
pr1 (simplify-div-quotient-div-ℕ' {a} {d} {x} H) =
  tr (λ u → div-ℕ u a) (commutative-mul-ℕ d x) ∘ div-div-quotient-div-ℕ x a d H
pr2 (simplify-div-quotient-div-ℕ' {a} {d} {x} H) =
  div-quotient-div-div-ℕ x a d H ∘ tr (λ u → div-ℕ u a) (commutative-mul-ℕ x d)
```

### If `x` is nonzero and `d | x`, then `x/d ＝ 1` if and only if `d ＝ x`

```agda
is-one-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → (d ＝ x) →
  is-one-ℕ (quotient-div-ℕ d x H)
is-one-quotient-div-ℕ d .d f H refl = is-idempotent-quotient-div-ℕ d f H

eq-is-one-quotient-div-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ (quotient-div-ℕ d x H) → d ＝ x
eq-is-one-quotient-div-ℕ d (succ-ℕ x) (.1 , q) refl =
  inv (left-unit-law-mul-ℕ d) ∙ q
```

### If `x` is nonzero and `d | x`, then `x/d ＝ x` if and only if `d ＝ 1`

```agda
compute-quotient-div-is-one-ℕ :
  (d x : ℕ) → (H : div-ℕ d x) → is-one-ℕ d → quotient-div-ℕ d x H ＝ x
compute-quotient-div-is-one-ℕ .1 zero-ℕ H refl = refl
compute-quotient-div-is-one-ℕ .1 (succ-ℕ x) (u , q) refl =
  inv (right-unit-law-mul-ℕ u) ∙ q

is-one-divisor-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) →
  quotient-div-ℕ d x H ＝ x → is-one-ℕ d
is-one-divisor-ℕ d zero-ℕ N H p = ex-falso (N refl)
is-one-divisor-ℕ d (succ-ℕ x) N (.(succ-ℕ x) , q) refl =
  is-injective-left-mul-ℕ
    ( succ-ℕ x)
    ( N)
    ( q ∙ inv (right-unit-law-mul-ℕ (succ-ℕ x)))
```

### If `x` is nonzero and `d | x` is a nontrivial divisor, then `x/d < x`

```agda
le-quotient-div-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) → ¬ is-one-ℕ d →
  le-ℕ (quotient-div-ℕ d x H) x
le-quotient-div-ℕ d x f H g =
  map-left-unit-law-coproduct-is-empty
    ( quotient-div-ℕ d x H ＝ x)
    ( le-ℕ (quotient-div-ℕ d x H) x)
    ( map-neg (is-one-divisor-ℕ d x f H) g)
    ( eq-or-le-leq-ℕ
      ( quotient-div-ℕ d x H)
      ( x)
      ( upper-bound-quotient-div-ℕ d x H))
```

## See also

- [Bounded divisibility of natural numbers](elementary-number-theory.bounded-divisibility-natural-numbers.md)
- [Greatest common divisors of natural numbers](elementary-number-theory.greatest-common-divisors-natural-numbers.md)
- [Nontrivial divisors of natural numbers](elementary-number-theory.nontrivial-divisors-natural-numbers.md)
- [Prime divisors](elementary-number-theory.prime-divisors-natural-numbers.md)
- [Proper divisors of natural numbers](elementary-number-theory.proper-divisors-natural-numbers.md)
- [The poset of natural numbers ordered by divisibility](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md)
