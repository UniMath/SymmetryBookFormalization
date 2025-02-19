# Bounded divisibility of natural numbers

```agda
module elementary-number-theory.bounded-divisibility-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Consider two [natural numbers](elementary-number-theory.natural-numbers.md) `m`
and `n`. The
{{#concept "bounded divisibility relation" Disambiguation="natural numbers" Agda=bounded-div-ℕ}}
is a [binary relation](foundation.binary-relations.md) on the type of
[natural numbers](elementary-number-theory.natural-numbers.md), where we say
that a number `n` is bounded divisible by `m` if there is an integer `q ≤ n`
such that `q * m ＝ n`.

The bounded divisibility relation is a slight strengthening of the
[divisibility relation](elementary-number-theory.divisibility-natural-numbers.md)
by ensuring that the quotient is bounded from above by `n`. This ensures that
the bounded divisibility relation is valued in
[propositions](foundation-core.propositions.md) for all `m` and `n`, unlike the
divisibility relation. Since the bounded divisibility relation is
[logically equivalent](foundation.logical-equivalences.md) to the divisibility
relation, but it is always valued in the propositions, we use the bounded
divisibility relation in the definition of the [poset](order-theory.posets.md)
of the
[natural numbers ordered by division](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

## Definitions

### The bounded divisibility predicate

```agda
module _
  (m n : ℕ)
  where

  bounded-div-ℕ : UU lzero
  bounded-div-ℕ = Σ ℕ (λ k → (k ≤-ℕ n) × (k *ℕ m ＝ n))

  quotient-bounded-div-ℕ : bounded-div-ℕ → ℕ
  quotient-bounded-div-ℕ = pr1

  upper-bound-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H ≤-ℕ n
  upper-bound-quotient-bounded-div-ℕ H = pr1 (pr2 H)

  eq-quotient-bounded-div-ℕ :
    (H : bounded-div-ℕ) → quotient-bounded-div-ℕ H *ℕ m ＝ n
  eq-quotient-bounded-div-ℕ H = pr2 (pr2 H)

  eq-quotient-bounded-div-ℕ' :
    (H : bounded-div-ℕ) → m *ℕ quotient-bounded-div-ℕ H ＝ n
  eq-quotient-bounded-div-ℕ' H =
    commutative-mul-ℕ m (quotient-bounded-div-ℕ H) ∙ eq-quotient-bounded-div-ℕ H
```

## Properties

### If a nonzero number `n` is bounded divisible by `m`, then its quotient is nonzero

```agda
is-nonzero-quotient-bounded-div-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → (H : bounded-div-ℕ m n) →
  is-nonzero-ℕ (quotient-bounded-div-ℕ m n H)
is-nonzero-quotient-bounded-div-ℕ m n N H refl =
  N (inv (eq-quotient-bounded-div-ℕ m n H))
```

### If a nonzero number `n` is bounded divisible by `m`, then `m` is bounded from above by `n`

**Proof.** Suppose that `q ≤ n` is such that `q * m ＝ n`. Since `n` is assumed
to be nonzero, it follows that `q` is nonzero. Therefore it follows that
`m ≤ q * m = n`.

```agda
upper-bound-divisor-bounded-div-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → bounded-div-ℕ m n → m ≤-ℕ n
upper-bound-divisor-bounded-div-ℕ m n H K =
  concatenate-leq-eq-ℕ m
    ( leq-mul-is-nonzero-ℕ'
      ( quotient-bounded-div-ℕ m n K)
      ( m)
      ( is-nonzero-quotient-bounded-div-ℕ m n H K))
    ( eq-quotient-bounded-div-ℕ m n K)
```

### If `n` is bounded divisible by a number `m`, then `n` is bounded divisible by its quotient by `m`

```agda
bounded-div-quotient-bounded-div-ℕ :
  (m n : ℕ) (H : bounded-div-ℕ m n) →
  bounded-div-ℕ (quotient-bounded-div-ℕ m n H) n
bounded-div-quotient-bounded-div-ℕ m zero-ℕ (q , b , p) =
  ( 0 , refl-leq-ℕ 0 , refl)
bounded-div-quotient-bounded-div-ℕ m (succ-ℕ n) H@(q , b , p) =
  ( m ,
    upper-bound-divisor-bounded-div-ℕ m (succ-ℕ n) (is-nonzero-succ-ℕ n) H ,
    commutative-mul-ℕ m (quotient-bounded-div-ℕ m (succ-ℕ n) H) ∙
    eq-quotient-bounded-div-ℕ m (succ-ℕ n) H)
```

### Bounded divisibility is decidable

```agda
is-decidable-bounded-div-ℕ :
  (m n : ℕ) → is-decidable (bounded-div-ℕ m n)
is-decidable-bounded-div-ℕ m n =
  is-decidable-bounded-Σ-ℕ'
    ( n)
    ( λ x → mul-ℕ x m ＝ n)
    ( λ x → has-decidable-equality-ℕ (mul-ℕ x m) n)
```

### Concatenating equality and bounded divisibility

```agda
concatenate-eq-bounded-div-ℕ :
  {x y z : ℕ} → x ＝ y → bounded-div-ℕ y z → bounded-div-ℕ x z
concatenate-eq-bounded-div-ℕ refl p = p

concatenate-bounded-div-eq-ℕ :
  {x y z : ℕ} → bounded-div-ℕ x y → y ＝ z → bounded-div-ℕ x z
concatenate-bounded-div-eq-ℕ p refl = p

concatenate-eq-bounded-div-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → bounded-div-ℕ y z → z ＝ w → bounded-div-ℕ x w
concatenate-eq-bounded-div-eq-ℕ refl p refl = p
```

### The quotients of a natural number `n` by two natural numbers `c` and `d` are equal if `c` and `d` are equal

Since the quotient is defined in terms of explicit proofs of divisibility, we
assume arbitrary proofs of dibisibility on both sides.

```agda
eq-quotient-bounded-div-eq-divisor-ℕ :
  (c d n : ℕ) → is-nonzero-ℕ c → c ＝ d →
  (H : bounded-div-ℕ c n) → (I : bounded-div-ℕ d n) →
  quotient-bounded-div-ℕ c n H ＝ quotient-bounded-div-ℕ d n I
eq-quotient-bounded-div-eq-divisor-ℕ c d n N p H I =
  is-injective-left-mul-ℕ c N
    ( tr
      ( λ x → c *ℕ quotient-bounded-div-ℕ c n H ＝ x *ℕ quotient-bounded-div-ℕ d n I)
      ( inv p)
      ( commutative-mul-ℕ c (quotient-bounded-div-ℕ c n H) ∙
        eq-quotient-bounded-div-ℕ c n H ∙
        inv (eq-quotient-bounded-div-ℕ d n I) ∙
        commutative-mul-ℕ (quotient-bounded-div-ℕ d n I) d))
```

### If two natural numbers are equal and one is divisible by a number `d`, then the other is divisible by `d` and their quotients are the same

The first part of the claim was proven above. Since the quotient is defined in
terms of explicit proofs of divisibility, we assume arbitrary proofs of
dibisibility on both sides.

```agda
eq-quotient-bounded-div-eq-is-nonzero-divisor-ℕ :
  {d m n : ℕ} → is-nonzero-ℕ d → m ＝ n → (H : bounded-div-ℕ d m) (K : bounded-div-ℕ d n) →
  quotient-bounded-div-ℕ d m H ＝ quotient-bounded-div-ℕ d n K
eq-quotient-bounded-div-eq-is-nonzero-divisor-ℕ N refl H K =
  is-injective-right-mul-ℕ _ N
    ( eq-quotient-bounded-div-ℕ _ _ H ∙ inv (eq-quotient-bounded-div-ℕ _ _ K))

eq-quotient-bounded-div-eq-is-nonzero-ℕ :
  {d m n : ℕ} → is-nonzero-ℕ m → m ＝ n → (H : bounded-div-ℕ d m) (K : bounded-div-ℕ d n) →
  quotient-bounded-div-ℕ d m H ＝ quotient-bounded-div-ℕ d n K
eq-quotient-bounded-div-eq-is-nonzero-ℕ {zero-ℕ} N refl H K =
  ex-falso
    ( N
      ( inv (eq-quotient-bounded-div-ℕ _ _ H) ∙
        right-zero-law-mul-ℕ (quotient-bounded-div-ℕ _ _ H)))
eq-quotient-bounded-div-eq-is-nonzero-ℕ {succ-ℕ d} N refl H K =
  eq-quotient-bounded-div-eq-is-nonzero-divisor-ℕ
    ( is-nonzero-succ-ℕ d) refl H K
```

### Bounded divisibility is a property

```agda
abstract
  is-prop-bounded-div-ℕ :
    (k n : ℕ) → is-prop (bounded-div-ℕ k n)
  is-prop-bounded-div-ℕ zero-ℕ n =
    is-prop-all-elements-equal
      ( λ (q , b , p) (q' , b' , p') →
        eq-type-subtype
          ( λ u → product-Prop (leq-ℕ-Prop u n) (Id-Prop ℕ-Set _ _))
          ( is-zero-leq-zero-ℕ q
            ( concatenate-leq-eq-ℕ q b (inv p ∙ right-zero-law-mul-ℕ q)) ∙
            inv
              ( is-zero-leq-zero-ℕ q'
                ( concatenate-leq-eq-ℕ q' b'
                  ( inv p' ∙ right-zero-law-mul-ℕ q')))))
  is-prop-bounded-div-ℕ (succ-ℕ k) n =
    is-prop-all-elements-equal
      ( λ (q , b , p) (q' , b' , p') →
        eq-type-subtype
          ( λ u → product-Prop (leq-ℕ-Prop u n) (Id-Prop ℕ-Set _ _))
          ( eq-quotient-bounded-div-eq-divisor-ℕ
            ( succ-ℕ k)
            ( succ-ℕ k)
            ( n)
            ( is-nonzero-succ-ℕ k)
            ( refl)
            ( q , b , p)
            ( q' , b' , p')))

bounded-div-ℕ-Prop : (k n : ℕ) → Prop lzero
pr1 (bounded-div-ℕ-Prop k n) = bounded-div-ℕ k n
pr2 (bounded-div-ℕ-Prop k n) = is-prop-bounded-div-ℕ k n

bounded-div-ℕ-Decidable-Prop : (k n : ℕ) → Decidable-Prop lzero
pr1 (bounded-div-ℕ-Decidable-Prop k n) = bounded-div-ℕ k n
pr1 (pr2 (bounded-div-ℕ-Decidable-Prop k n)) = is-prop-bounded-div-ℕ k n
pr2 (pr2 (bounded-div-ℕ-Decidable-Prop k n)) = is-decidable-bounded-div-ℕ k n
```

### The quotient of two numbers by any two proofs bounded divisibility are the same

```agda
compute-quotient-bounded-div-ℕ :
  {m m' n n' : ℕ} (q : m ＝ m') (p : n ＝ n')
  (H : bounded-div-ℕ m n) (K : bounded-div-ℕ m' n') →
  quotient-bounded-div-ℕ m n H ＝ quotient-bounded-div-ℕ m' n' K
compute-quotient-bounded-div-ℕ refl refl H K =
  ap
    ( quotient-bounded-div-ℕ _ _)
    { H}
    { K}
    ( eq-is-prop (is-prop-bounded-div-ℕ _ _))
```

### `0` is bounded divisible by any natural number

```agda
bounded-div-zero-ℕ :
  (n : ℕ) → bounded-div-ℕ n 0
pr1 (bounded-div-zero-ℕ n) = 0
pr1 (pr2 (bounded-div-zero-ℕ n)) = refl-leq-ℕ 0
pr2 (pr2 (bounded-div-zero-ℕ n)) = left-zero-law-mul-ℕ n

is-zero-quotient-bounded-div-zero-ℕ :
  (n : ℕ) (H : bounded-div-ℕ n 0) →
  is-zero-ℕ (quotient-bounded-div-ℕ n 0 H)
is-zero-quotient-bounded-div-zero-ℕ n H =
  is-zero-leq-zero-ℕ
    ( quotient-bounded-div-ℕ n 0 H)
    ( upper-bound-quotient-bounded-div-ℕ n 0 H)

is-zero-quotient-bounded-div-is-zero-ℕ :
  (m n : ℕ) (H : bounded-div-ℕ m n) →
  is-zero-ℕ n → is-zero-ℕ (quotient-bounded-div-ℕ m n H)
is-zero-quotient-bounded-div-is-zero-ℕ m .zero-ℕ H refl =
  is-zero-quotient-bounded-div-zero-ℕ m H
```

### If a number is bounded divisible by `0`, then it is `0`

```agda
is-zero-bounded-div-zero-divisor-ℕ :
  (n : ℕ) → bounded-div-ℕ 0 n → is-zero-ℕ n
is-zero-bounded-div-zero-divisor-ℕ n H =
  inv (eq-quotient-bounded-div-ℕ 0 n H) ∙
  right-zero-law-mul-ℕ (quotient-bounded-div-ℕ 0 n H)

is-zero-quotient-bounded-div-zero-divisor-ℕ :
  (n : ℕ) (H : bounded-div-ℕ 0 n) →
  is-zero-ℕ (quotient-bounded-div-ℕ 0 n H)
is-zero-quotient-bounded-div-zero-divisor-ℕ n H =
  is-zero-quotient-bounded-div-is-zero-ℕ 0 n H
    ( is-zero-bounded-div-zero-divisor-ℕ n H)

is-zero-bounded-div-is-zero-divisor-ℕ :
  (m n : ℕ) → bounded-div-ℕ m n → is-zero-ℕ m → is-zero-ℕ n
is-zero-bounded-div-is-zero-divisor-ℕ .zero-ℕ n H refl =
  is-zero-bounded-div-zero-divisor-ℕ n H

is-zero-quotient-bounded-div-is-zero-divisor-ℕ :
  (m n : ℕ) (H : bounded-div-ℕ m n) →
  is-zero-ℕ m → is-zero-ℕ (quotient-bounded-div-ℕ m n H)
is-zero-quotient-bounded-div-is-zero-divisor-ℕ m n H p =
  is-zero-quotient-bounded-div-is-zero-ℕ m n H
    ( is-zero-bounded-div-is-zero-divisor-ℕ m n H p)
```

### The divisibility relation is a partial order on the natural numbers

The [poset](order-theory.posets.md) of natural numbers ordered by divisibility
is defined in
[`elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility`](elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility.md).

```agda
refl-bounded-div-ℕ : is-reflexive bounded-div-ℕ
pr1 (refl-bounded-div-ℕ zero-ℕ) = 0
pr1 (pr2 (refl-bounded-div-ℕ zero-ℕ)) = refl-leq-ℕ 0
pr2 (pr2 (refl-bounded-div-ℕ zero-ℕ)) = refl
pr1 (refl-bounded-div-ℕ (succ-ℕ n)) = 1
pr1 (pr2 (refl-bounded-div-ℕ (succ-ℕ n))) = leq-zero-ℕ n
pr2 (pr2 (refl-bounded-div-ℕ (succ-ℕ n))) = left-unit-law-mul-ℕ (succ-ℕ n)

bounded-div-eq-ℕ : (x y : ℕ) → x ＝ y → bounded-div-ℕ x y
bounded-div-eq-ℕ x .x refl = refl-bounded-div-ℕ x

antisymmetric-bounded-div-ℕ : is-antisymmetric bounded-div-ℕ
antisymmetric-bounded-div-ℕ zero-ℕ n H K =
  inv (is-zero-bounded-div-zero-divisor-ℕ n H)
antisymmetric-bounded-div-ℕ (succ-ℕ m) zero-ℕ H K =
  is-zero-bounded-div-zero-divisor-ℕ (succ-ℕ m) K
antisymmetric-bounded-div-ℕ (succ-ℕ m) (succ-ℕ n) H K =
  antisymmetric-leq-ℕ
    ( succ-ℕ m)
    ( succ-ℕ n)
    ( upper-bound-divisor-bounded-div-ℕ
      ( succ-ℕ m)
      ( succ-ℕ n)
      ( is-nonzero-succ-ℕ n)
      ( H))
    ( upper-bound-divisor-bounded-div-ℕ
      ( succ-ℕ n)
      ( succ-ℕ m)
      ( is-nonzero-succ-ℕ m)
      ( K))

quotient-transitive-bounded-div-ℕ :
  (m n k : ℕ) → bounded-div-ℕ n k → bounded-div-ℕ m n → ℕ
quotient-transitive-bounded-div-ℕ m n k K H =
  quotient-bounded-div-ℕ n k K *ℕ quotient-bounded-div-ℕ m n H

eq-quotient-transitive-bounded-div-ℕ :
  (m n k : ℕ) (K : bounded-div-ℕ n k) (H : bounded-div-ℕ m n) →
  quotient-transitive-bounded-div-ℕ m n k K H *ℕ m ＝ k
eq-quotient-transitive-bounded-div-ℕ m n k K H =
  ( associative-mul-ℕ
    ( quotient-bounded-div-ℕ n k K)
    ( quotient-bounded-div-ℕ m n H)
    ( m)) ∙
  ( ap
    ( mul-ℕ (quotient-bounded-div-ℕ n k K))
    ( eq-quotient-bounded-div-ℕ m n H)) ∙
  ( eq-quotient-bounded-div-ℕ n k K)

upper-bound-quotient-transitive-bounded-div-ℕ :
  (m n k : ℕ) (K : bounded-div-ℕ n k) (H : bounded-div-ℕ m n) →
  quotient-transitive-bounded-div-ℕ m n k K H ≤-ℕ k
upper-bound-quotient-transitive-bounded-div-ℕ zero-ℕ n k K H =
  leq-is-zero-ℕ
    ( quotient-transitive-bounded-div-ℕ 0 n k K H)
    ( k)
    ( right-zero-law-mul-is-zero-ℕ
      ( quotient-bounded-div-ℕ n k K)
      ( quotient-bounded-div-ℕ 0 n H)
      ( is-zero-quotient-bounded-div-zero-divisor-ℕ n H))
upper-bound-quotient-transitive-bounded-div-ℕ (succ-ℕ m) n k K H =
  leq-left-factor-eq-ℕ
    ( quotient-transitive-bounded-div-ℕ (succ-ℕ m) n k K H)
    ( succ-ℕ m)
    ( k)
    ( is-nonzero-succ-ℕ m)
    ( eq-quotient-transitive-bounded-div-ℕ (succ-ℕ m) n k K H)

transitive-bounded-div-ℕ : is-transitive bounded-div-ℕ
pr1 (transitive-bounded-div-ℕ m n k K H) =
  quotient-transitive-bounded-div-ℕ m n k K H
pr1 (pr2 (transitive-bounded-div-ℕ m n k K H)) =
  upper-bound-quotient-transitive-bounded-div-ℕ m n k K H
pr2 (pr2 (transitive-bounded-div-ℕ m n k K H)) =
  eq-quotient-transitive-bounded-div-ℕ m n k K H
```
