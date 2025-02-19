# The pronic numbers

```agda
module elementary-number-theory.pronic-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "pronic numbers" Agda=pronic-number-ℕ WD="pronic number" WDID=Q1486643}}
are the [natural numbers](elementary-number-theory.natural-numbers.md) of the
form

$$
  n(n+1).
$$

The pronic numbers satisfy the recurrence

$$
  a_{n+1} = a_n + 2(n+1).
$$

The sequence `0, 2, 6, 12, 20, 30, 42, …` of pronic numbers is listed as
[A002378](https://oeis.org/A002378) in the [OEIS](literature.oeis.md)
{{#cite OEIS}}. The $n$th pronic number is
[even](elementary-number-theory.parity-natural-numbers.md) for every $n$, and it
is twice the $n$th
[triangular number](elementary-number-theory.triangular-numbers.md).

## Definitions

### The pronic numbers

```agda
pronic-number-ℕ : ℕ → ℕ
pronic-number-ℕ n = n *ℕ succ-ℕ n
```

### The iterated pronic numbers

The iterated pronic numbers are listed as [https://oeis.org/A007018) in the OEIS
{{#cite OEIS}}. Saidak {{#cite Saidak2006}} showed that the $n$th iterated
pronic number has at least $n$ prime factors, to obtain a new proof of the
[infinitude of primes](elementary-number-theory.infinitude-of-primes.md) as
recently as 2006.

Saidak's proof of the infinitude of primes is as follows. Write $N_n$ for the
$n$th iterated pronic number. Then $N_0 = 1$, which has at least $0$
[prime](elementary-number-theory.prime-numbers.md)
[divisors](elementary-number-theory.divisibility-natural-numbers.md). Assume
that $N_n$ has at least $n$ prime divisors. The number $N_n + 1$ is coprime to
$N_n$, so its prime divisors are distinct from the prime divisors of $N_n$.
Since $N_n + 1 > 1$, it has at least one prime divisor, so it follows that
$N_n(N_n + 1)$ has at least $n+1$ prime divisors. Therefore, there are
infinitely many primes.

```agda
iterated-pronic-number-ℕ :
  ℕ → ℕ
iterated-pronic-number-ℕ zero-ℕ =
  1
iterated-pronic-number-ℕ (succ-ℕ n) =
  pronic-number-ℕ (iterated-pronic-number-ℕ n)
```

## Properties

### The pronic number of a successor

```agda
pronic-number-succ-ℕ :
  (n : ℕ) → pronic-number-ℕ (succ-ℕ n) ＝ pronic-number-ℕ n +ℕ 2 *ℕ succ-ℕ n
pronic-number-succ-ℕ n =
  ( left-distributive-mul-add-ℕ (succ-ℕ n) n 2) ∙
  ( ap-add-ℕ (commutative-mul-ℕ (succ-ℕ n) n) (commutative-mul-ℕ (succ-ℕ n) 2))
```

### The $n$th pronic number $n(n + 1)$ is even

```agda
abstract
  is-even-pronic-number-ℕ :
    (n : ℕ) → is-even-ℕ (pronic-number-ℕ n)
  is-even-pronic-number-ℕ n
    with is-even-or-is-even-succ-ℕ n
  ... | inl H =
    is-even-div-is-even-ℕ
      ( n)
      ( pronic-number-ℕ n)
      ( H)
      ( succ-ℕ n , commutative-mul-ℕ (succ-ℕ n) n)
  ... | inr H =
    is-even-div-is-even-ℕ
      ( succ-ℕ n)
      ( pronic-number-ℕ n)
      ( H)
      ( n , refl)
```

### The $(n+1)$st pronic number

We have `(n + 1) * (n + 2) ＝ n * (n + 1) + 2 * (n + 1)`

```agda
compute-pronic-number-succ-ℕ :
  (n : ℕ) → pronic-number-ℕ (succ-ℕ n) ＝ pronic-number-ℕ n +ℕ 2 *ℕ succ-ℕ n
compute-pronic-number-succ-ℕ n =
  commutative-mul-ℕ (succ-ℕ n) (succ-ℕ (succ-ℕ n)) ∙
  right-distributive-mul-add-ℕ n 2 (succ-ℕ n)
```

### The sum of pronic numbers

The sum of the pronic numbers from $1$ to $n$ is given by the identity

$$
  \sum_{k=0}^n k(k+1) = \frac{n(n+1)(n+3)}{3} = 2\binom{n+3}{3}
$$

This sequence of numbers starts out as

$$
  0,\ 2,  8,\ 20,\ 40,\ 70,\ \ldots
$$

and it is listed as A007290 in the [OEIS](literature.oeis.md) {{#cite OEIS}}.
The computation of the sum of pronic numbers is stated as exercise 4 in section
1.2 of {{#cite Andrews94}}.

```agda
sum-of-pronic-numbers-ℕ : ℕ → ℕ
sum-of-pronic-numbers-ℕ n =
  sum-Fin-ℕ (succ-ℕ n) (λ i → pronic-number-ℕ (nat-Fin (succ-ℕ n) i))

dividend-sum-of-pronic-numbers-ℕ : ℕ → ℕ
dividend-sum-of-pronic-numbers-ℕ n = pronic-number-ℕ n *ℕ succ-ℕ (succ-ℕ n)

dividend-sum-of-pronic-numbers-succ-ℕ :
  (n : ℕ) →
  dividend-sum-of-pronic-numbers-ℕ (succ-ℕ n) ＝
  dividend-sum-of-pronic-numbers-ℕ n +ℕ 3 *ℕ pronic-number-ℕ (succ-ℕ n)
dividend-sum-of-pronic-numbers-succ-ℕ n =
  ( commutative-mul-ℕ (pronic-number-ℕ (succ-ℕ n)) (n +ℕ 3)) ∙
  ( right-distributive-mul-add-ℕ n 3 (pronic-number-ℕ (succ-ℕ n))) ∙
  ( ap
    ( _+ℕ 3 *ℕ pronic-number-ℕ (succ-ℕ n))
    ( inv (associative-mul-ℕ n (succ-ℕ n) (succ-ℕ (succ-ℕ n)))))

div-3-dividend-sum-of-pronic-numbers-ℕ :
  (n : ℕ) → div-ℕ 3 (dividend-sum-of-pronic-numbers-ℕ n)
div-3-dividend-sum-of-pronic-numbers-ℕ zero-ℕ = div-zero-ℕ 3
div-3-dividend-sum-of-pronic-numbers-ℕ (succ-ℕ n) =
  tr
    ( div-ℕ 3)
    ( inv (dividend-sum-of-pronic-numbers-succ-ℕ n))
    ( div-add-ℕ 3
      ( dividend-sum-of-pronic-numbers-ℕ n)
      ( 3 *ℕ pronic-number-ℕ (succ-ℕ n))
      ( div-3-dividend-sum-of-pronic-numbers-ℕ n)
      ( div-mul-ℕ' (pronic-number-ℕ (succ-ℕ n)) 3 3 (refl-div-ℕ 3)))

value-sum-of-pronic-numbers-ℕ : ℕ → ℕ
value-sum-of-pronic-numbers-ℕ n =
  quotient-div-ℕ 3
    ( dividend-sum-of-pronic-numbers-ℕ n)
    ( div-3-dividend-sum-of-pronic-numbers-ℕ n)

eq-value-sum-of-pronic-numbers-ℕ :
  (n : ℕ) →
  3 *ℕ value-sum-of-pronic-numbers-ℕ n ＝ dividend-sum-of-pronic-numbers-ℕ n
eq-value-sum-of-pronic-numbers-ℕ n =
  eq-quotient-div-ℕ' 3
    ( dividend-sum-of-pronic-numbers-ℕ n)
    ( div-3-dividend-sum-of-pronic-numbers-ℕ n)

compute-sum-of-pronic-numbers-ℕ' :
  (n : ℕ) →
  3 *ℕ sum-of-pronic-numbers-ℕ n ＝ dividend-sum-of-pronic-numbers-ℕ n
compute-sum-of-pronic-numbers-ℕ' zero-ℕ = refl
compute-sum-of-pronic-numbers-ℕ' (succ-ℕ n) =
  ( left-distributive-mul-add-ℕ 3
    ( sum-of-pronic-numbers-ℕ n)
    ( pronic-number-ℕ (succ-ℕ n))) ∙
  ( ap
    ( _+ℕ 3 *ℕ pronic-number-ℕ (succ-ℕ n))
    ( compute-sum-of-pronic-numbers-ℕ' n)) ∙
  ( inv (dividend-sum-of-pronic-numbers-succ-ℕ n))

compute-sum-of-pronic-numbers-ℕ :
  (n : ℕ) → sum-of-pronic-numbers-ℕ n ＝ value-sum-of-pronic-numbers-ℕ n
compute-sum-of-pronic-numbers-ℕ n =
  is-injective-left-mul-ℕ 3
    ( is-nonzero-succ-ℕ 2)
    ( ( compute-sum-of-pronic-numbers-ℕ' n) ∙
      ( inv (eq-value-sum-of-pronic-numbers-ℕ n)))
```

## See also

- [Nicomachus's Theorem](elementary-number-theory.nicomachuss-theorem.md)
- [Square pyramidal numbers](elementary-number-theory.square-pyramidal-numbers.md)
- [Squares of natural numbers](elementary-number-theory.squares-natural-numbers.md)
- [Triangular numbers](elementary-number-theory.triangular-numbers.md)

## References

{{#bibliography}}
