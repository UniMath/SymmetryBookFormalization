# Factorials of natural numbers

```agda
module elementary-number-theory.factorials where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
```

</details>

## Idea

The {{#concept "factorial" WD="factorial" WDID=Q120976 Agda=factorial-ℕ}} `n!`
of a number `n`, counts the number of ways to linearly order `n` distinct
objects.

## Definitions

### Factorial numbers

```agda
factorial-ℕ : ℕ → ℕ
factorial-ℕ 0 = 1
factorial-ℕ (succ-ℕ m) = (factorial-ℕ m) *ℕ (succ-ℕ m)
```

### Successors of factorial numbers

```agda
succ-factorial-ℕ : ℕ → ℕ
succ-factorial-ℕ n = succ-ℕ (factorial-ℕ n)
```

## Properties

```agda
div-factorial-ℕ :
  (n x : ℕ) → leq-ℕ x n → is-nonzero-ℕ x → div-ℕ x (factorial-ℕ n)
div-factorial-ℕ zero-ℕ zero-ℕ l H = ex-falso (H refl)
div-factorial-ℕ (succ-ℕ n) x l H with
  decide-leq-succ-ℕ x n l
... | inl l' =
  transitive-div-ℕ x
    ( factorial-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( pair (succ-ℕ n) (commutative-mul-ℕ (succ-ℕ n) (factorial-ℕ n)))
    ( div-factorial-ℕ n x l' H)
... | inr refl = pair (factorial-ℕ n) refl
```

```agda
is-nonzero-factorial-ℕ :
  (x : ℕ) → is-nonzero-ℕ (factorial-ℕ x)
is-nonzero-factorial-ℕ zero-ℕ = Eq-eq-ℕ
is-nonzero-factorial-ℕ (succ-ℕ x) =
  is-nonzero-mul-ℕ
    ( factorial-ℕ x)
    ( succ-ℕ x)
    ( is-nonzero-factorial-ℕ x)
    ( is-nonzero-succ-ℕ x)

leq-factorial-ℕ :
  (n : ℕ) → leq-ℕ n (factorial-ℕ n)
leq-factorial-ℕ zero-ℕ = leq-zero-ℕ 1
leq-factorial-ℕ (succ-ℕ n) =
  leq-mul-is-nonzero-ℕ'
    ( factorial-ℕ n)
    ( succ-ℕ n)
    ( is-nonzero-factorial-ℕ n)
```

### For any nonzero natural number $n$, the successor factorial of $n$ and $n$ itself are relatively prime

Note that the assumption that $n$ is nonzero is necessary, because the numbers $0$ and $0! + 1$ have greatest common divisor $2$.

```agda
is-one-is-common-divisor-id-succ-factorial-ℕ :
  (n d : ℕ) → is-nonzero-ℕ n →
  is-common-divisor-ℕ n (succ-factorial-ℕ n) d → is-one-ℕ d
is-one-is-common-divisor-id-succ-factorial-ℕ n d H (K , L) =
  is-one-div-one-ℕ d
    ( div-right-summand-ℕ d
      ( factorial-ℕ n)
      ( 1)
      ( transitive-div-ℕ d n
        ( factorial-ℕ n)
        ( div-factorial-ℕ n n (refl-leq-ℕ n) H)
      ( K))
    ( L))

relatively-prime-id-succ-factorial-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-relatively-prime-ℕ n (succ-factorial-ℕ n)
relatively-prime-id-succ-factorial-ℕ n H =
  is-one-is-common-divisor-id-succ-factorial-ℕ
    ( n)
    ( gcd-ℕ n (succ-factorial-ℕ n))
    ( H)
    ( is-common-divisor-gcd-ℕ n (succ-factorial-ℕ n))
```

### The successor factorials of $n$ and $n+1$ are relatively prime for any nonzero $n$

This property is stated as exercise 53 in section 1.2 of {{#cite NZM}}. This exercise was stated in a setting where the natural numbers start at $1$. The assumption that $n$ is nonzero is necessary, because $0! + 1 = 2$ and $1! + 1 = 2$.

**Proof.** First, we observe that

```text
  ((n + 1)! + 1) + n ＝ n!(n + 1) + (n + 1)
                     ＝ (n! + 1)(n + 1).
```

This shows that if `d` is a common divisor of `n! + 1` and `(n + 1)! + 1`, then `d` is a divisor of `n`. However, `n` and `n! + 1` are relatively prime if `n` is nonzero, so it follows that `d = 1`.

```agda
recursive-law-succ-factorial-ℕ :
  (n : ℕ) → succ-factorial-ℕ (succ-ℕ n) +ℕ n ＝ succ-factorial-ℕ n *ℕ succ-ℕ n
recursive-law-succ-factorial-ℕ n =
  left-successor-law-add-ℕ (factorial-ℕ (succ-ℕ n)) n ∙
  inv (left-successor-law-mul-ℕ (factorial-ℕ n) (succ-ℕ n))

is-one-is-common-divisor-consecutive-succ-factorial-ℕ :
  (n d : ℕ) → is-nonzero-ℕ n →
  is-common-divisor-ℕ (succ-factorial-ℕ n) (succ-factorial-ℕ (succ-ℕ n)) d →
  is-one-ℕ d
is-one-is-common-divisor-consecutive-succ-factorial-ℕ n d H (K , L) =
  is-one-is-common-divisor-id-succ-factorial-ℕ n d H
    ( ( div-right-summand-ℕ
        ( d)
        ( succ-factorial-ℕ (succ-ℕ n))
        ( n)
        ( L)
        ( concatenate-div-eq-ℕ
          ( div-mul-ℕ' (succ-ℕ n) d (succ-factorial-ℕ n) K)
          ( inv (recursive-law-succ-factorial-ℕ n)))) ,
      ( K))

is-relatively-prime-consecutive-succ-factorial-ℕ :
  (n : ℕ) → is-nonzero-ℕ n →
  is-relatively-prime-ℕ (succ-factorial-ℕ n) (succ-factorial-ℕ (succ-ℕ n))
is-relatively-prime-consecutive-succ-factorial-ℕ n H =
  is-one-is-common-divisor-consecutive-succ-factorial-ℕ
    ( n)
    ( gcd-ℕ
      ( succ-factorial-ℕ n)
      ( succ-factorial-ℕ (succ-ℕ n)))
    ( H)
    ( is-common-divisor-gcd-ℕ
      ( succ-factorial-ℕ n)
      ( succ-factorial-ℕ (succ-ℕ n)))
```

## External links

- [Factorial](https://en.wikipedia.org/wiki/Factorial) at Wikipedia
- [A000142](https://oeis.org/A000142) in the OEIS

## References

{{#bibliography}}
