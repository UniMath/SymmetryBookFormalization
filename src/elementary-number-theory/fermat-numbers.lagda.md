# Fermat numbers

```agda
module elementary-number-theory.fermat-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.squares-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Fermat numbers" WD="Fermat number" WDID=Q207264 OEIS=A000215 Agda=fermat-number-ℕ}}
are numbers of the form $F_n := 2^{2^n}+1$. The first five Fermat numbers are

```text
  3, 5, 17, 257, and 65537.
```

The sequence of Fermat numbers is listed as A000215 in the
[Online Encyclopedia of Integer Sequences](literature.oeis.md) {{#cite OEIS}}.

Alternatively, the Fermat numbers can be defined with
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
F 0 := 3
F (n + 1) := 2 + Π_{i≤n} F_i
```

This recurrence implies that any two Fermat numbers are
[relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md),
because it follows from this recurrence that any divisor of two distinct Fermat
numbers must divide the number $2$. Since the Fermat numbers are all odd, this
implies that any divisor of two distinct Fermat numbers must be the number $1$.

Goldbach used this observation to prove the
[infinitude of primes](elementary-number-theory.infinitude-of-primes.md)
{{#cite AZ18}} : Since there are infinitely many Fermat numbers, and all of them
are relatively prime, there must be infinitely many prime numbers. Fermat
numbers also feature in a series of long-standing open problems in mathematics,
including:

- Are there infinitely many prime Fermat numbers?
- Is $F_n$ composite for all $n\geq 5$?

## Definition

### The Fermat numbers

```agda
fermat-number-ℕ : ℕ → ℕ
fermat-number-ℕ n = exp-ℕ 2 (exp-ℕ 2 n) +ℕ 1
```

### The recursive definition of the Fermat numbers

```agda
recursive-fermat-number-ℕ : ℕ → ℕ
recursive-fermat-number-ℕ =
  strong-rec-ℕ 3
    ( λ n f →
      add-ℕ
        ( Π-ℕ
          ( succ-ℕ n)
          ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))
        ( 2))

compute-succ-recursive-fermat-number-ℕ :
  (n : ℕ) →
  recursive-fermat-number-ℕ (succ-ℕ n) ＝
  Π-ℕ (succ-ℕ n) (λ i → recursive-fermat-number-ℕ (nat-Fin (succ-ℕ n) i)) +ℕ 2
compute-succ-recursive-fermat-number-ℕ =
  compute-succ-strong-rec-ℕ 3
    ( λ n f →
      add-ℕ
        ( Π-ℕ
          ( succ-ℕ n)
          ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))
        ( 2))
```

## Properties

### Every Fermat number is greater than $2$

```agda
leq-two-fermat-number-ℕ :
  (n : ℕ) → 2 ≤-ℕ fermat-number-ℕ n
leq-two-fermat-number-ℕ n = leq-one-exp-ℕ 2 (2 ^ℕ n) star
```

### Every Fermat number is odd

```agda
is-odd-fermat-number-ℕ :
  (n : ℕ) → is-odd-ℕ (fermat-number-ℕ n)
is-odd-fermat-number-ℕ n =
  is-odd-succ-is-even-ℕ
    ( 2 ^ℕ (2 ^ℕ n))
    ( div-exp-ℕ 2 (2 ^ℕ n) (is-nonzero-exp-ℕ 2 n (is-nonzero-succ-ℕ 1)))
```

### The distance from a Fermat number to the number $2$

Any Fermat number of the form $F(n+1)=2^{2^{n+1}}+1$ can be computed as

$$
  F(n+1)-2=(2^{2^n})^2-1=(2^{2^n}+1)(2^{2^n}-1)=F(n)(F(n)-2).
$$

```agda
dist-fermat-number-two-ℕ :
  (n : ℕ) →
  dist-ℕ (fermat-number-ℕ n) 2 ＝
  Π-ℕ n (λ k → fermat-number-ℕ (nat-Fin n k))
dist-fermat-number-two-ℕ zero-ℕ = refl
dist-fermat-number-two-ℕ (succ-ℕ n) =
  ap (λ x → dist-ℕ x 1) (ap (2 ^ℕ_) (exp-succ-ℕ 2 n) ∙ exp-mul-ℕ (2 ^ℕ n) 2) ∙
  distance-of-squares-ℕ (2 ^ℕ 2 ^ℕ n) 1 ∙
  ap (_*ℕ fermat-number-ℕ n) (dist-fermat-number-two-ℕ n)
```

### Computing the $n$-th Fermat number as the product of all the previous Fermat numbers plus $2$

```agda
compute-fermat-number-ℕ :
  (n : ℕ) →
  fermat-number-ℕ n ＝ Π-ℕ n (λ k → fermat-number-ℕ (nat-Fin n k)) +ℕ 2
compute-fermat-number-ℕ n =
  ( inv
    ( rewrite-right-dist-add-ℕ 2
      ( Π-ℕ n (λ k → fermat-number-ℕ (nat-Fin n k)))
      ( fermat-number-ℕ n)
      ( leq-two-fermat-number-ℕ n)
      ( inv
        ( ( symmetric-dist-ℕ 2 (fermat-number-ℕ n)) ∙
          ( dist-fermat-number-two-ℕ n))))) ∙
  ( commutative-add-ℕ 2 (Π-ℕ n (λ k → fermat-number-ℕ (nat-Fin n k))))
```

### The $n$th Fermat number is equal to the $n$th recursive Fermat number

**Proof.** The proof is by strong induction on the natural numbers. The base
case holds by reflexivity. For the inductive step, assume that

```agda
compute-recursive-fermat-number-ℕ :
  (n : ℕ) → recursive-fermat-number-ℕ n ＝ fermat-number-ℕ n
compute-recursive-fermat-number-ℕ =
  strong-ind-ℕ
    ( λ n → recursive-fermat-number-ℕ n ＝ fermat-number-ℕ n)
    ( refl)
    ( λ n H →
      ( compute-succ-recursive-fermat-number-ℕ n) ∙
      ( ap
        ( _+ℕ 2)
        ( preserves-htpy-Π-ℕ
          ( succ-ℕ n)
          ( λ i → H (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))) ∙
      ( inv (compute-fermat-number-ℕ (succ-ℕ n))))
```

### Any two distinct Fermat numbers are relatively prime

**Proof.** By the recursive definition of the Fermat numbers, we have that
$F_{n+1}=(\prod_{n=0}^n F_n) + 2$. This implies that if $d$ divides $F_m$ and
$F_n$ for some $n>m$, then $d|2$. However, the Fermat numbers are odd, so $d=1$.

```agda
is-one-div-fermat-number-nat-Fin-ℕ :
  (n d : ℕ) (i : Fin n) →
  div-ℕ d (fermat-number-ℕ (nat-Fin n i)) →
  div-ℕ d (fermat-number-ℕ n) →
  is-one-ℕ d
is-one-div-fermat-number-nat-Fin-ℕ (succ-ℕ n) d i H K =
  is-one-is-odd-div-two-ℕ d
    ( div-right-summand-ℕ d
      ( Π-ℕ (succ-ℕ n) (λ j → fermat-number-ℕ (nat-Fin (succ-ℕ n) j)))
      ( 2)
      ( transitive-div-ℕ d
        ( fermat-number-ℕ (nat-Fin (succ-ℕ n) i))
        ( Π-ℕ (succ-ℕ n) (λ j → fermat-number-ℕ (nat-Fin (succ-ℕ n) j)))
        ( div-factor-Π-ℕ (succ-ℕ n) (fermat-number-ℕ ∘ nat-Fin (succ-ℕ n)) i)
        ( H))
      ( concatenate-div-eq-ℕ K (compute-fermat-number-ℕ (succ-ℕ n))))
    ( is-odd-div-is-odd-ℕ d
      ( fermat-number-ℕ (succ-ℕ n))
      ( is-odd-fermat-number-ℕ (succ-ℕ n))
      ( K))

is-one-div-fermat-number-le-ℕ :
  (m n d : ℕ) → m <-ℕ n →
  div-ℕ d (fermat-number-ℕ m) → div-ℕ d (fermat-number-ℕ n) → is-one-ℕ d
is-one-div-fermat-number-le-ℕ m (succ-ℕ n) d H K L =
  is-one-div-fermat-number-nat-Fin-ℕ
    ( succ-ℕ n)
    ( d)
    ( mod-succ-ℕ n m)
    ( tr
      ( div-ℕ d ∘ fermat-number-ℕ)
      ( inv (eq-nat-mod-succ-ℕ n m H))
      ( K))
    ( L)

is-one-is-common-divisor-fermat-number-ℕ :
  (m n d : ℕ) → m ≠ n →
  is-common-divisor-ℕ (fermat-number-ℕ m) (fermat-number-ℕ n) d → is-one-ℕ d
is-one-is-common-divisor-fermat-number-ℕ m n d H (K , L) =
  rec-coproduct
    ( λ u → is-one-div-fermat-number-le-ℕ m n d u K L)
    ( λ u → is-one-div-fermat-number-le-ℕ n m d u L K)
    ( decide-le-neq-ℕ m n H)

is-relatively-prime-fermat-number-ℕ :
  (m n : ℕ) → m ≠ n →
  is-relatively-prime-ℕ (fermat-number-ℕ m) (fermat-number-ℕ n)
is-relatively-prime-fermat-number-ℕ m n H =
  is-one-is-common-divisor-fermat-number-ℕ m n
    ( gcd-ℕ (fermat-number-ℕ m) (fermat-number-ℕ n))
    ( H)
    ( is-common-divisor-gcd-ℕ (fermat-number-ℕ m) (fermat-number-ℕ n))
```

## External link

- [Fermat number](https://en.wikipedia.org/wiki/Fermat_number) at Wikipedia
- [A000215](https://oeis.org/A000215) in the OEIS

## References

{{#bibliography}}
