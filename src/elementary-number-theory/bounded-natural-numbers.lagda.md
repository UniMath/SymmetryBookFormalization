# Bounded natural numbers

```agda
module elementary-number-theory.bounded-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of {{#concept "bounded natural numbers" Agda=bounded-ℕ}} with upper
bound $n$ is the type

$$
  \mathbb{N}_{\leq n} := \{k : ℕ \mid k \leq n\}.
$$

The type $\mathbb{N}_{\leq n}$ is [equivalent](foundation-core.equivalences.md)
to the [standard finite type](univalent-combinatorics.standard-finite-types.md)
$\mathsf{Fin}(n+1)$.

## Definition

### The bounded natural numbers

```agda
bounded-ℕ : ℕ → UU lzero
bounded-ℕ n = Σ ℕ (λ k → k ≤-ℕ n)

nat-bounded-ℕ : (n : ℕ) → bounded-ℕ n → ℕ
nat-bounded-ℕ n = pr1

upper-bound-nat-bounded-ℕ : (n : ℕ) (x : bounded-ℕ n) → nat-bounded-ℕ n x ≤-ℕ n
upper-bound-nat-bounded-ℕ n = pr2
```

## Properties

### The type of bounded natural numbers is a set

```agda
is-set-bounded-ℕ :
  (n : ℕ) → is-set (bounded-ℕ n)
is-set-bounded-ℕ n =
  is-set-type-subtype
    ( λ k → leq-ℕ-Prop k n)
    ( is-set-ℕ)
```

### The type $\mathbb{N}_{\leq b}$ is equivalent to the standard finite type $\mathsf{Fin}(n+1)$

```agda
bounded-nat-Fin :
  (n : ℕ) → Fin (succ-ℕ n) → bounded-ℕ n
pr1 (bounded-nat-Fin n x) = nat-Fin (succ-ℕ n) x
pr2 (bounded-nat-Fin n x) = upper-bound-nat-Fin n x

fin-bounded-ℕ :
  (n : ℕ) → bounded-ℕ n → Fin (succ-ℕ n)
fin-bounded-ℕ n x =
  mod-succ-ℕ n (nat-bounded-ℕ n x)

is-section-fin-bounded-ℕ :
  (n : ℕ) → is-section (bounded-nat-Fin n) (fin-bounded-ℕ n)
is-section-fin-bounded-ℕ n i =
  eq-type-subtype
    ( λ x → leq-ℕ-Prop x n)
    ( eq-cong-le-ℕ
      ( succ-ℕ n)
      ( nat-Fin (succ-ℕ n) (fin-bounded-ℕ n i))
      ( nat-bounded-ℕ n i)
      ( strict-upper-bound-nat-Fin (succ-ℕ n) (fin-bounded-ℕ n i))
      ( le-succ-leq-ℕ (nat-bounded-ℕ n i) n (upper-bound-nat-bounded-ℕ n i))
      ( cong-nat-mod-succ-ℕ n (nat-bounded-ℕ n i)))

is-retraction-fin-bounded-ℕ :
  (n : ℕ) → is-retraction (bounded-nat-Fin n) (fin-bounded-ℕ n)
is-retraction-fin-bounded-ℕ n =
  is-section-nat-Fin n

is-equiv-bounded-nat-Fin :
  (n : ℕ) → is-equiv (bounded-nat-Fin n)
is-equiv-bounded-nat-Fin n =
  is-equiv-is-invertible
    ( fin-bounded-ℕ n)
    ( is-section-fin-bounded-ℕ n)
    ( is-retraction-fin-bounded-ℕ n)

equiv-count-bounded-ℕ :
  (n : ℕ) → Fin (succ-ℕ n) ≃ bounded-ℕ n
pr1 (equiv-count-bounded-ℕ n) = bounded-nat-Fin n
pr2 (equiv-count-bounded-ℕ n) = is-equiv-bounded-nat-Fin n

count-bounded-ℕ :
  (n : ℕ) → count (bounded-ℕ n)
pr1 (count-bounded-ℕ n) = succ-ℕ n
pr2 (count-bounded-ℕ n) = equiv-count-bounded-ℕ n

is-finite-bounded-ℕ :
  (n : ℕ) → is-finite (bounded-ℕ n)
is-finite-bounded-ℕ n =
  is-finite-count (count-bounded-ℕ n)
```

## See also

- [The strictly bounded natural numbers](elementary-number-theory.strictly-bounded-natural-numbers.md)
