# Strictly bounded natural numbers

```agda
module elementary-number-theory.strictly-bounded-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.equality-natural-numbers
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
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of
{{#concept "strictly bounded natural numbers" Agda=strictly-bounded-ℕ}} with
strict upper bound $n$ is the type

$$
  \mathbb{N}_{< n} := \{k : ℕ \mid k < n\}.
$$

The type $\mathbb{N}_{\leq n}$ is [equivalent](foundation-core.equivalences.md)
to the [standard finite type](univalent-combinatorics.standard-finite-types.md)
$\mathsf{Fin}(n+1)$.

## Definition

### The strictly bounded natural numbers

```agda
strictly-bounded-ℕ : ℕ → UU lzero
strictly-bounded-ℕ n = Σ ℕ (λ k → k <-ℕ n)

nat-strictly-bounded-ℕ :
  (n : ℕ) → strictly-bounded-ℕ n → ℕ
nat-strictly-bounded-ℕ n =
  pr1

strict-upper-bound-nat-strictly-bounded-ℕ :
  (n : ℕ) (x : strictly-bounded-ℕ n) → nat-strictly-bounded-ℕ n x <-ℕ n
strict-upper-bound-nat-strictly-bounded-ℕ n =
  pr2
```

## Properties

### The type of bounded natural numbers is a set

```agda
is-set-strictly-bounded-ℕ :
  (n : ℕ) → is-set (strictly-bounded-ℕ n)
is-set-strictly-bounded-ℕ n =
  is-set-type-subtype
    ( λ k → le-ℕ-Prop k n)
    ( is-set-ℕ)
```

### The type $\mathbb{N}_{\leq b}$ is equivalent to the standard finite type $\mathsf{Fin}(n+1)$

```agda
strictly-bounded-nat-Fin :
  (n : ℕ) → Fin n → strictly-bounded-ℕ n
pr1 (strictly-bounded-nat-Fin n i) = nat-Fin n i
pr2 (strictly-bounded-nat-Fin n i) = strict-upper-bound-nat-Fin n i

fin-strictly-bounded-ℕ :
  (n : ℕ) → strictly-bounded-ℕ n → Fin n
fin-strictly-bounded-ℕ (succ-ℕ n) x =
  mod-succ-ℕ n (nat-strictly-bounded-ℕ (succ-ℕ n) x)

is-section-fin-strictly-bounded-ℕ :
  (n : ℕ) → is-section (strictly-bounded-nat-Fin n) (fin-strictly-bounded-ℕ n)
is-section-fin-strictly-bounded-ℕ (succ-ℕ n) i =
  eq-type-subtype
    ( λ x → le-ℕ-Prop x (succ-ℕ n))
    ( eq-nat-mod-succ-ℕ n
      ( nat-strictly-bounded-ℕ (succ-ℕ n) i)
      ( strict-upper-bound-nat-strictly-bounded-ℕ (succ-ℕ n) i))

is-retraction-fin-strictly-bounded-ℕ :
  (n : ℕ) →
  is-retraction (strictly-bounded-nat-Fin n) (fin-strictly-bounded-ℕ n)
is-retraction-fin-strictly-bounded-ℕ (succ-ℕ n) i =
  is-section-nat-Fin n i

is-equiv-strictly-bounded-nat-Fin :
  (n : ℕ) → is-equiv (strictly-bounded-nat-Fin n)
is-equiv-strictly-bounded-nat-Fin n =
  is-equiv-is-invertible
    ( fin-strictly-bounded-ℕ n)
    ( is-section-fin-strictly-bounded-ℕ n)
    ( is-retraction-fin-strictly-bounded-ℕ n)

equiv-count-strictly-bounded-ℕ :
  (n : ℕ) → Fin n ≃ strictly-bounded-ℕ n
pr1 (equiv-count-strictly-bounded-ℕ n) =
  strictly-bounded-nat-Fin n
pr2 (equiv-count-strictly-bounded-ℕ n) =
  is-equiv-strictly-bounded-nat-Fin n

count-strictly-bounded-ℕ :
  (n : ℕ) → count (strictly-bounded-ℕ n)
pr1 (count-strictly-bounded-ℕ n) = n
pr2 (count-strictly-bounded-ℕ n) = equiv-count-strictly-bounded-ℕ n
```

## See also

- [The bounded natural numbers](elementary-number-theory.bounded-natural-numbers.md)
