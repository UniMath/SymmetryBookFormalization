# Exponentiation of natural numbers

```agda
module elementary-number-theory.exponentiation-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.commutative-semiring-of-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.strictly-inflationary-functions-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.strict-order-preserving-maps

open import univalent-combinatorics.finite-maps
```

</details>

## Idea

The {{#concept "exponential" Agda=exp-ℕ WD="exponentiation" WDID=Q33456}} $m^n$
of two [natural numbers](elementary-number-theory.natural-numbers.md) is the
number obtained by multiplying $m$ with itself $n$ times. We use the following
terminology in our formalization and naming scheme:

- The number $m^n$ is the **$n$th power** of $m$.
- The number $m^n$ is an **exponential**.
- The number $n$ in $m^n$ is called the **exponent** of the exponential.
- The number $m$ in $m^n$ is the **base** of the exponential.
- The operation $m,n \mapsto m^n$ is called **exponentiation**.
- The function $n \mapsto m^n$ is the **exponentiation function** with base $m$.
- The function $m \mapsto m^n$ is the **$n$th power function**. Specific
  instances are [squaring](elementary-number-theory.squares-natural-numbers.md)
  and [cubing](elementary-number-theory.cubes-natural-numbers.md).

The natural numbers satisfy Tarski's high school arithmetic laws for
exponentiation.

## Definition

### Powers of natural numbers

The function `power-ℕ n : ℕ → ℕ` defines $n$th power of a natural number $m$.

```agda
power-ℕ : ℕ → ℕ → ℕ
power-ℕ = power-Commutative-Semiring ℕ-Commutative-Semiring
```

### The predicate of being an $n$th power

```agda
is-power-ℕ : ℕ → ℕ → UU lzero
is-power-ℕ m n = fiber (power-ℕ n) m
```

### Exponentiation of natural numbers

The function `exp-ℕ : ℕ → ℕ → ℕ` defines the exponentiation map
$m,n \mapsto m^n$. Note that this is just the power function, with the order of
its arguments swapped.

```agda
exp-ℕ : ℕ → ℕ → ℕ
exp-ℕ m n = power-ℕ n m

infixr 45 _^ℕ_
_^ℕ_ = exp-ℕ
```

### The predicate of being an exponential of a given natural number

```agda
is-exponential-ℕ : ℕ → ℕ → UU lzero
is-exponential-ℕ m n = fiber (exp-ℕ m) n

valuation-is-exponential-ℕ :
  (m n : ℕ) → is-exponential-ℕ m n → ℕ
valuation-is-exponential-ℕ m n = pr1

eq-valuation-is-exponential-ℕ :
  (m n : ℕ) (H : is-exponential-ℕ m n) →
  exp-ℕ m (valuation-is-exponential-ℕ m n H) ＝ n
eq-valuation-is-exponential-ℕ m n = pr2
```

## Properties

### `1ⁿ ＝ 1`

```agda
annihilation-law-exp-ℕ : (n : ℕ) → 1 ^ℕ n ＝ 1
annihilation-law-exp-ℕ = power-one-Commutative-Semiring ℕ-Commutative-Semiring
```

### `mⁿ⁺¹ = mⁿm`

```agda
exp-succ-ℕ :
  (m n : ℕ) → m ^ℕ succ-ℕ n ＝ m ^ℕ n *ℕ m
exp-succ-ℕ m n =
  power-succ-Commutative-Semiring ℕ-Commutative-Semiring n m
```

### `mⁿ⁺¹ ＝ mmⁿ`

```agda
exp-succ-ℕ' :
  (m n : ℕ) → m ^ℕ succ-ℕ n ＝ m *ℕ m ^ℕ n
exp-succ-ℕ' m n =
  power-succ-Commutative-Semiring' ℕ-Commutative-Semiring n m
```

### Powers by sums of natural numbers are products of powers

```agda
left-distributive-exp-add-ℕ :
  (m n : ℕ) {x : ℕ} → x ^ℕ (m +ℕ n) ＝ x ^ℕ m *ℕ x ^ℕ n
left-distributive-exp-add-ℕ =
  distributive-power-add-Commutative-Semiring ℕ-Commutative-Semiring
```

### Powers distribute over products

```agda
right-distributive-exp-mul-ℕ :
  (n : ℕ) (x y : ℕ) → (x *ℕ y) ^ℕ n ＝ x ^ℕ n *ℕ y ^ℕ n
right-distributive-exp-mul-ℕ =
  distributive-power-mul-Commutative-Semiring ℕ-Commutative-Semiring
```

### Powers by products of natural numbers are iterated powers

```agda
exp-mul-ℕ :
  (m n : ℕ) {x : ℕ} → x ^ℕ (m *ℕ n) ＝ (x ^ℕ m) ^ℕ n
exp-mul-ℕ =
  power-mul-Commutative-Semiring ℕ-Commutative-Semiring
```

### The exponent $m^n$ is nonzero if $m$ is nonzero

```agda
is-nonzero-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ m → is-nonzero-ℕ (m ^ℕ n)
is-nonzero-exp-ℕ m zero-ℕ H =
  is-nonzero-one-ℕ
is-nonzero-exp-ℕ m (succ-ℕ zero-ℕ) H = H
is-nonzero-exp-ℕ m (succ-ℕ (succ-ℕ n)) H =
  is-nonzero-mul-ℕ (m ^ℕ succ-ℕ n) m (is-nonzero-exp-ℕ m (succ-ℕ n) H) H

le-zero-exp-ℕ :
  (m n : ℕ) → 0 <-ℕ m → 0 <-ℕ m ^ℕ n
le-zero-exp-ℕ m zero-ℕ H =
  star
le-zero-exp-ℕ m (succ-ℕ zero-ℕ) H =
  H
le-zero-exp-ℕ m (succ-ℕ (succ-ℕ n)) H =
  preserves-strict-order-mul-ℕ
    ( 0)
    ( m ^ℕ succ-ℕ n)
    ( 0)
    ( m)
    ( le-zero-exp-ℕ m (succ-ℕ n) H)
    ( H)

leq-one-exp-ℕ :
  (m n : ℕ) → 1 ≤-ℕ m → 1 ≤-ℕ m ^ℕ n
leq-one-exp-ℕ m n H =
  leq-one-is-nonzero-ℕ
    ( m ^ℕ n)
    ( is-nonzero-exp-ℕ m n (is-nonzero-leq-one-ℕ m H))
```

### The exponent $m^n$ of a number $m>1$ by a nonzero number $n$ is strictly greater than $0$

```agda
le-one-exp-ℕ :
  (m n : ℕ) → 1 <-ℕ m → is-nonzero-ℕ n → 1 <-ℕ m ^ℕ n
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) zero-ℕ H K = ex-falso (K refl)
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ zero-ℕ) H K = star
le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ (succ-ℕ n)) H K =
  concatenate-le-leq-ℕ 1
    ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)
    ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ (succ-ℕ n))
    ( le-one-exp-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ n) H (is-nonzero-succ-ℕ n))
    ( concatenate-eq-leq-eq-ℕ
      ( inv (right-unit-law-mul-ℕ (succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)))
      ( preserves-order-right-mul-ℕ
        ( succ-ℕ (succ-ℕ m) ^ℕ succ-ℕ n)
        ( 1)
        ( succ-ℕ (succ-ℕ m))
        ( star))
      ( exp-succ-ℕ (succ-ℕ (succ-ℕ m)) (succ-ℕ n)))
```

### The exponent $m^n$ is equal to the $n$-fold product of $m$

```agda
compute-constant-product-ℕ :
  (m n : ℕ) → Π-ℕ n (λ _ → m) ＝ exp-ℕ m n
compute-constant-product-ℕ m zero-ℕ = refl
compute-constant-product-ℕ m (succ-ℕ zero-ℕ) = left-unit-law-add-ℕ m
compute-constant-product-ℕ m (succ-ℕ (succ-ℕ n)) =
  ap (_*ℕ m) (compute-constant-product-ℕ m (succ-ℕ n))
```

### The base of the exponent divides its successor exponents

```agda
div-exp-succ-ℕ :
  (m n : ℕ) → div-ℕ m (m ^ℕ succ-ℕ n)
pr1 (div-exp-succ-ℕ m n) = m ^ℕ n
pr2 (div-exp-succ-ℕ m n) = inv (exp-succ-ℕ m n)

div-exp-succ-ℕ' :
  (m n : ℕ) → div-ℕ (m ^ℕ n) (m ^ℕ succ-ℕ n)
pr1 (div-exp-succ-ℕ' m n) = m
pr2 (div-exp-succ-ℕ' m n) = inv (exp-succ-ℕ' m n)

div-exp-is-successor-ℕ :
  (m n : ℕ) → is-successor-ℕ n → div-ℕ m (m ^ℕ n)
div-exp-is-successor-ℕ m .(succ-ℕ k) (k , refl) =
  div-exp-succ-ℕ m k

div-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → div-ℕ m (m ^ℕ n)
div-exp-ℕ m n H =
  div-exp-is-successor-ℕ m n (is-successor-is-nonzero-ℕ H)

bounded-div-exp-ℕ :
  (m n : ℕ) → is-nonzero-ℕ n → bounded-div-ℕ m (m ^ℕ n)
bounded-div-exp-ℕ m n H =
  bounded-div-div-ℕ m (m ^ℕ n) (div-exp-ℕ m n H)
```

### If an exponential of a number greater than $1$ is equal to $1$, then its exponent is $0$

```agda
is-zero-exponent-is-one-exp-ℕ :
  (m n : ℕ) → 1 <-ℕ m → is-one-ℕ (m ^ℕ n) → is-zero-ℕ n
is-zero-exponent-is-one-exp-ℕ m zero-ℕ H K =
  refl
is-zero-exponent-is-one-exp-ℕ m (succ-ℕ n) H p =
  ex-falso
    ( neq-le-ℕ
      ( 1)
      ( m ^ℕ n *ℕ m)
      ( concatenate-leq-le-ℕ 1
        ( m ^ℕ n)
        ( m ^ℕ n *ℕ m)
        ( leq-one-exp-ℕ m n (leq-le-ℕ 1 m H))
        ( concatenate-eq-le-ℕ
          ( m ^ℕ n)
          ( m ^ℕ n *ℕ 1)
          ( m ^ℕ n *ℕ m)
          ( inv (right-unit-law-mul-ℕ (m ^ℕ n)))
          ( preserves-strict-order-left-mul-ℕ
            ( m ^ℕ n)
            ( 1)
            ( m)
            ( is-nonzero-exp-ℕ m n (is-nonzero-le-ℕ 1 m H)) H)))
      ( inv p ∙ exp-succ-ℕ m n))
```

### The function $n \mapsto m^n$ is injective and an embedding for any $m>1$

```agda
is-injective-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-injective (m ^ℕ_)
is-injective-exp-ℕ m H {zero-ℕ} {zero-ℕ} p =
  refl
is-injective-exp-ℕ m H {zero-ℕ} {succ-ℕ l} p =
  inv (is-zero-exponent-is-one-exp-ℕ m (succ-ℕ l) H (inv p))
is-injective-exp-ℕ m H {succ-ℕ k} {zero-ℕ} p =
  is-zero-exponent-is-one-exp-ℕ m (succ-ℕ k) H p
is-injective-exp-ℕ m H {succ-ℕ k} {succ-ℕ l} p =
  ap
    ( succ-ℕ)
    ( is-injective-exp-ℕ m H {k} {l}
      ( is-injective-right-mul-ℕ m
        ( is-nonzero-le-ℕ 1 m H)
        ( inv (exp-succ-ℕ m k) ∙ p ∙ exp-succ-ℕ m l)))

is-emb-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-emb (m ^ℕ_)
is-emb-exp-ℕ m H =
  is-emb-is-injective is-set-ℕ (is-injective-exp-ℕ m H)
```

### Exponentiating a nonzero number is an order preserving function

```agda
preserves-order-exponent-exp-ℕ :
  (m : ℕ) → is-nonzero-ℕ m →
  preserves-order-Poset ℕ-Poset ℕ-Poset (m ^ℕ_)
preserves-order-exponent-exp-ℕ m H zero-ℕ zero-ℕ K =
  refl-leq-ℕ 1
preserves-order-exponent-exp-ℕ m H zero-ℕ (succ-ℕ k) K =
  leq-one-exp-ℕ m (succ-ℕ k) (leq-one-is-nonzero-ℕ m H)
preserves-order-exponent-exp-ℕ m H (succ-ℕ n) (succ-ℕ k) K =
  concatenate-eq-leq-eq-ℕ
    ( exp-succ-ℕ m n)
    ( preserves-order-mul-ℕ
      ( m ^ℕ n)
      ( m ^ℕ k)
      ( m)
      ( m)
      ( preserves-order-exponent-exp-ℕ m H n k K)
      ( refl-leq-ℕ m))
    ( inv (exp-succ-ℕ m k))
```

### Exponentiating a number strictly greater than $1$ is a strictly order preserving function

```agda
preserves-strict-order-exponent-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m →
  preserves-strict-order-map-Strict-Preorder
    ( ℕ-Strict-Preorder)
    ( ℕ-Strict-Preorder)
    ( m ^ℕ_)
preserves-strict-order-exponent-exp-ℕ m H zero-ℕ (succ-ℕ k) K =
  le-one-exp-ℕ m (succ-ℕ k) H (is-nonzero-succ-ℕ k)
preserves-strict-order-exponent-exp-ℕ m H (succ-ℕ n) (succ-ℕ k) K =
  concatenate-eq-le-eq-ℕ
    ( m ^ℕ succ-ℕ n)
    ( m ^ℕ n *ℕ m)
    ( m ^ℕ k *ℕ m)
    ( m ^ℕ succ-ℕ k)
    ( exp-succ-ℕ m n)
    ( preserves-strict-order-right-mul-ℕ
      ( m)
      ( m ^ℕ n)
      ( m ^ℕ k)
      ( is-nonzero-le-ℕ 1 m H)
      ( preserves-strict-order-exponent-exp-ℕ m H n k K))
    ( inv (exp-succ-ℕ m k))
```

### The function $n \mapsto m^n$ is strictly inflationary for any $1<m$

```agda
is-strictly-inflationary-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-strictly-inflationary-map-ℕ (m ^ℕ_)
is-strictly-inflationary-exp-ℕ m H zero-ℕ = star
is-strictly-inflationary-exp-ℕ m H (succ-ℕ zero-ℕ) = H
is-strictly-inflationary-exp-ℕ m H (succ-ℕ (succ-ℕ n)) =
  concatenate-leq-le-leq-ℕ
    ( succ-ℕ (succ-ℕ n))
    ( succ-ℕ n *ℕ 2)
    ( m ^ℕ succ-ℕ n *ℕ 2)
    ( m ^ℕ succ-ℕ (succ-ℕ n))
    ( concatenate-leq-eq-ℕ
      ( n +ℕ 2)
      ( preserves-order-add-ℕ
        { succ-ℕ n}
        { succ-ℕ n *ℕ 1}
        { 1}
        { succ-ℕ n}
        ( leq-eq-ℕ
          ( succ-ℕ n)
          ( succ-ℕ n *ℕ 1)
          ( inv (right-unit-law-mul-ℕ (succ-ℕ n))))
        ( leq-zero-ℕ n))
      ( inv (right-successor-law-mul-ℕ (succ-ℕ n) 1)))
    ( preserves-strict-order-right-mul-ℕ 2
      ( succ-ℕ n)
      ( m ^ℕ succ-ℕ n)
      ( is-nonzero-succ-ℕ 1)
      ( is-strictly-inflationary-exp-ℕ m H (succ-ℕ n)))
    ( concatenate-leq-eq-ℕ
      ( m ^ℕ succ-ℕ n *ℕ 2)
      ( preserves-order-right-mul-ℕ (m ^ℕ succ-ℕ n) 2 m (leq-succ-le-ℕ 1 m H))
      ( inv (exp-succ-ℕ m (succ-ℕ n))))
```

### The exponential function $n \mapsto m^n$ if a decidable function

```agda
leq-one-exp-zero-ℕ :
  (n : ℕ) → exp-ℕ 0 n ≤-ℕ 1
leq-one-exp-zero-ℕ zero-ℕ = refl-leq-ℕ 1
leq-one-exp-zero-ℕ (succ-ℕ n) =
  concatenate-eq-leq-ℕ 1
    ( exp-succ-ℕ 0 n ∙ right-zero-law-mul-ℕ (0 ^ℕ n))
    ( star)

is-decidable-map-exp-zero-ℕ :
  is-decidable-map (exp-ℕ 0)
is-decidable-map-exp-zero-ℕ zero-ℕ =
  inl (1 , refl)
is-decidable-map-exp-zero-ℕ (succ-ℕ zero-ℕ) =
  inl (0 , refl)
is-decidable-map-exp-zero-ℕ (succ-ℕ (succ-ℕ n)) =
  inr
    ( λ (k , p) →
      concatenate-eq-leq-ℕ 1 (inv p) (leq-one-exp-zero-ℕ k))

is-decidable-map-exp-one-ℕ :
  is-decidable-map (exp-ℕ 1)
is-decidable-map-exp-one-ℕ n =
  rec-coproduct
    ( λ p → inl (0 , p))
    ( λ H → inr (λ (k , p) → H (inv (annihilation-law-exp-ℕ k) ∙ p)))
    ( has-decidable-equality-ℕ 1 n)

is-decidable-map-exp-ℕ :
  (m : ℕ) → is-decidable-map (exp-ℕ m)
is-decidable-map-exp-ℕ zero-ℕ =
  is-decidable-map-exp-zero-ℕ
is-decidable-map-exp-ℕ (succ-ℕ zero-ℕ) =
  is-decidable-map-exp-one-ℕ
is-decidable-map-exp-ℕ (succ-ℕ (succ-ℕ m)) =
  is-decidable-map-is-strictly-inflationary-map-ℕ
    ( is-strictly-inflationary-exp-ℕ (succ-ℕ (succ-ℕ m)) star)
```

### The exponential function is a decidable embedding if its base is strictly greater than $1$

```agda
is-decidable-emb-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-decidable-emb (exp-ℕ m)
pr1 (is-decidable-emb-exp-ℕ m H) = is-emb-exp-ℕ m H
pr2 (is-decidable-emb-exp-ℕ m H) = is-decidable-map-exp-ℕ m
```

### The exponential function is a finite map if its base is strictly greater than $1$

```agda
is-finite-map-exp-ℕ :
  (m : ℕ) → 1 <-ℕ m → is-finite-map (exp-ℕ m)
is-finite-map-exp-ℕ m H =
  is-finite-map-is-decidable-emb (is-decidable-emb-exp-ℕ m H)
```

### Exponentiation with base $m>1$ reflects divisibility into inequality

```agda
leq-exponent-div-exp-ℕ :
  (m n k : ℕ) → 1 <-ℕ m → div-ℕ (m ^ℕ k) (m ^ℕ n) → k ≤-ℕ n
leq-exponent-div-exp-ℕ m zero-ℕ zero-ℕ H K = refl-leq-ℕ 0
leq-exponent-div-exp-ℕ m zero-ℕ (succ-ℕ k) H K =
  neq-le-ℕ 1 m H
    ( inv (is-one-div-one-ℕ (m ^ℕ succ-ℕ k) K) ∙
      exp-succ-ℕ m k ∙
      ap
        ( λ x → m ^ℕ x *ℕ m)
        ( is-zero-leq-zero-ℕ k
          ( leq-exponent-div-exp-ℕ m 0 k H
            ( transitive-div-ℕ
              ( m ^ℕ k)
              ( m ^ℕ succ-ℕ k)
              ( 1)
              ( K)
              ( div-exp-succ-ℕ' m k)))) ∙
      left-unit-law-mul-ℕ m)
leq-exponent-div-exp-ℕ m (succ-ℕ n) zero-ℕ H K = leq-zero-ℕ (succ-ℕ n)
leq-exponent-div-exp-ℕ m (succ-ℕ n) (succ-ℕ k) H K =
  leq-exponent-div-exp-ℕ m n k H
    ( reflects-div-right-mul-ℕ m
      ( m ^ℕ k)
      ( m ^ℕ n)
      ( is-nonzero-le-ℕ 1 m H)
      ( concatenate-eq-div-eq-ℕ (inv (exp-succ-ℕ m k)) K (exp-succ-ℕ m n)))
```

### If $m^k \mid m^n$ and $m$ is nonzero, then its quotient is $m^{d(n,k)}$

In the case where $m=0$ we have $0^n \mid 0^n$. For any nonzero number $n$ this
would give $0 \mid 0$. The quotient of $0$ divided by $0$ is the unique number
$k \leq 0$ such that $k\cdot 0=0$, i.e., it is $0$. However, since $d(n,n)=0$ we
have $m^{d(n,n)}=1$, which isn't the quotient under our definitions.

```agda
valuation-is-exponent-div-exp-exp-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ m → div-ℕ (m ^ℕ k) (m ^ℕ n) → ℕ
valuation-is-exponent-div-exp-exp-ℕ m n k H K =
  dist-ℕ n k

eq-valuation-is-exponent-div-exp-exp-ℕ :
  (m n k : ℕ) (H : is-nonzero-ℕ m) (K : div-ℕ (m ^ℕ k) (m ^ℕ n)) →
  exp-ℕ m (valuation-is-exponent-div-exp-exp-ℕ m n k H K) ＝
  quotient-div-ℕ (m ^ℕ k) (m ^ℕ n) K
eq-valuation-is-exponent-div-exp-exp-ℕ zero-ℕ n k H K =
  ex-falso (H refl)
eq-valuation-is-exponent-div-exp-exp-ℕ (succ-ℕ zero-ℕ) n k H K =
  annihilation-law-exp-ℕ (dist-ℕ n k) ∙
  compute-quotient-div-ℕ
    ( inv (annihilation-law-exp-ℕ k))
    ( inv (annihilation-law-exp-ℕ n))
    ( refl-div-ℕ 1)
    ( K)
eq-valuation-is-exponent-div-exp-exp-ℕ (succ-ℕ (succ-ℕ m)) n k H K =
  is-injective-left-mul-ℕ
    ( succ-ℕ (succ-ℕ m) ^ℕ k)
    ( is-nonzero-exp-ℕ (succ-ℕ (succ-ℕ m)) k H)
    ( inv (left-distributive-exp-add-ℕ k (dist-ℕ n k)) ∙
      ap (succ-ℕ (succ-ℕ m) ^ℕ_) (ap (k +ℕ_) (symmetric-dist-ℕ n k) ∙
      is-difference-dist-ℕ k n
        ( leq-exponent-div-exp-ℕ (succ-ℕ (succ-ℕ m)) n k star K)) ∙
      inv
        ( eq-quotient-div-ℕ'
          ( succ-ℕ (succ-ℕ m) ^ℕ k)
          ( succ-ℕ (succ-ℕ m) ^ℕ n)
          ( K)))

is-exponent-div-exp-exp-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ m → (K : div-ℕ (m ^ℕ k) (m ^ℕ n)) →
  is-exponential-ℕ m (quotient-div-ℕ (m ^ℕ k) (m ^ℕ n) K)
pr1 (is-exponent-div-exp-exp-ℕ m n k H K) =
  valuation-is-exponent-div-exp-exp-ℕ m n k H K
pr2 (is-exponent-div-exp-exp-ℕ m n k H K) =
  eq-valuation-is-exponent-div-exp-exp-ℕ m n k H K
```
