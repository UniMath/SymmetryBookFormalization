# 2-Adic decomposition

```agda
module elementary-number-theory.2-adic-decomposition where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.largest-power-divisors-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

The {{#concept "2-adic decomposition" Agda=2-adic-decomposition-ℕ}} of a
[natural number](elementary-number-theory.natural-numbers.md) $n$ is a
factorization of $n$ into a
[power](elementary-number-theory.exponentiation-natural-numbers.md) of $2$ and
an [odd](elementary-number-theory.parity-natural-numbers.md) natural number.

The $2$-adic decomposition of the natural numbers can be used to construct an
[equivalence](foundation-core.equivalences.md)
$\mathbb{N}\times\mathbb{N} \simeq \mathbb{N}$ by mapping

$$
  (m , n) \mapsto 2^m(2n + 1) - 1.
$$

The exponent $k$ such that the 2-adic decomposition of $n$ is $2^k \cdot m=n$ is
called the
{{#concept "2-adic valuation" Disambiguation="natural numbers" Agda=valuation-2-adic-decomposition-ℕ}}
of $n$.

## Definitions

### The $2$-adic composition function

```agda
2-adic-composition-ℕ : ℕ → ℕ → ℕ
2-adic-composition-ℕ k l = 2 ^ℕ k *ℕ odd-number-ℕ l
```

### The type of $2$-adic decompositions of a natural number

```agda
2-adic-decomposition-ℕ : ℕ → UU lzero
2-adic-decomposition-ℕ n =
  Σ ℕ (λ k → Σ ℕ (λ l → 2-adic-composition-ℕ k l ＝ n))

module _
  (n : ℕ) (d : 2-adic-decomposition-ℕ n)
  where

  fiber-2-adic-composition-2-adic-decomposition-ℕ :
    fiber (λ x → 2-adic-composition-ℕ (pr1 x) (pr2 x)) n
  fiber-2-adic-composition-2-adic-decomposition-ℕ =
    ((pr1 d , pr1 (pr2 d)) , pr2 (pr2 d))

  valuation-2-adic-decomposition-ℕ : ℕ
  valuation-2-adic-decomposition-ℕ = pr1 d

  exp-valuation-2-adic-decomposition-ℕ : ℕ
  exp-valuation-2-adic-decomposition-ℕ =
    2 ^ℕ valuation-2-adic-decomposition-ℕ

  is-nonzero-exp-valuation-2-adic-decomposition-ℕ :
    is-nonzero-ℕ exp-valuation-2-adic-decomposition-ℕ
  is-nonzero-exp-valuation-2-adic-decomposition-ℕ =
    is-nonzero-exp-ℕ 2 valuation-2-adic-decomposition-ℕ (is-nonzero-succ-ℕ 1)

  index-odd-factor-2-adic-decomposition-ℕ : ℕ
  index-odd-factor-2-adic-decomposition-ℕ = pr1 (pr2 d)

  odd-factor-2-adic-decomposition-ℕ : ℕ
  odd-factor-2-adic-decomposition-ℕ =
    odd-number-ℕ index-odd-factor-2-adic-decomposition-ℕ

  is-odd-odd-factor-2-adic-decomposition-ℕ :
    is-odd-ℕ odd-factor-2-adic-decomposition-ℕ
  is-odd-odd-factor-2-adic-decomposition-ℕ =
    is-odd-odd-number-ℕ index-odd-factor-2-adic-decomposition-ℕ

  eq-2-adic-decomposition-ℕ :
    2-adic-composition-ℕ
      valuation-2-adic-decomposition-ℕ
      index-odd-factor-2-adic-decomposition-ℕ ＝
    n
  eq-2-adic-decomposition-ℕ = pr2 (pr2 d)

  div-exp-valuation-2-adic-decomposition-ℕ :
    div-ℕ exp-valuation-2-adic-decomposition-ℕ n
  pr1 div-exp-valuation-2-adic-decomposition-ℕ =
    odd-factor-2-adic-decomposition-ℕ
  pr2 div-exp-valuation-2-adic-decomposition-ℕ =
    commutative-mul-ℕ
      odd-factor-2-adic-decomposition-ℕ
      exp-valuation-2-adic-decomposition-ℕ ∙
    eq-2-adic-decomposition-ℕ

  is-power-divisor-exp-valuation-2-adic-decomposition-ℕ :
    is-power-divisor-ℕ 2 n
      exp-valuation-2-adic-decomposition-ℕ
  pr1 (pr1 (is-power-divisor-exp-valuation-2-adic-decomposition-ℕ)) =
    valuation-2-adic-decomposition-ℕ
  pr2 (pr1 (is-power-divisor-exp-valuation-2-adic-decomposition-ℕ)) =
    refl
  pr2 (is-power-divisor-exp-valuation-2-adic-decomposition-ℕ) =
    div-exp-valuation-2-adic-decomposition-ℕ

  is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ :
    is-largest-power-divisor-ℕ 2 n exp-valuation-2-adic-decomposition-ℕ
  pr1 is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ =
    is-power-divisor-exp-valuation-2-adic-decomposition-ℕ
  pr2 is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ y
    ((k , refl) , K) =
    leq-exponent-div-exp-ℕ
      ( 2)
      ( valuation-2-adic-decomposition-ℕ)
      ( k)
      ( star)
      ( div-exp-2-left-factor-div-exp-2-mul-ℕ k
        ( exp-valuation-2-adic-decomposition-ℕ)
        ( odd-factor-2-adic-decomposition-ℕ)
        ( concatenate-div-eq-ℕ K (inv eq-2-adic-decomposition-ℕ))
        ( is-odd-odd-factor-2-adic-decomposition-ℕ))
```

## Properties

### The type of 2-adic decompositions of any natural number is a proposition

```agda
eq-valuation-2-adic-decomposition-ℕ :
  (n : ℕ) (H K : 2-adic-decomposition-ℕ n) →
  valuation-2-adic-decomposition-ℕ n H ＝ valuation-2-adic-decomposition-ℕ n K
eq-valuation-2-adic-decomposition-ℕ n H K =
  eq-valuation-is-largest-power-divisor-ℕ 2 n
    ( exp-valuation-2-adic-decomposition-ℕ n H)
    ( exp-valuation-2-adic-decomposition-ℕ n K)
    ( star)
    ( is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ n H)
    ( is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ n K)

eq-exp-valuation-2-adic-decomposition-ℕ :
  (n : ℕ) (H K : 2-adic-decomposition-ℕ n) →
  exp-valuation-2-adic-decomposition-ℕ n H ＝
  exp-valuation-2-adic-decomposition-ℕ n K
eq-exp-valuation-2-adic-decomposition-ℕ n H K =
  ap (2 ^ℕ_) (eq-valuation-2-adic-decomposition-ℕ n H K)

eq-odd-factor-2-adic-decomposition-ℕ :
  (n : ℕ) (H K : 2-adic-decomposition-ℕ n) →
  odd-factor-2-adic-decomposition-ℕ n H ＝ odd-factor-2-adic-decomposition-ℕ n K
eq-odd-factor-2-adic-decomposition-ℕ n H K =
  is-injective-left-mul-ℕ
    ( exp-valuation-2-adic-decomposition-ℕ n H)
    ( is-nonzero-exp-valuation-2-adic-decomposition-ℕ n H)
    ( ( eq-2-adic-decomposition-ℕ n H) ∙
      ( inv (eq-2-adic-decomposition-ℕ n K)) ∙
      ( ap
        ( _*ℕ odd-factor-2-adic-decomposition-ℕ n K)
        ( inv (eq-exp-valuation-2-adic-decomposition-ℕ n H K))))

eq-index-odd-factor-2-adic-decomposition-ℕ :
  (n : ℕ) (H K : 2-adic-decomposition-ℕ n) →
  index-odd-factor-2-adic-decomposition-ℕ n H ＝
  index-odd-factor-2-adic-decomposition-ℕ n K
eq-index-odd-factor-2-adic-decomposition-ℕ n H K =
  is-injective-odd-number-ℕ (eq-odd-factor-2-adic-decomposition-ℕ n H K)

all-elements-equal-2-adic-decomposition-ℕ :
  (n : ℕ) → all-elements-equal (2-adic-decomposition-ℕ n)
all-elements-equal-2-adic-decomposition-ℕ n H@(k , m , p) K@(k' , m' , p') =
  eq-pair-Σ
    ( eq-valuation-2-adic-decomposition-ℕ n H K)
    ( eq-type-subtype
      ( λ x → Id-Prop ℕ-Set _ _)
      ( eq-index-odd-factor-2-adic-decomposition-ℕ n
        ( k' ,
          tr
            ( λ x → Σ ℕ (λ y → 2-adic-composition-ℕ x y ＝ n))
            ( eq-valuation-2-adic-decomposition-ℕ n H K)
            ( m , p))
        ( K)))

is-prop-2-adic-decomposition-ℕ :
  (n : ℕ) → is-prop (2-adic-decomposition-ℕ n)
is-prop-2-adic-decomposition-ℕ n =
  is-prop-all-elements-equal (all-elements-equal-2-adic-decomposition-ℕ n)
```

### The values of the $2$-adic composition function are nonzero

```agda
is-nonzero-2-adic-composition-ℕ :
  (k l : ℕ) → is-nonzero-ℕ (2-adic-composition-ℕ k l)
is-nonzero-2-adic-composition-ℕ k l =
  is-nonzero-mul-ℕ
    ( 2 ^ℕ k)
    ( odd-number-ℕ l)
    ( is-nonzero-exp-ℕ 2 k is-nonzero-two-ℕ)
    ( is-nonzero-odd-number-ℕ l)
```

### Any number that has a $2$-adic decomposition is nonzero

```agda
is-nonzero-2-adic-decomposition-ℕ :
  (n : ℕ) → 2-adic-decomposition-ℕ n → is-nonzero-ℕ n
is-nonzero-2-adic-decomposition-ℕ ._ (k , l , refl) =
  is-nonzero-2-adic-composition-ℕ k l
```

### Every odd number has a $2$-adic decomposition

```agda
2-adic-decomposition-is-odd-ℕ :
  (n : ℕ) → is-odd-ℕ n → 2-adic-decomposition-ℕ n
pr1 (2-adic-decomposition-is-odd-ℕ n H) =
  0
pr1 (pr2 (2-adic-decomposition-is-odd-ℕ n H)) =
  pr1 (has-odd-expansion-is-odd-ℕ n H)
pr2 (pr2 (2-adic-decomposition-is-odd-ℕ n H)) =
  left-unit-law-mul-ℕ _ ∙ pr2 (has-odd-expansion-is-odd-ℕ n H)
```

### Every nonzero natural number has a $2$-adic decomposition

```agda
module _
  (n : ℕ) (H : is-nonzero-ℕ n)
  where

  valuation-2-adic-decomposition-is-nonzero-ℕ :
    ℕ
  valuation-2-adic-decomposition-is-nonzero-ℕ =
    valuation-largest-power-divisor-ℕ 2 n star H

  exp-valuation-2-adic-decomposition-is-nonzero-ℕ :
    ℕ
  exp-valuation-2-adic-decomposition-is-nonzero-ℕ =
    2 ^ℕ valuation-2-adic-decomposition-is-nonzero-ℕ

  div-exp-valuation-2-adic-decomposition-is-nonzero-ℕ :
    div-ℕ exp-valuation-2-adic-decomposition-is-nonzero-ℕ n
  div-exp-valuation-2-adic-decomposition-is-nonzero-ℕ =
    div-largest-power-divisor-ℕ 2 n star H

  is-upper-bound-valuation-2-adic-decomposition-is-nonzero-ℕ :
    (k : ℕ) → div-ℕ (2 ^ℕ k) n →
    k ≤-ℕ valuation-2-adic-decomposition-is-nonzero-ℕ
  is-upper-bound-valuation-2-adic-decomposition-is-nonzero-ℕ =
    is-upper-bound-valuation-largest-power-divisor-ℕ 2 n star H

  odd-factor-2-adic-decomposition-is-nonzero-ℕ :
    ℕ
  odd-factor-2-adic-decomposition-is-nonzero-ℕ =
    quotient-div-ℕ
      ( exp-valuation-2-adic-decomposition-is-nonzero-ℕ)
      ( n)
      ( div-exp-valuation-2-adic-decomposition-is-nonzero-ℕ)

  is-odd-odd-factor-2-adic-decomposition-is-nonzero-ℕ :
    is-odd-ℕ odd-factor-2-adic-decomposition-is-nonzero-ℕ
  is-odd-odd-factor-2-adic-decomposition-is-nonzero-ℕ K =
    neg-succ-leq-ℕ
      ( valuation-2-adic-decomposition-is-nonzero-ℕ)
      ( is-upper-bound-valuation-2-adic-decomposition-is-nonzero-ℕ
        ( succ-ℕ valuation-2-adic-decomposition-is-nonzero-ℕ)
        ( tr
          ( is-divisor-ℕ n)
          ( inv (exp-succ-ℕ 2 valuation-2-adic-decomposition-is-nonzero-ℕ))
          ( div-div-quotient-div-ℕ 2 n
            ( 2 ^ℕ valuation-2-adic-decomposition-is-nonzero-ℕ)
            ( div-exp-valuation-2-adic-decomposition-is-nonzero-ℕ)
            ( K))))

  has-odd-expansion-odd-factor-2-adic-decomposition-is-nonzero-ℕ :
    has-odd-expansion-ℕ odd-factor-2-adic-decomposition-is-nonzero-ℕ
  has-odd-expansion-odd-factor-2-adic-decomposition-is-nonzero-ℕ =
    has-odd-expansion-is-odd-ℕ
      odd-factor-2-adic-decomposition-is-nonzero-ℕ
      is-odd-odd-factor-2-adic-decomposition-is-nonzero-ℕ

  index-odd-factor-2-adic-decomposition-is-nonzero-ℕ :
    ℕ
  index-odd-factor-2-adic-decomposition-is-nonzero-ℕ =
    pr1 has-odd-expansion-odd-factor-2-adic-decomposition-is-nonzero-ℕ

  eq-index-odd-factor-2-adic-decomposition-is-nonzero-ℕ :
    odd-number-ℕ index-odd-factor-2-adic-decomposition-is-nonzero-ℕ ＝
    odd-factor-2-adic-decomposition-is-nonzero-ℕ
  eq-index-odd-factor-2-adic-decomposition-is-nonzero-ℕ =
    pr2 has-odd-expansion-odd-factor-2-adic-decomposition-is-nonzero-ℕ

  eq-2-adic-decomposition-is-nonzero-ℕ :
    2-adic-composition-ℕ
      ( valuation-2-adic-decomposition-is-nonzero-ℕ)
      ( index-odd-factor-2-adic-decomposition-is-nonzero-ℕ) ＝
    n
  eq-2-adic-decomposition-is-nonzero-ℕ =
    ( ap
      ( 2 ^ℕ valuation-2-adic-decomposition-is-nonzero-ℕ *ℕ_)
      ( eq-index-odd-factor-2-adic-decomposition-is-nonzero-ℕ)) ∙
    ( eq-quotient-div-ℕ'
      ( 2 ^ℕ valuation-2-adic-decomposition-is-nonzero-ℕ)
      ( n)
      ( div-exp-valuation-2-adic-decomposition-is-nonzero-ℕ))

  2-adic-decomposition-is-nonzero-ℕ :
    2-adic-decomposition-ℕ n
  pr1 2-adic-decomposition-is-nonzero-ℕ =
    valuation-2-adic-decomposition-is-nonzero-ℕ
  pr1 (pr2 2-adic-decomposition-is-nonzero-ℕ) =
    index-odd-factor-2-adic-decomposition-is-nonzero-ℕ
  pr2 (pr2 2-adic-decomposition-is-nonzero-ℕ) =
    eq-2-adic-decomposition-is-nonzero-ℕ

  is-largest-power-divisor-exp-valuation-2-adic-decomposition-is-nonzero-ℕ :
    is-largest-power-divisor-ℕ 2 n
      exp-valuation-2-adic-decomposition-is-nonzero-ℕ
  is-largest-power-divisor-exp-valuation-2-adic-decomposition-is-nonzero-ℕ =
    is-largest-power-divisor-exp-valuation-2-adic-decomposition-ℕ n
      2-adic-decomposition-is-nonzero-ℕ
```

### A logical equivalence between the type of 2-adic decompositions and the fibers of the successor function

```agda
logical-equiv-fiber-2-adic-composition-fiber-succ-ℕ :
  (n : ℕ) →
  fiber (λ x → 2-adic-composition-ℕ (pr1 x) (pr2 x)) n ↔ fiber succ-ℕ n
pr1 (logical-equiv-fiber-2-adic-composition-fiber-succ-ℕ n) ((x , y) , p) =
  fiber-succ-is-successor-ℕ
    ( is-successor-is-nonzero-ℕ
      ( is-nonzero-2-adic-decomposition-ℕ n (x , y , p)))
pr2 (logical-equiv-fiber-2-adic-composition-fiber-succ-ℕ n) (m , refl) =
  fiber-2-adic-composition-2-adic-decomposition-ℕ n
    ( 2-adic-decomposition-is-nonzero-ℕ (succ-ℕ m) (is-nonzero-succ-ℕ m))
```

### The type of 2-adic decompositions of a nonzero natural number is contractible

```agda
is-contr-2-adic-decomposition-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-contr (2-adic-decomposition-ℕ n)
is-contr-2-adic-decomposition-ℕ n H =
  is-proof-irrelevant-is-prop
    ( is-prop-2-adic-decomposition-ℕ n)
    ( 2-adic-decomposition-is-nonzero-ℕ n H)
```

### The 2-adic composition function is a propositional map

```agda
is-prop-map-2-adic-composition-ℕ :
  is-prop-map (λ x → 2-adic-composition-ℕ (pr1 x) (pr2 x))
is-prop-map-2-adic-composition-ℕ n =
  is-prop-equiv
    ( associative-Σ ℕ _ _)
    ( is-prop-2-adic-decomposition-ℕ n)
```

### The 2-adic composition function is an embedding

```agda
is-emb-2-adic-composition-ℕ :
  is-emb (λ x → 2-adic-composition-ℕ (pr1 x) (pr2 x))
is-emb-2-adic-composition-ℕ =
  is-emb-is-prop-map is-prop-map-2-adic-composition-ℕ

2-adic-composition-emb-ℕ :
  ℕ × ℕ ↪ ℕ
pr1 2-adic-composition-emb-ℕ (x , y) = 2-adic-composition-ℕ x y
pr2 2-adic-composition-emb-ℕ = is-emb-2-adic-composition-ℕ
```

### The 2-adic composition function is injective

```agda
is-injective-2-adic-composition-ℕ :
  is-injective (λ x → 2-adic-composition-ℕ (pr1 x) (pr2 x))
is-injective-2-adic-composition-ℕ =
  is-injective-is-emb is-emb-2-adic-composition-ℕ
```
