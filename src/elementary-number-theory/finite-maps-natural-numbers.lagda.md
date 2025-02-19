# Finite maps into the natural numbers

```agda
module elementary-number-theory.finite-maps-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-subtypes-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-maps
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.decidable-subtypes
```

</details>

## Idea

A map $f : A \to \mathbb{N}$ is said to be a
{{#concept "finite map" Disambiguation="natural numbers"}} if its
[fibers](foundation-core.finite-types.md) are
[finite](univalent-combinatorics.finite-types.md).

Finite maps are
[decidable](elementary-number-theory.decidable-maps-natural-numbers.md). Every
finite map $f : \mathbb{N} \to \mathbb{N}$ has a definite lowest value, and for
every finite map $f : \mathbb{N} \to \mathbb{N}$ that takes a value below $B$
there is a largest number $k$ such that $f(k) \leq b$.

The condition that $f : \mathbb{N} \to \mathbb{N}$ is finite is equivalent to
the condition that for every natural number $n$, if $f$ has a value below $n$
there is a maximal number $k$ such that $f(k)\leq n$.

## Definitions

### The predicate of being a finite map into the natural numbers

```agda
module _
  {l : Level} {A : UU l} (f : A → ℕ)
  where

  is-finite-prop-map-ℕ : Prop l
  is-finite-prop-map-ℕ = is-finite-prop-map f

  is-finite-map-ℕ : UU l
  is-finite-map-ℕ = is-finite-map f

  is-prop-is-finite-map-ℕ : is-prop is-finite-map-ℕ
  is-prop-is-finite-map-ℕ = is-prop-is-finite-map f
```

### The maximal value-bound input property of a function on the natural numbers

The maximal value-bound input property asserts that for every natural number $n$
there is a maximal number $k$ for which $f(k)\leq n$. Note that it is not
necessarily the case that the value $f(k)$ is itself maximal.

This property doesn't seem to have a widely recognized name, so we use an
explicit descriptor. Suggestions are welcome.

```agda
module _
  (f : ℕ → ℕ) (n : ℕ)
  where

  is-value-bound-input-ℕ :
    (k : ℕ) → UU lzero
  is-value-bound-input-ℕ k =
    f k ≤-ℕ n

  is-prop-is-value-bound-input-ℕ :
    (k : ℕ) → is-prop (is-value-bound-input-ℕ k)
  is-prop-is-value-bound-input-ℕ k =
    is-prop-leq-ℕ (f k) n

  is-decidable-is-value-bound-input-ℕ :
    (k : ℕ) → is-decidable (is-value-bound-input-ℕ k)
  is-decidable-is-value-bound-input-ℕ k =
    is-decidable-leq-ℕ (f k) n

  is-value-bound-input-subtype-ℕ :
    subtype lzero ℕ
  pr1 (is-value-bound-input-subtype-ℕ k) =
    is-value-bound-input-ℕ k
  pr2 (is-value-bound-input-subtype-ℕ k) =
    is-prop-is-value-bound-input-ℕ k

  is-value-bound-input-decidable-subtype-ℕ :
    decidable-subtype lzero ℕ
  pr1 (is-value-bound-input-decidable-subtype-ℕ k) =
    is-value-bound-input-ℕ k
  pr1 (pr2 (is-value-bound-input-decidable-subtype-ℕ k)) =
    is-prop-is-value-bound-input-ℕ k
  pr2 (pr2 (is-value-bound-input-decidable-subtype-ℕ k)) =
    is-decidable-is-value-bound-input-ℕ k

maximal-value-bound-input-property-ℕ :
  (ℕ → ℕ) → UU lzero
maximal-value-bound-input-property-ℕ f =
  (n k : ℕ) → f k ≤-ℕ n → maximal-element-ℕ (is-value-bound-input-ℕ f n)
```

### The maximal structured value-bound input property of a function on the natural numbers

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-structured-value-bound-input-ℕ :
    (f : ℕ → ℕ) (n k : ℕ) → UU l
  is-structured-value-bound-input-ℕ f n k =
    f k ≤-ℕ n × P (f k)

  is-prop-is-structured-value-bound-input-ℕ :
    ((x : ℕ) → is-prop (P x)) →
    (f : ℕ → ℕ) (n k : ℕ) → is-prop (is-structured-value-bound-input-ℕ f n k)
  is-prop-is-structured-value-bound-input-ℕ H f n k =
    is-prop-product (is-prop-leq-ℕ (f k) n) (H (f k))

  is-decidable-is-structured-value-bound-input-ℕ :
    is-decidable-fam P → (f : ℕ → ℕ) (n k : ℕ) →
    is-decidable (is-structured-value-bound-input-ℕ f n k)
  is-decidable-is-structured-value-bound-input-ℕ d f n k =
    is-decidable-product (is-decidable-leq-ℕ (f k) n) (d (f k))

module _
  {l : Level} (P : ℕ → Prop l)
  where

  is-structured-value-bound-input-subtype-ℕ :
    (f : ℕ → ℕ) (n : ℕ) → subtype l ℕ
  pr1 (is-structured-value-bound-input-subtype-ℕ f n k) =
    is-structured-value-bound-input-ℕ (type-Prop ∘ P) f n k
  pr2 (is-structured-value-bound-input-subtype-ℕ f n k) =
    is-prop-is-structured-value-bound-input-ℕ
      ( type-Prop ∘ P)
      ( is-prop-type-Prop ∘ P)
      ( f)
      ( n)
      ( k)

module _
  {l : Level} (P : decidable-subtype l ℕ)
  where

  is-structured-value-bound-input-decidable-subtype-ℕ :
    (f : ℕ → ℕ) (n : ℕ) → decidable-subtype l ℕ
  pr1 (is-structured-value-bound-input-decidable-subtype-ℕ f n k) =
    is-structured-value-bound-input-ℕ (is-in-decidable-subtype P) f n k
  pr1 (pr2 (is-structured-value-bound-input-decidable-subtype-ℕ f n k)) =
    is-prop-is-structured-value-bound-input-ℕ
      ( is-in-decidable-subtype P)
      ( is-prop-is-in-decidable-subtype P)
      ( f)
      ( n)
      ( k)
  pr2 (pr2 (is-structured-value-bound-input-decidable-subtype-ℕ f n k)) =
    is-decidable-is-structured-value-bound-input-ℕ
      ( is-in-decidable-subtype P)
      ( is-decidable-decidable-subtype P)
      ( f)
      ( n)
      ( k)

maximal-structured-value-bound-input-property-ℕ :
  {l : Level} (P : ℕ → UU l) → (ℕ → ℕ) → UU l
maximal-structured-value-bound-input-property-ℕ P f =
  (n k : ℕ) → f k ≤-ℕ n → P (f k) →
  maximal-element-ℕ (is-structured-value-bound-input-ℕ P f n)
```

## Properties

### Any finite map on the natural numbers satisfies the maximal value-bound input property

**Proof.** Consider a map $f : \mathbb{N} \to \mathbb{N}$ with finite fibers,
and consider natural numbers $n$ and $k$ such that $f(k) \leq n$. Since $f$ has
finite fibers, it follows that the type

$$
  \sum_{i:\mathbb{N}}f(i)\leq n
$$

is a finite decidable subtype of the natural numbers, with at least one element.

For the converse, suppose that $f$ satisfies the maximal value-bound input
property. The fiber of $f$ at $n$ is a decidable subtype of the type

$$
  \sum_{i:\mathbb{N}}f(i)\leq n.
$$

Since the type above itself is a decidable subtype of the natural numbers with a
maximal element, it is finite. It therefore follows that the fiber of $f$ at $n$
is finite.

```agda
module _
  (f : ℕ → ℕ) (H : is-finite-map-ℕ f)
  where

  is-finite-is-value-bound-input-decidable-subtype-ℕ :
    (n : ℕ) → is-finite (type-subtype (is-value-bound-input-subtype-ℕ f n))
  is-finite-is-value-bound-input-decidable-subtype-ℕ zero-ℕ =
    is-finite-equiv'
      ( equiv-tot
        ( λ x →
          equiv-iff-is-prop
            ( is-prop-is-value-bound-input-ℕ f 0 x)
            ( is-set-ℕ (f x) 0)
            ( is-zero-leq-zero-ℕ (f x))
            ( leq-eq-ℕ (f x) 0)))
      ( H 0)
  is-finite-is-value-bound-input-decidable-subtype-ℕ (succ-ℕ n) =
    is-finite-equiv'
      ( left-distributive-Σ-coproduct ℕ _ _ ∘e
        ( equiv-tot (λ x → compute-leq-succ-ℕ (f x) n)))
      ( is-finite-coproduct
        ( is-finite-is-value-bound-input-decidable-subtype-ℕ n)
        ( H (succ-ℕ n)))

  maximal-value-bound-input-property-is-finite-map-ℕ :
    maximal-value-bound-input-property-ℕ f
  maximal-value-bound-input-property-is-finite-map-ℕ n k K =
    maximal-element-is-finite-decidable-subtype-ℕ
      ( is-value-bound-input-decidable-subtype-ℕ f n)
      ( is-finite-is-value-bound-input-decidable-subtype-ℕ n)
      ( unit-trunc-Prop (k , K))

  nat-maximal-value-bound-input-property-is-finite-map-ℕ :
    (n k : ℕ) → f k ≤-ℕ n → ℕ
  nat-maximal-value-bound-input-property-is-finite-map-ℕ n k K =
    nat-maximal-element-ℕ
      ( is-value-bound-input-ℕ f n)
      ( maximal-value-bound-input-property-is-finite-map-ℕ n k K)

  is-upper-bound-nat-maximal-value-bound-input-property-is-finite-map-ℕ :
    (n k : ℕ) (K : f k ≤-ℕ n) (x : ℕ) → f x ≤-ℕ n →
    x ≤-ℕ nat-maximal-value-bound-input-property-is-finite-map-ℕ n k K
  is-upper-bound-nat-maximal-value-bound-input-property-is-finite-map-ℕ n k K =
    is-upper-bound-maximal-element-ℕ
      ( is-value-bound-input-ℕ f n)
      ( maximal-value-bound-input-property-is-finite-map-ℕ n k K)

  is-value-bound-input-maximal-value-bound-input-property-is-finite-map-ℕ :
    (n k : ℕ) (K : f k ≤-ℕ n) →
    is-value-bound-input-ℕ f n
      ( nat-maximal-value-bound-input-property-is-finite-map-ℕ n k K)
  is-value-bound-input-maximal-value-bound-input-property-is-finite-map-ℕ
    n k K =
    structure-maximal-element-ℕ
      ( is-value-bound-input-ℕ f n)
      ( maximal-value-bound-input-property-is-finite-map-ℕ n k K)
```

### Any finite map on the natural numbers satisfies the maximal structured value-bound input property

Consider the following data:

- A family $P$ of decidable types over the natural numbers
- A finite map $f$
- A natural number $n$
- A natural number $k$ such that $f(k) \leq n$ equipped with an element of type
  $P(f(k))$.

Then there is a largest natural number $m$ such that $f(m) \leq n$ equipped with
an element of type $P(f(m))$.

**Example.** For any natural number $1 \leq n$ there exists a largest number $m$
such that $m^2 \mid n$. Indeed, if we let $P(x)$ be the decidable predicate that
$x$ divides $n$ and $f$ the
[squaring function](elementary-number-theory.squares-natural-numbers.md). The
squaring function has finite fibers and we have $1^2 \leq n$ and $1^2 \mid n$.
The theorem thus gives us a largest number $m$ such that $m^2 \mid n$. We carry
out this example in the module about
[Square-free decompositions](elementary-number-theory.square-free-decompositions-natural-numbers.md).

```agda
module _
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (f : ℕ → ℕ) (H : is-finite-map-ℕ f)
  where

  maximal-structured-value-bound-input-property-is-finite-map-ℕ :
    maximal-structured-value-bound-input-property-ℕ P f
  maximal-structured-value-bound-input-property-is-finite-map-ℕ n k K p =
    ( ( nat-bounded-maximal-element-ℕ
        ( λ x → is-value-bound-input-ℕ f n x × P (f x))
        ( nat-maximal-value-bound-input-property-is-finite-map-ℕ f H n k K)
        ( b)) ,
      ( structure-bounded-maximal-element-ℕ
          ( λ x → is-value-bound-input-ℕ f n x × P (f x))
          ( nat-maximal-value-bound-input-property-is-finite-map-ℕ f H n k K)
          ( b)) ,
      ( λ x (u , v) →
        is-upper-bound-bounded-maximal-element-ℕ
          ( λ x → is-value-bound-input-ℕ f n x × P (f x))
          ( nat-maximal-value-bound-input-property-is-finite-map-ℕ f H n k K)
          ( b)
          ( x)
          ( ( is-upper-bound-nat-maximal-value-bound-input-property-is-finite-map-ℕ
              f H n k K x u) ,
            ( u) ,
            ( v))))
    where

    b =
      bounded-maximal-element-instance-ℕ
        ( λ x → is-value-bound-input-ℕ f n x × P (f x))
        ( λ x → is-decidable-product (is-decidable-leq-ℕ (f x) n) (d (f x)))
        ( nat-maximal-value-bound-input-property-is-finite-map-ℕ f H n k K)
        ( k)
        ( is-upper-bound-nat-maximal-value-bound-input-property-is-finite-map-ℕ
          f H n k K k K)
        ( K , p)
```
