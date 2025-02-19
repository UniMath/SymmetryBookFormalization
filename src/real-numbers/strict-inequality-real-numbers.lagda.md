# Strict inequality of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="real numbers" Agda=le-ℝ}}
on the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
presence of a [rational number](elementary-number-theory.rational-numbers.md)
between them. This is the definition used in {{#cite UF13}}, section 11.2.1.

```agda
le-ℝ-Prop : Large-Relation-Prop _⊔_ ℝ
le-ℝ-Prop x y = ∃ ℚ (λ q → upper-cut-ℝ x q ∧ lower-cut-ℝ y q)

le-ℝ : Large-Relation _⊔_ ℝ
le-ℝ x y = type-Prop (le-ℝ-Prop x y)

is-prop-le-ℝ : {l1 l2 : Level} → (x : ℝ l1) (y : ℝ l2) → is-prop (le-ℝ x y)
is-prop-le-ℝ x y = is-prop-type-Prop (le-ℝ-Prop x y)
```

## Properties

### Strict inequality on the reals is irreflexive

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  irreflexive-le-ℝ : ¬ (le-ℝ x x)
  irreflexive-le-ℝ =
    elim-exists
      ( empty-Prop)
      ( λ q (q-in-ux , q-in-lx) → is-disjoint-cut-ℝ x q (q-in-lx , q-in-ux))
```

### Strict inequality on the reals is asymmetric

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  asymmetric-le-ℝ : le-ℝ x y → ¬ (le-ℝ y x)
  asymmetric-le-ℝ x<y y<x =
    do
      ( p , x<p , p<y) ← x<y
      ( q , y<q , q<x) ← y<x
      rec-coproduct
        ( asymmetric-le-ℚ
            ( q)
            ( p)
            ( le-lower-upper-cut-ℝ x q p q<x x<p))
        ( not-leq-le-ℚ
            ( p)
            ( q)
            ( le-lower-upper-cut-ℝ y p q p<y y<q))
        ( decide-le-leq-ℚ p q)
    where open do-syntax-trunc-Prop empty-Prop
```

### Strict inequality on the reals is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-le-ℝ : le-ℝ y z → le-ℝ x y → le-ℝ x z
  transitive-le-ℝ y<z x<y =
    do
      ( p , x<p , p<y) ← x<y
      ( q , y<q , q<z) ← y<z
      intro-exists
        ( p)
        ( x<p ,
          le-lower-cut-ℝ z p q (le-lower-upper-cut-ℝ y p q p<y y<q) q<z)
    where open do-syntax-trunc-Prop (le-ℝ-Prop x z)
```

### The canonical map from rationals to reals preserves and reflects strict inequality

```agda
module _
  (x y : ℚ)
  where

  preserves-le-real-ℚ : le-ℚ x y → le-ℝ (real-ℚ x) (real-ℚ y)
  preserves-le-real-ℚ x<y =
    intro-exists
      ( mediant-ℚ x y)
      ( le-left-mediant-ℚ x y x<y , le-right-mediant-ℚ x y x<y)

  reflects-le-real-ℚ : le-ℝ (real-ℚ x) (real-ℚ y) → le-ℚ x y
  reflects-le-real-ℚ =
    elim-exists
      ( le-ℚ-Prop x y)
      ( λ q (x<q , q<y) → transitive-le-ℚ x q y q<y x<q)

  iff-le-real-ℚ : le-ℚ x y ↔ le-ℝ (real-ℚ x) (real-ℚ y)
  pr1 iff-le-real-ℚ = preserves-le-real-ℚ
  pr2 iff-le-real-ℚ = reflects-le-real-ℚ
```

### Concatenation rules for inequality and strict inequality on the real numbers

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  concatenate-le-leq-ℝ : le-ℝ x y → leq-ℝ y z → le-ℝ x z
  concatenate-le-leq-ℝ x<y y≤z =
    map-tot-exists (λ p → map-product id (y≤z p)) x<y

  concatenate-leq-le-ℝ : leq-ℝ x y → le-ℝ y z → le-ℝ x z
  concatenate-leq-le-ℝ x≤y =
    map-tot-exists
      ( λ p → map-product (forward-implication (leq-iff-ℝ' x y) x≤y p) id)
```

### The reals have no lower or upper bound

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  exists-lesser-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop y x)
  exists-lesser-ℝ =
    map-exists
      ( λ y → le-ℝ y x)
      ( real-ℚ)
      ( λ q → forward-implication (is-rounded-lower-cut-ℝ x q))
      ( is-inhabited-lower-cut-ℝ x)

  exists-greater-ℝ : exists (ℝ lzero) (λ y → le-ℝ-Prop x y)
  exists-greater-ℝ =
    do
      q , x<q ← is-inhabited-upper-cut-ℝ x
      r , r<q , x<r ← forward-implication (is-rounded-upper-cut-ℝ x q) x<q
      intro-exists (real-ℚ q) (intro-exists r (x<r , r<q))
    where open do-syntax-trunc-Prop (∃ (ℝ lzero) (le-ℝ-Prop x))
```

### Negation reverses the strict ordering of real numbers

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  reverses-order-neg-ℝ : le-ℝ x y → le-ℝ (neg-ℝ y) (neg-ℝ x)
  reverses-order-neg-ℝ x<y =
    do
      ( p , x<p , p<y) ← x<y
      intro-exists
        (neg-ℚ p)
        ( tr (is-in-lower-cut-ℝ y) (inv (neg-neg-ℚ p)) p<y ,
          tr (is-in-upper-cut-ℝ x) (inv (neg-neg-ℚ p)) x<p)
    where open do-syntax-trunc-Prop (le-ℝ-Prop (neg-ℝ y) (neg-ℝ x))
```

### If `x` is less than `y`, then `y` is not less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-leq-le-ℝ : le-ℝ x y → ¬ (leq-ℝ y x)
  not-leq-le-ℝ x<y y≤x =
    elim-exists
      ( empty-Prop)
      ( λ q (q-in-ux , q-in-ly) →
        is-disjoint-cut-ℝ x q (y≤x q q-in-ly , q-in-ux))
      ( x<y)
```

### If `x` is not less than `y`, then `y` is less than or equal to `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-not-le-ℝ : ¬ (le-ℝ x y) → leq-ℝ y x
  leq-not-le-ℝ x≮y p p∈ly =
    elim-exists
      ( lower-cut-ℝ x p)
      ( λ q (p<q , q∈ly) →
        elim-disjunction
          ( lower-cut-ℝ x p)
          ( id)
          ( λ q∈ux → ex-falso (x≮y (intro-exists q (q∈ux , q∈ly))))
          ( is-located-lower-upper-cut-ℝ x p q p<q))
      ( forward-implication (is-rounded-lower-cut-ℝ y p) p∈ly)
```

### If `x` is less than or equal to `y`, then `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  not-le-leq-ℝ : leq-ℝ x y → ¬ (le-ℝ y x)
  not-le-leq-ℝ x≤y y<x = not-leq-le-ℝ y x y<x x≤y
```

### `x` is less than or equal to `y` if and only if `y` is not less than `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-iff-not-le-ℝ : leq-ℝ x y ↔ ¬ (le-ℝ y x)
  pr1 leq-iff-not-le-ℝ = not-le-leq-ℝ x y
  pr2 leq-iff-not-le-ℝ = leq-not-le-ℝ y x
```

### A rational is in the lower cut of `x` iff its real projection is less than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  le-iff-lower-cut-real-ℚ : is-in-lower-cut-ℝ x q ↔ le-ℝ (real-ℚ q) x
  le-iff-lower-cut-real-ℚ = is-rounded-lower-cut-ℝ x q

  le-lower-cut-real-ℚ : is-in-lower-cut-ℝ x q → le-ℝ (real-ℚ q) x
  le-lower-cut-real-ℚ = forward-implication le-iff-lower-cut-real-ℚ

  lower-cut-real-le-ℚ : le-ℝ (real-ℚ q) x → is-in-lower-cut-ℝ x q
  lower-cut-real-le-ℚ = backward-implication le-iff-lower-cut-real-ℚ
```

### A rational is in the upper cut of `x` iff its real projection is greater than `x`

```agda
module _
  {l : Level} (q : ℚ) (x : ℝ l)
  where

  le-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q → le-ℝ x (real-ℚ q)
  le-upper-cut-real-ℚ H =
    map-tot-exists
      ( λ p (p<q , p∈ux) → (p∈ux , p<q))
      ( forward-implication (is-rounded-upper-cut-ℝ x q) H)

  upper-cut-real-le-ℚ : le-ℝ x (real-ℚ q) → is-in-upper-cut-ℝ x q
  upper-cut-real-le-ℚ H =
    backward-implication
      ( is-rounded-upper-cut-ℝ x q)
      ( map-tot-exists (λ _ (p>x , p<q) → (p<q , p>x)) H)

  le-iff-upper-cut-real-ℚ : is-in-upper-cut-ℝ x q ↔ le-ℝ x (real-ℚ q)
  pr1 le-iff-upper-cut-real-ℚ = le-upper-cut-real-ℚ
  pr2 le-iff-upper-cut-real-ℚ = upper-cut-real-le-ℚ
```

### Strict inequality on the real numbers is dense

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  where

  dense-le-ℝ : le-ℝ x y → exists (ℝ lzero) (λ z → le-ℝ-Prop x z ∧ le-ℝ-Prop z y)
  dense-le-ℝ x<y =
    do
      ( q , x<q , q<y) ← x<y
      ( p , p<q , x<p) ← forward-implication (is-rounded-upper-cut-ℝ x q) x<q
      ( r , q<r , r<y) ← forward-implication (is-rounded-lower-cut-ℝ y q) q<y
      intro-exists
        ( real-ℚ q)
        ( intro-exists p (x<p , p<q) , intro-exists r (q<r , r<y))
    where
      open
        do-syntax-trunc-Prop
          ( ∃ (ℝ lzero) (λ z → le-ℝ-Prop x z ∧ le-ℝ-Prop z y))
```

### Strict inequality on the real numbers is cotransitive

```agda
cotransitive-le-ℝ : is-cotransitive-Large-Relation-Prop ℝ le-ℝ-Prop
cotransitive-le-ℝ x y z =
  elim-exists
    ( le-ℝ-Prop x z ∨ le-ℝ-Prop z y)
    ( λ q (x<q , q<y) →
      elim-exists
        ( le-ℝ-Prop x z ∨ le-ℝ-Prop z y)
        ( λ p (p<q , x<p) →
          elim-disjunction
            ( le-ℝ-Prop x z ∨ le-ℝ-Prop z y)
            ( λ p<z → inl-disjunction (intro-exists p (x<p , p<z)))
            ( λ z<q → inr-disjunction (intro-exists q (z<q , q<y)))
            ( is-located-lower-upper-cut-ℝ z p q p<q))
        ( forward-implication (is-rounded-upper-cut-ℝ x q) x<q))
```

## References

{{#bibliography}}
