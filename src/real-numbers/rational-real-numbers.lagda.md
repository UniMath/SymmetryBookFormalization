# Rational real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.rational-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The type of [rationals](elementary-number-theory.rational-numbers.md) `ℚ`
[embeds](foundation-core.embeddings.md) into the type of
[Dedekind reals](real-numbers.dedekind-real-numbers.md) `ℝ`. We call numbers in
the [image](foundation.images.md) of this embedding
{{#concept "rational real numbers" Agda=Rational-ℝ}}.

## Definitions

### Strict inequality on rationals gives Dedekind cuts

```agda
is-dedekind-lower-upper-real-ℚ :
  (x : ℚ) →
  is-dedekind-lower-upper-ℝ
    ( lower-real-ℚ x)
    ( upper-real-ℚ x)
is-dedekind-lower-upper-real-ℚ x =
  (λ q (H , K) → asymmetric-le-ℚ q x H K) ,
  located-le-ℚ x
```

### The canonical map from `ℚ` to `ℝ`

```agda
real-ℚ : ℚ → ℝ lzero
real-ℚ x = (lower-real-ℚ x , upper-real-ℚ x , is-dedekind-lower-upper-real-ℚ x)
```

### Zero as a real number

```agda
zero-ℝ : ℝ lzero
zero-ℝ = real-ℚ zero-ℚ
```

### The property of being a rational real number

```agda
module _
  {l : Level} (x : ℝ l) (p : ℚ)
  where

  is-rational-ℝ-Prop : Prop l
  is-rational-ℝ-Prop =
    (¬' (lower-cut-ℝ x p)) ∧ (¬' (upper-cut-ℝ x p))

  is-rational-ℝ : UU l
  is-rational-ℝ = type-Prop is-rational-ℝ-Prop
```

```agda
all-eq-is-rational-ℝ :
  {l : Level} (x : ℝ l) (p q : ℚ) →
  is-rational-ℝ x p →
  is-rational-ℝ x q →
  p ＝ q
all-eq-is-rational-ℝ x p q H H' =
  trichotomy-le-ℚ p q left-case id right-case
  where
  left-case : le-ℚ p q → p ＝ q
  left-case I =
    ex-falso
      ( elim-disjunction
        ( empty-Prop)
        ( pr1 H)
        ( pr2 H')
        ( is-located-lower-upper-cut-ℝ x p q I))

  right-case : le-ℚ q p → p ＝ q
  right-case I =
    ex-falso
      ( elim-disjunction
        ( empty-Prop)
        ( pr1 H')
        ( pr2 H)
        ( is-located-lower-upper-cut-ℝ x q p I))

is-prop-rational-real : {l : Level} (x : ℝ l) → is-prop (Σ ℚ (is-rational-ℝ x))
is-prop-rational-real x =
  is-prop-all-elements-equal
    ( λ p q →
      eq-type-subtype
        ( is-rational-ℝ-Prop x)
        ( all-eq-is-rational-ℝ x (pr1 p) (pr1 q) (pr2 p) (pr2 q)))
```

### The subtype of rational reals

```agda
subtype-rational-real : {l : Level} → ℝ l → Prop l
subtype-rational-real x =
  Σ ℚ (is-rational-ℝ x) , is-prop-rational-real x

Rational-ℝ : (l : Level) → UU (lsuc l)
Rational-ℝ l =
  type-subtype subtype-rational-real

module _
  {l : Level} (x : Rational-ℝ l)
  where

  real-rational-ℝ : ℝ l
  real-rational-ℝ = pr1 x

  rational-rational-ℝ : ℚ
  rational-rational-ℝ = pr1 (pr2 x)

  is-rational-rational-ℝ : is-rational-ℝ real-rational-ℝ rational-rational-ℝ
  is-rational-rational-ℝ = pr2 (pr2 x)
```

## Properties

### The real embedding of a rational number is rational

```agda
is-rational-real-ℚ : (p : ℚ) → is-rational-ℝ (real-ℚ p) p
is-rational-real-ℚ p = (irreflexive-le-ℚ p , irreflexive-le-ℚ p)
```

### Rational real numbers are embedded rationals

```agda
opaque
  unfolding sim-ℝ

  sim-rational-ℝ :
    {l : Level} →
    (x : Rational-ℝ l) →
    sim-ℝ (real-rational-ℝ x) (real-ℚ (rational-rational-ℝ x))
  pr1 (sim-rational-ℝ (x , q , q∉lx , q∉ux)) p p∈lx =
    trichotomy-le-ℚ
      ( p)
      ( q)
      ( id)
      ( λ p=q → ex-falso (q∉lx (tr (is-in-lower-cut-ℝ x) p=q p∈lx)))
      ( λ q<p → ex-falso (q∉lx (le-lower-cut-ℝ x q p q<p p∈lx)))
  pr2 (sim-rational-ℝ (x , q , q∉lx , q∉ux)) p p<q =
    elim-disjunction
      ( lower-cut-ℝ x p)
      ( id)
      ( ex-falso ∘ q∉ux)
      ( is-located-lower-upper-cut-ℝ x p q p<q)

eq-real-rational-is-rational-ℝ :
  (x : ℝ lzero) (q : ℚ) (H : is-rational-ℝ x q) → real-ℚ q ＝ x
eq-real-rational-is-rational-ℝ x q H =
  inv (eq-sim-ℝ {lzero} {x} {real-ℚ q} (sim-rational-ℝ (x , q , H)))
```

### The canonical map from rationals to rational reals

```agda
rational-real-ℚ : ℚ → Rational-ℝ lzero
rational-real-ℚ q = (real-ℚ q , q , is-rational-real-ℚ q)
```

### The rationals and rational reals are equivalent

```agda
is-section-rational-real-ℚ :
  (q : ℚ) →
  rational-rational-ℝ (rational-real-ℚ q) ＝ q
is-section-rational-real-ℚ q = refl

is-retraction-rational-real-ℚ :
  (x : Rational-ℝ lzero) →
  rational-real-ℚ (rational-rational-ℝ x) ＝ x
is-retraction-rational-real-ℚ (x , q , H) =
  eq-type-subtype
    subtype-rational-real
    ( ap real-ℚ α ∙ eq-real-rational-is-rational-ℝ x q H)
  where
    α : rational-rational-ℝ (x , q , H) ＝ q
    α = refl

equiv-rational-real : Rational-ℝ lzero ≃ ℚ
pr1 equiv-rational-real = rational-rational-ℝ
pr2 equiv-rational-real =
  section-rational-rational-ℝ , retraction-rational-rational-ℝ
  where
  section-rational-rational-ℝ : section rational-rational-ℝ
  section-rational-rational-ℝ =
    (rational-real-ℚ , is-section-rational-real-ℚ)

  retraction-rational-rational-ℝ : retraction rational-rational-ℝ
  retraction-rational-rational-ℝ =
    (rational-real-ℚ , is-retraction-rational-real-ℚ)
```
