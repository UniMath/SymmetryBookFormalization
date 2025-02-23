# Negation of lower and upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.negation-lower-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "negation" Disambiguation="of a one-sided Dedekind real number" Agda=neg-lower-ℝ Agda=neg-upper-ℝ}}
of a [lower Dedekind real number](real-numbers.lower-dedekind-real-numbers.md)
is an [upper Dedekind real number](real-numbers.upper-dedekind-real-numbers.md)
whose cut contains negations of elements in the lower cut, and vice versa.

## Definitions

### The negation of a lower Dedekind real, as an upper Dedekind real

```agda
module _
  {l : Level} (x : lower-ℝ l)
  where

  cut-neg-lower-ℝ : subtype l ℚ
  cut-neg-lower-ℝ p = cut-lower-ℝ x (neg-ℚ p)

  is-in-cut-neg-lower-ℝ : ℚ → UU l
  is-in-cut-neg-lower-ℝ = is-in-subtype cut-neg-lower-ℝ

  abstract
    is-inhabited-cut-neg-lower-ℝ : exists ℚ cut-neg-lower-ℝ
    is-inhabited-cut-neg-lower-ℝ =
      map-exists
        ( is-in-cut-neg-lower-ℝ)
        ( neg-ℚ)
        ( λ p → tr (is-in-cut-lower-ℝ x) (inv (neg-neg-ℚ p)))
        ( is-inhabited-cut-lower-ℝ x)

    is-rounded-cut-neg-lower-ℝ :
      (q : ℚ) →
      is-in-cut-neg-lower-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-neg-lower-ℝ p)
    pr1 (is-rounded-cut-neg-lower-ℝ q) -q<x =
      map-exists
        (λ p → le-ℚ p q × is-in-cut-neg-lower-ℝ p)
        ( neg-ℚ)
        ( λ p (-q<p , p<x) →
          tr (le-ℚ (neg-ℚ p)) (neg-neg-ℚ q) (neg-le-ℚ (neg-ℚ q) p -q<p) ,
          tr (is-in-cut-lower-ℝ x) (inv (neg-neg-ℚ p)) p<x)
        ( forward-implication (is-rounded-cut-lower-ℝ x (neg-ℚ q)) -q<x)
    pr2 (is-rounded-cut-neg-lower-ℝ q) =
      elim-exists
        ( cut-neg-lower-ℝ q)
        ( λ p (p<q , -q<x) →
          backward-implication
            ( is-rounded-cut-lower-ℝ x (neg-ℚ q))
            ( intro-exists (neg-ℚ p) (neg-le-ℚ p q p<q , -q<x)))

  neg-lower-ℝ : upper-ℝ l
  pr1 neg-lower-ℝ = cut-neg-lower-ℝ
  pr1 (pr2 neg-lower-ℝ) = is-inhabited-cut-neg-lower-ℝ
  pr2 (pr2 neg-lower-ℝ) = is-rounded-cut-neg-lower-ℝ
```

### The negation of an upper Dedekind real, as a lower Dedekind real

```agda
module _
  {l : Level} (x : upper-ℝ l)
  where

  cut-neg-upper-ℝ : subtype l ℚ
  cut-neg-upper-ℝ q = cut-upper-ℝ x (neg-ℚ q)

  is-in-cut-neg-upper-ℝ : ℚ → UU l
  is-in-cut-neg-upper-ℝ = is-in-subtype cut-neg-upper-ℝ

  abstract
    is-inhabited-cut-neg-upper-ℝ : exists ℚ cut-neg-upper-ℝ
    is-inhabited-cut-neg-upper-ℝ =
      map-exists
        ( is-in-cut-neg-upper-ℝ)
        ( neg-ℚ)
        ( λ p → tr (is-in-cut-upper-ℝ x) (inv (neg-neg-ℚ p)))
        ( is-inhabited-cut-upper-ℝ x)

    is-rounded-cut-neg-upper-ℝ :
      (q : ℚ) →
      is-in-cut-neg-upper-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-neg-upper-ℝ r)
    pr1 (is-rounded-cut-neg-upper-ℝ q) x<-q =
      map-exists
        ( λ r → le-ℚ q r × is-in-cut-neg-upper-ℝ r)
        ( neg-ℚ)
        ( λ p (p<-q , x<p) →
          tr
            ( λ x → le-ℚ x (neg-ℚ p))
            ( neg-neg-ℚ q)
            ( neg-le-ℚ p (neg-ℚ q) p<-q) ,
          tr (is-in-cut-upper-ℝ x) (inv (neg-neg-ℚ p)) x<p)
        ( forward-implication (is-rounded-cut-upper-ℝ x (neg-ℚ q)) x<-q)
    pr2 (is-rounded-cut-neg-upper-ℝ q) =
      elim-exists
        ( cut-neg-upper-ℝ q)
        ( λ r (q<r , x<-r) →
          backward-implication
            ( is-rounded-cut-upper-ℝ x (neg-ℚ q))
            ( intro-exists (neg-ℚ r) (neg-le-ℚ q r q<r , x<-r)))

  neg-upper-ℝ : lower-ℝ l
  pr1 neg-upper-ℝ = cut-neg-upper-ℝ
  pr1 (pr2 neg-upper-ℝ) = is-inhabited-cut-neg-upper-ℝ
  pr2 (pr2 neg-upper-ℝ) = is-rounded-cut-neg-upper-ℝ
```

### The negation of lower and upper Dedekind reals are mutual inverses

```agda
abstract
  is-retraction-neg-upper-ℝ :
    (l : Level) → is-retraction (neg-lower-ℝ {l}) (neg-upper-ℝ {l})
  is-retraction-neg-upper-ℝ l x =
    eq-eq-cut-lower-ℝ
      ( neg-upper-ℝ (neg-lower-ℝ x))
      ( x)
      ( eq-sim-subtype
        ( cut-neg-upper-ℝ (neg-lower-ℝ x))
        ( cut-lower-ℝ x)
        ( (λ p → tr (is-in-cut-lower-ℝ x) (neg-neg-ℚ p)) ,
          (λ p → tr (is-in-cut-lower-ℝ x) (inv (neg-neg-ℚ p)))))

  is-section-neg-upper-ℝ :
    (l : Level) → is-section (neg-lower-ℝ {l}) (neg-upper-ℝ {l})
  is-section-neg-upper-ℝ l x =
    eq-eq-cut-upper-ℝ
      ( neg-lower-ℝ (neg-upper-ℝ x))
      ( x)
      ( eq-sim-subtype
        ( cut-neg-lower-ℝ (neg-upper-ℝ x))
        ( cut-upper-ℝ x)
        ( (λ p → tr (is-in-cut-upper-ℝ x) (neg-neg-ℚ p)) ,
          (λ p → tr (is-in-cut-upper-ℝ x) (inv (neg-neg-ℚ p)))))

  is-equiv-neg-lower-ℝ : (l : Level) → is-equiv (neg-lower-ℝ {l})
  pr1 (pr1 (is-equiv-neg-lower-ℝ l)) = neg-upper-ℝ
  pr1 (pr2 (is-equiv-neg-lower-ℝ l)) = neg-upper-ℝ
  pr2 (pr1 (is-equiv-neg-lower-ℝ l)) = is-section-neg-upper-ℝ l
  pr2 (pr2 (is-equiv-neg-lower-ℝ l)) = is-retraction-neg-upper-ℝ l

  is-equiv-neg-upper-ℝ : (l : Level) → is-equiv (neg-upper-ℝ {l})
  pr1 (pr1 (is-equiv-neg-upper-ℝ l)) = neg-lower-ℝ
  pr1 (pr2 (is-equiv-neg-upper-ℝ l)) = neg-lower-ℝ
  pr2 (pr1 (is-equiv-neg-upper-ℝ l)) = is-retraction-neg-upper-ℝ l
  pr2 (pr2 (is-equiv-neg-upper-ℝ l)) = is-section-neg-upper-ℝ l
```

### The negation of a rational projected to a lower real is the projection of its negation as an upper real

```agda
neg-lower-real-ℚ :
  (q : ℚ) → neg-lower-ℝ (lower-real-ℚ q) ＝ upper-real-ℚ (neg-ℚ q)
neg-lower-real-ℚ q =
  eq-eq-cut-upper-ℝ
    ( neg-lower-ℝ (lower-real-ℚ q))
    ( upper-real-ℚ (neg-ℚ q))
    ( eq-sim-subtype
      ( cut-neg-lower-ℝ (lower-real-ℚ q))
      ( cut-upper-real-ℚ (neg-ℚ q))
      ( (λ p -p<q →
          tr (le-ℚ (neg-ℚ q)) (neg-neg-ℚ p) (neg-le-ℚ (neg-ℚ p) q -p<q)) ,
        (λ p -q<p →
          tr (le-ℚ (neg-ℚ p)) (neg-neg-ℚ q) (neg-le-ℚ (neg-ℚ q) p -q<p))))
```

### The negation of a rational projected to an upper real is the projection of its negation as a lower real

```agda
neg-upper-real-ℚ :
  (q : ℚ) → neg-upper-ℝ (upper-real-ℚ q) ＝ lower-real-ℚ (neg-ℚ q)
neg-upper-real-ℚ q =
  eq-eq-cut-lower-ℝ
    ( neg-upper-ℝ (upper-real-ℚ q))
    ( lower-real-ℚ (neg-ℚ q))
    ( eq-sim-subtype
      ( cut-neg-upper-ℝ (upper-real-ℚ q))
      ( cut-lower-real-ℚ (neg-ℚ q))
      ( (λ p q<-p →
          tr
            ( λ r → le-ℚ r (neg-ℚ q))
            ( neg-neg-ℚ p)
            ( neg-le-ℚ q (neg-ℚ p) q<-p)) ,
        (λ p p<-q →
          tr
            ( λ r → le-ℚ r (neg-ℚ p))
            ( neg-neg-ℚ q)
            ( neg-le-ℚ p (neg-ℚ q) p<-q))))
```
