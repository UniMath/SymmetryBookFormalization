# Compactness of the type of increasing binary sequences

```agda
{-# OPTIONS --guardedness #-}

module set-theory.compactness-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.transport-along-identifications
open import foundation.functoriality-coproduct-types
open import foundation.negation
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.decidable-type-families
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.universal-decidability-search
open import foundation.decidability-search
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import set-theory.increasing-binary-sequences
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import elementary-number-theory.conatural-numbers
open import foundation.negated-equality
open import foundation.propositions
open import foundation.retractions
open import foundation.decidability-search
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.decidability-search
open import foundation.universal-decidability-search
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
open import set-theory.increasing-binary-sequences
open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
```

</details>

## Idea

The type of
[increasing binary sequences](set-theory.increasing-binary-sequences.md) is
compact. {{#cite TypeTopology}}

## Theorem

The following formalization is more or less a direct translation from
formalizations written by Martín Escardó {{#cite TypeTopology}}.

```agda
abstract
  has-pointed-decidability-search-bool-ℕ∞↑' :
    has-pointed-decidability-search-bool' ℕ∞↑
  has-pointed-decidability-search-bool-ℕ∞↑' p = (a , Lemma)
    where
    a : ℕ∞↑
    a = force-ℕ∞↑ (p ∘ inclusion-ℕ∞↑-ℕ)

    Dagger₀ : (n : ℕ) → a ＝ inclusion-ℕ∞↑-ℕ n → p (inclusion-ℕ∞↑-ℕ n) ＝ true
    Dagger₀ 0 r = ap (λ x → pr1 x 0) r
    Dagger₀ (succ-ℕ n) r =
      ( inv
        ( ap
          ( or-bool (p (inclusion-ℕ∞↑-ℕ (succ-ℕ n))))
          ( ap (λ x → pr1 x n) r ∙ le-succ-ℕ-ℕ∞↑ n) ∙
            right-unit-law-or-bool)) ∙
      ( ap (λ x → pr1 x (succ-ℕ n)) r) ∙
      ( refl-leq-ℕ-ℕ∞↑ n)

    Dagger₁ : a ＝ infinity-ℕ∞↑ → (n : ℕ) → p (inclusion-ℕ∞↑-ℕ n) ＝ false
    Dagger₁ r 0 =  ap (λ - →  pr1 - 0) r
    Dagger₁ r (succ-ℕ n) =
      ( inv
        ( ( ap
            ( or-bool (p (inclusion-ℕ∞↑-ℕ (succ-ℕ n))))
            ( ap (λ x → pr1 x n) r)) ∙
          ( right-unit-law-or-bool))) ∙
      ( ap (λ x → pr1 x (succ-ℕ n)) r)

    Lemma₀ : (n : ℕ) → a ＝ inclusion-ℕ∞↑-ℕ n → p a ＝ true
    Lemma₀ n t = ap p t ∙ Dagger₀ n t

    Claim₀ : p a ＝ false → (n : ℕ) → a ≠ inclusion-ℕ∞↑-ℕ n
    Claim₀ r n s = neq-false-true-bool (inv r ∙ Lemma₀ n s)

    Claim₁ : p a ＝ false → a ＝ infinity-ℕ∞↑
    Claim₁ r = eq-infinity-is-not-in-image-inclusion-ℕ∞↑-ℕ a (Claim₀ r)

    Claim₂ : p a ＝ false → (n : ℕ) → p (inclusion-ℕ∞↑-ℕ n) ＝ false
    Claim₂ r = Dagger₁ (Claim₁ r)

    Claim₃ : p a ＝ false → p infinity-ℕ∞↑ ＝ false
    Claim₃ r = ap p (inv (Claim₁ r)) ∙ r

    Lemma : p a ＝ false → (v : ℕ∞↑) → p v ＝ false
    Lemma r =
      htpy-ℕ∞↑-htpy-ℕ
        ( λ _ → has-double-negation-stable-equality-bool)
        ( Claim₂ r)
        ( Claim₃ r)
```

Thank you Professor Escardó! 🙏

## Corollaries

### The type of increasing binary sequences has decidability search

```agda
abstract
  has-pointed-decidability-search-bool-ℕ∞↑ :
    has-pointed-decidability-search-bool ℕ∞↑
  has-pointed-decidability-search-bool-ℕ∞↑ =
    flip-has-pointed-decidability-search-bool
      ( has-pointed-decidability-search-bool-ℕ∞↑')

has-pointed-decidability-search-on-subtypes-ℕ∞↑ :
  has-pointed-decidability-search-on-subtypes ℕ∞↑
has-pointed-decidability-search-on-subtypes-ℕ∞↑ =
  has-pointed-decidability-search-on-subtypes-has-pointed-decidability-search-bool
    ( has-pointed-decidability-search-bool-ℕ∞↑)

has-pointed-decidability-search-ℕ∞↑ : has-pointed-decidability-search ℕ∞↑
has-pointed-decidability-search-ℕ∞↑ =
  has-pointed-decidability-search-has-pointed-decidability-search-on-subtypes
    ( has-pointed-decidability-search-on-subtypes-ℕ∞↑)

has-decidability-search-ℕ∞↑ : has-decidability-search ℕ∞↑
has-decidability-search-ℕ∞↑ =
  has-decidability-search-has-pointed-decidability-search
    ( has-pointed-decidability-search-ℕ∞↑)
```

### The type of increasing binary sequences has universal decidability search

```agda
has-universal-decidability-search-ℕ∞↑ : has-universal-decidability-search ℕ∞↑
has-universal-decidability-search-ℕ∞↑ =
  has-universal-decidability-search-has-decidability-search
    ( has-decidability-search-ℕ∞↑)
```

## References

- [`TypeTopology.GenericConvergentSequenceCompactness`](https://martinescardo.github.io/TypeTopology/TypeTopology.GenericConvergentSequenceCompactness.html)
  at TypeTopology {{#cite TypeTopology}}

{{#bibliography}}
