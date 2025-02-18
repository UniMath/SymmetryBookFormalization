# Cantor's diagonal argument

```agda
module set-theory.cantors-diagonal-argument where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.double-negation
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.propositions

open import logic.propositionally-decidable-types

open import set-theory.countable-sets
open import set-theory.infinite-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

{{#concept "Cantor's diagonal argument" Agda=diagonal-argument-Cantor WD="Cantor's diagonal argument" WDID=Q729471}}
is the argument Georg Cantor used to establish that
[sets](foundation-core.sets.md) of infinite [sequences](foundation.sequences.md)
of elements from a ([discrete](foundation-core.discrete-types.md)) set with
[two distinct elements](foundation.pairs-of-distinct-elements.md) are
[uncountable](set-theory.uncountable-sets.md). The argument first appeared in
{{#cite Cantor1890/91}}. Although it is not the first uncountability argument to
be published, Cantor's diagonal argument is his first to employ a proof
technique known as _diagonalization_. This proof technique was also used to give
a generalization of the uncountability result in what is now known as
[Cantor's theorem](foundation.cantors-theorem.md).

## Lemma

Every type `X` with an [isolated](foundation.isolated-elements.md) element `m`
and another [distinct](foundation.negated-equality.md) element `w` has an
endofunction with [no](foundation-core.negation.md)
[fixed points](foundation.fixed-points-endofunctions.md).

```agda
module _
  {l1 : Level} {X : UU l1} {m w : X}
  (H : (x : X) → is-inhabited-or-empty (m ＝ x)) (d : m ≠ w)
  where

  endomap-diagonal-argument-Cantor : X → X
  endomap-diagonal-argument-Cantor x = rec-coproduct (λ _ → w) (λ _ → m) (H x)

  compute-left-endomap-diagonal-argument-Cantor :
    (x : X) → m ＝ x → endomap-diagonal-argument-Cantor x ＝ w
  compute-left-endomap-diagonal-argument-Cantor x p =
    ap
      ( rec-coproduct (λ _ → w) (λ _ → m))
      ( eq-is-prop'
        ( is-property-is-inhabited-or-empty (m ＝ x))
        ( H x)
        ( inl (unit-trunc-Prop p)))

  compute-right-endomap-diagonal-argument-Cantor :
    (x : X) → m ≠ x → m ＝ endomap-diagonal-argument-Cantor x
  compute-right-endomap-diagonal-argument-Cantor x np =
    ap
      ( rec-coproduct (λ _ → w) (λ _ → m))
      ( eq-is-prop'
        ( is-property-is-inhabited-or-empty (m ＝ x))
        ( inr np)
        ( H x))

  has-no-fixed-points-endomap-diagonal-argument-Cantor :
    (x : X) → endomap-diagonal-argument-Cantor x ≠ x
  has-no-fixed-points-endomap-diagonal-argument-Cantor x =
    rec-coproduct
      ( λ |q| p →
        rec-trunc-Prop empty-Prop
          ( λ q →
            d (q ∙ inv p ∙ compute-left-endomap-diagonal-argument-Cantor x q))
          ( |q|))
      ( λ nmx p →
        nmx (compute-right-endomap-diagonal-argument-Cantor x nmx ∙ p))
      ( H x)
```

## Theorem

There cannot exist a [surjection](foundation.surjective-maps.md) `N ↠ (N → X)`.

**Proof.** If there did, then using our endofunction with no fixed points we may
produce a new element of `N → X` _by diagonalization_ that our surjection
couldn't possibly have hit, leading to a contradiction.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {N : UU l2} {m w : X}
  (H : (x : X) → is-inhabited-or-empty (m ＝ x)) (d : m ≠ w)
  where

  map-diagonal-argument-Cantor : (N → (N → X)) → N → X
  map-diagonal-argument-Cantor E ν =
    endomap-diagonal-argument-Cantor H d (E ν ν)

  not-in-image-map-diagonal-argument-Cantor :
    (E : N → (N → X)) → ¬ (fiber E (map-diagonal-argument-Cantor E))
  not-in-image-map-diagonal-argument-Cantor E (ν , α) =
    has-no-fixed-points-endomap-diagonal-argument-Cantor H d
      ( E ν ν)
      ( htpy-eq (inv α) ν)

  abstract
    diagonal-argument-Cantor :
      {E : N → (N → X)} → ¬ (is-surjective E)
    diagonal-argument-Cantor {E} is-surjective-E =
      rec-trunc-Prop empty-Prop
        ( not-in-image-map-diagonal-argument-Cantor E)
        ( is-surjective-E (map-diagonal-argument-Cantor E))

module _
  {l1 : Level} (X : Discrete-Type l1) (m w : type-Discrete-Type X) (d : m ≠ w)
  where

  abstract
    diagonal-argument-discrete-type-Cantor :
      {l2 : Level} {N : UU l2} {E : N → (N → type-Discrete-Type X)} →
      ¬ (is-surjective E)
    diagonal-argument-discrete-type-Cantor =
      diagonal-argument-Cantor
        ( λ x →
          is-inhabited-or-empty-is-decidable
            (has-decidable-equality-type-Discrete-Type X m x))
        ( d)
```

Consequently, `ℕ → X` is uncountable.

```agda
module _
  {l1 : Level} (X : Set l1) {m w : type-Set X}
  (H : (x : type-Set X) → is-inhabited-or-empty (m ＝ x)) (d : m ≠ w)
  where

  abstract
    is-uncountable-sequence-diagonal-argument-Cantor :
      is-uncountable (function-Set ℕ X)
    is-uncountable-sequence-diagonal-argument-Cantor P =
      apply-universal-property-trunc-Prop
        ( is-directly-countable-is-countable (function-Set ℕ X) (λ _ → m) P)
        ( empty-Prop)
        ( λ P' → diagonal-argument-Cantor H d (pr2 P'))

module _
  {l1 : Level} (X : Discrete-Type l1) (m w : type-Discrete-Type X) (d : m ≠ w)
  where

  is-uncountable-sequence-discrete-type-diagonal-argument-Cantor :
    is-uncountable (function-Set ℕ (set-Discrete-Type X))
  is-uncountable-sequence-discrete-type-diagonal-argument-Cantor =
    is-uncountable-sequence-diagonal-argument-Cantor
      ( set-Discrete-Type X)
      ( λ x →
        is-inhabited-or-empty-is-decidable
          ( has-decidable-equality-type-Discrete-Type X m x))
      ( d)
```

## References

{{#bibliography}} {{#reference Cantor1890/91}}

## See also

- Cantor's diagonal argument is generalized by
  [Lawvere's fixed point theorem](foundation.lawveres-fixed-point-theorem.md).

## External links

- [Cantor's diagonal argument](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
  at Wikipedia
