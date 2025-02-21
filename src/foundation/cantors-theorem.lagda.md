# Cantor's theorem

```agda
module foundation.cantors-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-propositions
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.propositions

open import logic.de-morgan-propositions
open import logic.de-morgan-subtypes
open import logic.double-negation-dense-maps
open import logic.double-negation-stable-subtypes
```

</details>

## Idea

{{#concept "Cantor's theorem" Agda=theorem-Cantor WD="Cantor's theorem" WDID=Q474881}}
shows that there is [no](foundation-core.negation.md)
[surjective map](foundation.surjective-maps.md) from a type onto its
[powerset](foundation.powersets.md).

```text
  ¬ (A ↠ 𝒫(A))
```

## Theorem

**Proof.** The proof is an instance of an argument _by diagonalization_. Given a
function `f : A → 𝒫(A)` we may define an element of the powerset `𝒫(A)` that `f`
cannot possibly hit. This subtype is defined by

```text
  B := {x ∈ A | x ∉ f(x)}
```

which is given formally by the predicate `x ↦ ¬ (f x x)`. If this subtype were
to be hit by `f`, that would mean there is a `ξ ∈ A` such that `f(ξ) = B`. This
would have to be a fixed point of the negation operation, since

```text
  f(ξ)(ξ) = B(ξ) = ¬ (f(ξ)(ξ)),
```

but negation has no fixed points.

Cantor's theorem is the [63rd](literature.100-theorems.md#63) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
module _
  {l1 l2 : Level} {X : UU l1} (f : X → powerset l2 X)
  where

  subtype-theorem-Cantor : powerset l2 X
  subtype-theorem-Cantor x = neg-Prop (f x x)

  not-in-image-subtype-theorem-Cantor : ¬ (fiber f subtype-theorem-Cantor)
  not-in-image-subtype-theorem-Cantor (ξ , α) =
    no-fixed-points-neg-Prop (f ξ ξ) (iff-eq (htpy-eq α ξ))

  theorem-irrefutably-surjective-Cantor : ¬ (is-double-negation-dense-map f)
  theorem-irrefutably-surjective-Cantor H =
    H subtype-theorem-Cantor not-in-image-subtype-theorem-Cantor

  abstract
    theorem-Cantor : ¬ (is-surjective f)
    theorem-Cantor =
      map-neg
        is-double-negation-dense-map-is-surjective
        theorem-irrefutably-surjective-Cantor
```

### Cantor's theorem for the set of decidable subtypes

**Statement.** There is no surjective map from a type `X` to its set of
decidable subtypes `𝒫ᵈ(X)`.

```agda
module _
  {l1 l2 : Level} {X : UU l1} (f : X → decidable-subtype l2 X)
  where

  map-theorem-decidable-Cantor : decidable-subtype l2 X
  map-theorem-decidable-Cantor x = neg-Decidable-Prop (f x x)

  not-in-image-map-theorem-decidable-Cantor :
    ¬ (fiber f map-theorem-decidable-Cantor)
  not-in-image-map-theorem-decidable-Cantor (x , α) =
    no-fixed-points-neg-Decidable-Prop
      ( f x x)
      ( iff-eq (ap prop-Decidable-Prop (htpy-eq α x)))

  theorem-irrefutably-surjective-decidable-Cantor :
    ¬ (is-double-negation-dense-map f)
  theorem-irrefutably-surjective-decidable-Cantor H =
    H map-theorem-decidable-Cantor not-in-image-map-theorem-decidable-Cantor

  abstract
    theorem-decidable-Cantor : ¬ (is-surjective f)
    theorem-decidable-Cantor =
      map-neg
        is-double-negation-dense-map-is-surjective
        theorem-irrefutably-surjective-decidable-Cantor
```

### Cantor's theorem for the set of double negation stable subtypes

**Statement.** There is no surjective map from a type `X` to its set of double
negation stable subtypes `𝒫^¬¬(X)`.

```agda
module _
  {l1 l2 : Level} {X : UU l1} (f : X → double-negation-stable-subtype l2 X)
  where

  map-theorem-double-negation-stable-Cantor :
    double-negation-stable-subtype l2 X
  map-theorem-double-negation-stable-Cantor x =
    neg-Double-Negation-Stable-Prop (f x x)

  not-in-image-map-theorem-double-negation-stable-Cantor :
    ¬ (fiber f map-theorem-double-negation-stable-Cantor)
  not-in-image-map-theorem-double-negation-stable-Cantor (x , α) =
    no-fixed-points-neg-Double-Negation-Stable-Prop
      ( f x x)
      ( iff-eq (ap prop-Double-Negation-Stable-Prop (htpy-eq α x)))

  theorem-irrefutably-surjective-double-negation-stable-Cantor :
    ¬ (is-double-negation-dense-map f)
  theorem-irrefutably-surjective-double-negation-stable-Cantor H =
    H map-theorem-double-negation-stable-Cantor
      not-in-image-map-theorem-double-negation-stable-Cantor

  abstract
    theorem-double-negation-stable-Cantor : ¬ (is-surjective f)
    theorem-double-negation-stable-Cantor =
      map-neg
        is-double-negation-dense-map-is-surjective
        theorem-irrefutably-surjective-double-negation-stable-Cantor
```

### Cantor's theorem for the set of De Morgan subtypes

**Statement.** There is no surjective map from a type `X` to its set of De
Morgan subtypes `𝒫ᵈᵐ(X)`.

```agda
module _
  {l1 l2 : Level} {X : UU l1} (f : X → de-morgan-subtype l2 X)
  where

  map-theorem-de-morgan-Cantor : de-morgan-subtype l2 X
  map-theorem-de-morgan-Cantor x = neg-De-Morgan-Prop (f x x)

  not-in-image-map-theorem-de-morgan-Cantor :
    ¬ (fiber f map-theorem-de-morgan-Cantor)
  not-in-image-map-theorem-de-morgan-Cantor (x , α) =
    no-fixed-points-neg-De-Morgan-Prop
      ( f x x)
      ( iff-eq (ap prop-De-Morgan-Prop (htpy-eq α x)))

  theorem-irrefutably-surjective-de-morgan-Cantor :
    ¬ (is-double-negation-dense-map f)
  theorem-irrefutably-surjective-de-morgan-Cantor H =
    H map-theorem-de-morgan-Cantor not-in-image-map-theorem-de-morgan-Cantor

  abstract
    theorem-de-morgan-Cantor : ¬ (is-surjective f)
    theorem-de-morgan-Cantor =
      map-neg
        is-double-negation-dense-map-is-surjective
        theorem-irrefutably-surjective-de-morgan-Cantor
```

## References

A proof of Cantor's theorem first appeared in {{#cite Cantor1890/91}} where it
was considered in the context of [infinite sets](set-theory.infinite-sets.md).

{{#bibliography}} {{#reference Cantor1890/91}}

## See also

- Cantor's theorem generalizes
  [Cantor's diagonal argument](set-theory.cantors-diagonal-argument.md), which
  shows that the [set](foundation-core.sets.md) of
  [infinite sequences](foundation.sequences.md) on a set with at least two
  distinct elements is [uncountable](set-theory.uncountable-sets.md).
- Cantor's theorem is generalized by
  [Lawvere's fixed point theorem](foundation.lawveres-fixed-point-theorem.md).

## External links

- [Cantor's theorem](https://ncatlab.org/nlab/show/Cantor%27s+theorem) at $n$Lab
- [Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem) at
  Wikipedia
- [Cantor's theorem](https://www.britannica.com/science/Cantors-theorem) at
  Britannica
