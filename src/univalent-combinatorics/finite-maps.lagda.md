# Finite maps

```agda
module univalent-combinatorics.finite-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-embeddings
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

A map $f : A \to B$ is said to be a {{#concept "finite map"}} if its [fibers](foundation-core.finite-types.md) are [finite](univalent-combinatorics.finite-types.md).

Finite maps are [decidable](elementary-number-theory.decidable-maps-natural-numbers.md).

## Definitions

### The predicate of being a finite map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-finite-prop-map : Prop (l1 ⊔ l2)
  is-finite-prop-map =
    Π-Prop B (λ y → is-finite-Prop (fiber f y))
  
  is-finite-map : UU (l1 ⊔ l2)
  is-finite-map = type-Prop is-finite-prop-map

  is-prop-is-finite-map : is-prop is-finite-map
  is-prop-is-finite-map = is-prop-type-Prop is-finite-prop-map
```

## Properties

### Decidable embeddings are finite maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-finite-map-is-decidable-emb :
    is-decidable-emb f → is-finite-map f
  is-finite-map-is-decidable-emb H x =
    is-finite-is-decidable-prop (is-decidable-prop-map-is-decidable-emb H x)
```
