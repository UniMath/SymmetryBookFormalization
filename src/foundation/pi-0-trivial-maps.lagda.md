# π₀-trivial maps

```agda
module foundation.pi-0-trivial-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.retracts-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.iterating-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "π₀-trivial" Disambiguation="map of types" Agda=is-π₀-trivial-map'}}
if its [fibers](foundation-core.fibers-of-maps.md) are π₀-trivial types. I.e.,
that their [set of connected components](foundation.connected-components.md) is
a [proposition](foundation-core.propositions.md). Equivalently, a map is
π₀-trivial if the elements of its fibers are
[merely equal](foundation.mere-equality.md).

## Definitions

### π₀-trivial maps as maps whose fibers are types with mere equality

```agda
is-π₀-trivial-map' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-π₀-trivial-map' {B = B} f =
  (y : B) → all-elements-merely-equal (fiber f y)
```

## Properties

### Embeddings are π₀-trivial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-π₀-trivial-map'-is-prop-map : is-prop-map f → is-π₀-trivial-map' f
    is-π₀-trivial-map'-is-prop-map H b x y = mere-eq-eq (eq-is-prop (H b))

  abstract
    is-π₀-trivial-map'-is-emb : is-emb f → is-π₀-trivial-map' f
    is-π₀-trivial-map'-is-emb H =
      is-π₀-trivial-map'-is-prop-map (is-prop-map-is-emb H)

is-π₀-trivial-map'-id : {l : Level} {A : UU l} → is-π₀-trivial-map' (id {A = A})
is-π₀-trivial-map'-id = is-π₀-trivial-map'-is-emb is-emb-id
```

### Composition of π₀-trivial maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-π₀-trivial-map'-comp :
      is-π₀-trivial-map' g → is-π₀-trivial-map' f → is-π₀-trivial-map' (g ∘ f)
    is-π₀-trivial-map'-comp G F y =
      all-elements-merely-equal-equiv
        ( compute-fiber-comp g f y)
        ( all-elements-merely-equal-Σ (G y) (F ∘ pr1))

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  where

  is-π₀-trivial-map'-iterate :
    (n : ℕ) → is-π₀-trivial-map' (iterate n f)
  is-π₀-trivial-map'-iterate zero-ℕ = is-π₀-trivial-map'-id
  is-π₀-trivial-map'-iterate (succ-ℕ n) =
    is-π₀-trivial-map'-comp is-π₀-trivial-f (is-π₀-trivial-map'-iterate n)
```
