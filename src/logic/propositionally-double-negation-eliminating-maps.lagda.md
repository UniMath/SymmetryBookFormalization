# Propositionally double negation eliminating maps

```agda
module logic.propositionally-double-negation-eliminating-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.propositional-double-negation-elimination
open import logic.propositionally-decidable-maps
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "propositionally double negation eliminating" Disambiguation="map of types" Agda=is-prop-double-negation-eliminating-map}}
if its [fibers](foundation-core.fibers-of-maps.md) satisfy
[propositional double negation elimination](logic.propositional-double-negation-elimination.md).
I.e., for every `y : B`, if `fiber f y` is
[irrefutable](foundation.irrefutable-propositions.md), then we do in fact have
then the fiber is in fact inhabited. In other words, double negation eliminating
maps come [equipped](foundation.structure.md) with a map

```text
  (y : B) → ¬¬ (fiber f y) → ║ fiber f y ║₋₁.
```

## Definintion

### Double negation elimination structure on a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-double-negation-eliminating-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-double-negation-eliminating-map f =
    (y : B) → has-prop-double-negation-elim (fiber f y)

  is-property-is-prop-double-negation-eliminating-map :
    {f : A → B} → is-prop (is-prop-double-negation-eliminating-map f)
  is-property-is-prop-double-negation-eliminating-map {f} =
    is-prop-Π (λ y → is-prop-has-prop-double-negation-elim (fiber f y))

  is-prop-double-negation-eliminating-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-prop-double-negation-eliminating-map-Prop f =
    is-prop-double-negation-eliminating-map f ,
    is-property-is-prop-double-negation-eliminating-map
```

### The type of propositionally double negation eliminating maps

```agda
prop-double-negation-eliminating-map :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prop-double-negation-eliminating-map A B =
  Σ (A → B) (is-prop-double-negation-eliminating-map)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : prop-double-negation-eliminating-map A B)
  where

  map-prop-double-negation-eliminating-map : A → B
  map-prop-double-negation-eliminating-map = pr1 f

  is-prop-double-negation-eliminating-prop-double-negation-eliminating-map :
    is-prop-double-negation-eliminating-map
      map-prop-double-negation-eliminating-map
  is-prop-double-negation-eliminating-prop-double-negation-eliminating-map =
    pr2 f
```

## Properties

### Double negation eliminating maps are closed under homotopy

```agda
abstract
  is-prop-double-negation-eliminating-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g →
    is-prop-double-negation-eliminating-map g →
    is-prop-double-negation-eliminating-map f
  is-prop-double-negation-eliminating-map-htpy H K b =
    has-prop-double-negation-elim-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Double negation eliminating maps are propositionally double negation eliminating

```agda
is-prop-double-negation-eliminating-map-is-double-negation-eliminating-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-double-negation-eliminating-map f →
  is-prop-double-negation-eliminating-map f
is-prop-double-negation-eliminating-map-is-double-negation-eliminating-map H y =
  has-prop-double-negation-elim-has-double-negation-elim (H y)
```

### Propositionally decidable maps are propositionally double negation eliminating

```agda
is-prop-double-negation-eliminating-map-is-inhabited-or-empty-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-inhabited-or-empty-map f → is-prop-double-negation-eliminating-map f
is-prop-double-negation-eliminating-map-is-inhabited-or-empty-map H y =
  prop-double-negation-elim-is-inhabited-or-empty (H y)
```
