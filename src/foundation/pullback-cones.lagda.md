# Pullback cones

```agda
module foundation.pullback-cones where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.multivariable-homotopies
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.pullbacks
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
open import foundation-core.universal-property-pullbacks
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

A [cone](foundation.cones-over-cospan-diagrams.md) `𝑐` over a
[cospan diagram](foundation.cospans.md) `A -f-> X <-g- B` with domain `C` is a
{{#concept "pullback cone" Disambiguation="of types"}} if its gap map

```text
  C → standard-pullback f g
```

is an [equivalence](foundation-core.equivalenes.md). This is known as the
[small predicate of being a pullback](foundation-core.pullbacks.md).

## Definitions

### Pullback cones

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X)
  where

  pullback-cone : (l4 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4)
  pullback-cone l4 =
    Σ (Σ (UU l4) (λ C → cone f g C)) (λ (C , c) → is-pullback f g c)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (c : pullback-cone f g l4)
  where

  domain-pullback-cone : UU l4
  domain-pullback-cone = pr1 (pr1 c)

  cone-pullback-cone : cone f g domain-pullback-cone
  cone-pullback-cone = pr2 (pr1 c)

  vertical-map-pullback-cone : domain-pullback-cone → A
  vertical-map-pullback-cone =
    vertical-map-cone f g cone-pullback-cone

  horizontal-map-pullback-cone : domain-pullback-cone → B
  horizontal-map-pullback-cone =
    horizontal-map-cone f g cone-pullback-cone

  coherence-square-pullback-cone :
    coherence-square-maps
      ( horizontal-map-pullback-cone)
      ( vertical-map-pullback-cone)
      ( g)
      ( f)
  coherence-square-pullback-cone =
    coherence-square-cone f g cone-pullback-cone

  is-pullback-pullback-cone : is-pullback f g cone-pullback-cone
  is-pullback-pullback-cone = pr2 c

  up-pullback-cone : universal-property-pullback f g cone-pullback-cone
  up-pullback-cone =
    universal-property-pullback-is-pullback f g
      ( cone-pullback-cone)
      ( is-pullback-pullback-cone)
```

### Horizontal pasting of pullback cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (i : X → Y) (j : Y → Z) (h : C → Z)
  where

  pasting-horizontal-pullback-cone :
    (c : pullback-cone j h l1) →
    pullback-cone i (vertical-map-pullback-cone j h c) l2 →
    pullback-cone (j ∘ i) h l2
  pasting-horizontal-pullback-cone ((A , a) , pb-A) ((B , b) , pb-B) =
    ( B , pasting-horizontal-cone i j h a b) ,
    ( is-pullback-rectangle-is-pullback-left-square i j h a b pb-A pb-B)
```

### Vertical pasting of pullback cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (f : C → Z) (g : Y → Z) (h : X → Y)
  where

  pasting-vertical-pullback-cone :
    (c : pullback-cone f g l1) →
    pullback-cone (horizontal-map-pullback-cone f g c) h l2 →
    pullback-cone f (g ∘ h) l2
  pasting-vertical-pullback-cone ((A , a) , pb-A) ((B , b) , pb-B) =
    ( B , pasting-vertical-cone f g h a b) ,
    ( is-pullback-rectangle-is-pullback-top-square f g h a b pb-A pb-B)
```

### The swapping function on pullback cones

```agda
swap-pullback-cone :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) → pullback-cone f g l4 → pullback-cone g f l4
swap-pullback-cone f g ((C , c) , pb-C) =
  ( ( C , swap-cone f g c) , is-pullback-swap-cone f g c pb-C)
```

### The identity pullback cone over the identity cospan diagram

```agda
id-pullback-cone :
  {l : Level} (A : UU l) → pullback-cone (id {A = A}) (id {A = A}) l
id-pullback-cone A = ((A , id-cone A) , is-pullback-id-cone A)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
