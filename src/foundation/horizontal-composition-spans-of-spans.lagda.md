# Horizontal composition of spans of spans

```agda
module foundation.horizontal-composition-spans-of-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.composition-spans
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.equivalences-spans
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.pullbacks
open import foundation.spans
open import foundation.spans-of-spans
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-standard-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
```

</details>

## Idea

Given two [spans](foundation.spans.md) `F` and `G` from `A` to `B` and two spans
`H` and `I` from `B` to `C` together with
[higher spans](foundation.spans-of-spans.md) `α` from `F` to `G` and `β` from
`H` to `I`, i.e., we have a commuting diagram of types of the form

```text
      F₀      H₀
    ↙ ↑ ↘   ↙ ↑ ↘
  A   α₀  B   β₀  C,
    ↖ ↓ ↗   ↖ ↓ ↗
      G₀      I₀
```

then we may
{{#concept "horizontally compose" Disambiguation="spans of spans" Agda=horizontal-comp-span-of-spans}}
`α` and `β` to obtain a span of spans `α ∙ β` from `H ∘ F` to `I ∘ G`.
Explicitly, the horizontal composite is given by the unique construction of a
span of spans

```text
  F₀ ×_B H₀ ----------> C
      |    ↖            ∧
      |    α₀ ×_B β₀    |
      ∨            ↘    |
      A <---------- G₀ ×_B I₀
```

from the available data.

**Note.** There are four equivalent, but judgmentally different choices of
spanning type `α₀ ×_B β₀` of the horizontal composite. We pick the composites

```text
  α₀ ×_B β₀ ------> β₀
      | ⌟           ↓
      |             I₀
      ∨             ↓
      α₀ --> F₀ --> B
```

as this choice avoids inversions of coherences as part of the construction,
given our choice of orientation for coherences of spans of spans.

## Definitions

### Horizontal composition of spans of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (F : span l4 A B) (G : span l5 A B)
  (H : span l6 B C) (I : span l7 B C)
  (α : span-of-spans l8 F G)
  (β : span-of-spans l9 H I)
  where

  spanning-type-horizontal-comp-span-of-spans : UU (l2 ⊔ l8 ⊔ l9)
  spanning-type-horizontal-comp-span-of-spans =
    standard-pullback
      ( right-map-span F ∘ left-map-span-of-spans F G α)
      ( left-map-span I ∘ right-map-span-of-spans H I β)

  cone-left-map-horizontal-comp-span-of-spans :
    cone
      ( right-map-span F)
      ( left-map-span H)
      ( spanning-type-horizontal-comp-span-of-spans)
  cone-left-map-horizontal-comp-span-of-spans =
    left-map-span-of-spans F G α ∘ vertical-map-standard-pullback ,
    left-map-span-of-spans H I β ∘ horizontal-map-standard-pullback ,
    coherence-square-standard-pullback ∙h
    coh-left-span-of-spans H I β ·r horizontal-map-standard-pullback

  left-map-horizontal-comp-span-of-spans :
    spanning-type-horizontal-comp-span-of-spans → spanning-type-comp-span H F
  left-map-horizontal-comp-span-of-spans =
    gap
      ( right-map-span F)
      ( left-map-span H)
      ( cone-left-map-horizontal-comp-span-of-spans)

  cone-right-map-horizontal-comp-span-of-spans :
    cone
      ( right-map-span G)
      ( left-map-span I)
      ( spanning-type-horizontal-comp-span-of-spans)
  cone-right-map-horizontal-comp-span-of-spans =
    right-map-span-of-spans F G α ∘ vertical-map-standard-pullback ,
    right-map-span-of-spans H I β ∘ horizontal-map-standard-pullback ,
    coh-right-span-of-spans F G α ·r vertical-map-standard-pullback ∙h
    coherence-square-standard-pullback

  right-map-horizontal-comp-span-of-spans :
    spanning-type-horizontal-comp-span-of-spans → spanning-type-comp-span I G
  right-map-horizontal-comp-span-of-spans =
    gap
      ( right-map-span G)
      ( left-map-span I)
      ( cone-right-map-horizontal-comp-span-of-spans)

  span-horizontal-comp-span-of-spans :
    span
      ( l2 ⊔ l8 ⊔ l9)
      ( spanning-type-comp-span H F)
      ( spanning-type-comp-span I G)
  span-horizontal-comp-span-of-spans =
    spanning-type-horizontal-comp-span-of-spans ,
    left-map-horizontal-comp-span-of-spans ,
    right-map-horizontal-comp-span-of-spans

  coherence-left-horizontal-comp-span-of-spans :
    coherence-left-span-of-spans
      ( comp-span H F)
      ( comp-span I G)
      ( span-horizontal-comp-span-of-spans)
  coherence-left-horizontal-comp-span-of-spans =
    coh-left-span-of-spans F G α ·r vertical-map-standard-pullback

  coherence-right-horizontal-comp-span-of-spans :
    coherence-right-span-of-spans
      ( comp-span H F)
      ( comp-span I G)
      ( span-horizontal-comp-span-of-spans)
  coherence-right-horizontal-comp-span-of-spans =
    coh-right-span-of-spans H I β ·r horizontal-map-standard-pullback

  coherence-horizontal-comp-span-of-spans :
    coherence-span-of-spans
      ( comp-span H F)
      ( comp-span I G)
      ( span-horizontal-comp-span-of-spans)
  coherence-horizontal-comp-span-of-spans =
    coherence-left-horizontal-comp-span-of-spans ,
    coherence-right-horizontal-comp-span-of-spans

  horizontal-comp-span-of-spans :
    span-of-spans (l2 ⊔ l8 ⊔ l9) (comp-span H F) (comp-span I G)
  horizontal-comp-span-of-spans =
    span-horizontal-comp-span-of-spans ,
    coherence-horizontal-comp-span-of-spans
```
