# Sequential limits

```agda
module foundation.sequential-limits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-towers
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.towers
open import foundation.universal-property-sequential-limits
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

Given a [tower of types](foundation.towers.md)

```text
               fₙ                     f₁      f₀
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀
```

we can form the **standard sequential limit** `limₙ Aₙ` satisfying
[the universal property of the sequential limit](foundation.universal-property-sequential-limits.md)
of `Aₙ` thus completing the diagram

```text
                           fₙ                     f₁      f₀
  limₙ Aₙ ---> ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

The standard sequential limit consists of "points at infinity", which can be
recorded as [sequences](foundation.dependent-sequences.md) of terms whose images
under `f` agree:

```text
  ⋯  ↦   xₙ₊₁  ↦   xₙ  ↦   ⋯  ↦   x₂  ↦   x₁  ↦   x₀
          ⫙        ⫙              ⫙       ⫙       ⫙
  ⋯ ---> Aₙ₊₁ ---> Aₙ ---> ⋯ ---> A₂ ---> A₁ ---> A₀.
```

## Definitions

### The standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  standard-sequential-limit : UU l
  standard-sequential-limit =
    Σ ( (n : ℕ) → type-tower A n)
      ( λ a → (n : ℕ) → a n ＝ map-tower A n (a (succ-ℕ n)))

module _
  {l : Level} (A : tower l)
  where

  sequence-standard-sequential-limit :
    standard-sequential-limit A → (n : ℕ) → type-tower A n
  sequence-standard-sequential-limit = pr1

  coherence-standard-sequential-limit :
    (x : standard-sequential-limit A) (n : ℕ) →
    sequence-standard-sequential-limit x n ＝
    map-tower A n (sequence-standard-sequential-limit x (succ-ℕ n))
  coherence-standard-sequential-limit = pr2
```

### The cone at the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  cone-standard-sequential-limit : cone-tower A (standard-sequential-limit A)
  pr1 cone-standard-sequential-limit n x =
    sequence-standard-sequential-limit A x n
  pr2 cone-standard-sequential-limit n x =
    coherence-standard-sequential-limit A x n
```

### The gap map into the standard sequential limit

The **gap map** of a [cone over a tower](foundation.cones-over-towers.md) is the
map from the domain of the cone into the standard sequential limit.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  gap-tower : cone-tower A X → X → standard-sequential-limit A
  pr1 (gap-tower c x) n = map-cone-tower A c n x
  pr2 (gap-tower c x) n = coherence-cone-tower A c n x
```

### The property of being a sequential limit

The [proposition](foundation-core.propositions.md) `is-sequential-limit` is the
assertion that the gap map is an [equivalence](foundation-core.equivalences.md).
Note that this proposition is [small](foundation-core.small-types.md), whereas
[the universal property](foundation.universal-property-sequential-limits.md) is
a large proposition.

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit : cone-tower A X → UU (l1 ⊔ l2)
  is-sequential-limit c = is-equiv (gap-tower A c)

  is-property-is-sequential-limit :
    (c : cone-tower A X) → is-prop (is-sequential-limit c)
  is-property-is-sequential-limit c = is-property-is-equiv (gap-tower A c)

  is-sequential-limit-Prop : (c : cone-tower A X) → Prop (l1 ⊔ l2)
  pr1 (is-sequential-limit-Prop c) = is-sequential-limit c
  pr2 (is-sequential-limit-Prop c) = is-property-is-sequential-limit c
```

## Properties

### Characterization of equality in the standard sequential limit

```agda
module _
  {l : Level} (A : tower l)
  where

  Eq-standard-sequential-limit : (s t : standard-sequential-limit A) → UU l
  Eq-standard-sequential-limit s t =
    Σ ( sequence-standard-sequential-limit A s ~
        sequence-standard-sequential-limit A t)
      ( λ H →
        coherence-square-homotopies
          ( H)
          ( coherence-standard-sequential-limit A s)
          ( coherence-standard-sequential-limit A t)
          ( λ n → ap (map-tower A n) (H (succ-ℕ n))))

  refl-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) → Eq-standard-sequential-limit s s
  pr1 (refl-Eq-standard-sequential-limit s) = refl-htpy
  pr2 (refl-Eq-standard-sequential-limit s) = right-unit-htpy

  Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    s ＝ t → Eq-standard-sequential-limit s t
  Eq-eq-standard-sequential-limit s .s refl =
    refl-Eq-standard-sequential-limit s

  is-torsorial-Eq-standard-sequential-limit :
    (s : standard-sequential-limit A) →
    is-torsorial (Eq-standard-sequential-limit s)
  is-torsorial-Eq-standard-sequential-limit s =
    is-torsorial-Eq-structure _
      ( is-torsorial-htpy (pr1 s))
      ( pr1 s , refl-htpy)
      ( is-torsorial-Eq-Π _ (λ n → is-torsorial-path (pr2 s n ∙ refl)))

  is-equiv-Eq-eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    is-equiv (Eq-eq-standard-sequential-limit s t)
  is-equiv-Eq-eq-standard-sequential-limit s =
    fundamental-theorem-id
      ( is-torsorial-Eq-standard-sequential-limit s)
      ( Eq-eq-standard-sequential-limit s)

  extensionality-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    (s ＝ t) ≃ Eq-standard-sequential-limit s t
  pr1 (extensionality-standard-sequential-limit s t) =
    Eq-eq-standard-sequential-limit s t
  pr2 (extensionality-standard-sequential-limit s t) =
    is-equiv-Eq-eq-standard-sequential-limit s t

  eq-Eq-standard-sequential-limit :
    (s t : standard-sequential-limit A) →
    Eq-standard-sequential-limit s t → s ＝ t
  eq-Eq-standard-sequential-limit s t =
    map-inv-equiv (extensionality-standard-sequential-limit s t)
```

### The standard sequential limit satisfies the universal property of a sequential limit

```agda
module _
  {l1 : Level} (A : tower l1)
  where

  cone-map-standard-sequential-limit :
    {l : Level} {Y : UU l} → (Y → standard-sequential-limit A) → cone-tower A Y
  cone-map-standard-sequential-limit {Y = Y} =
    cone-map-tower A {Y = Y} (cone-standard-sequential-limit A)

  is-retraction-gap-tower :
    {l : Level} {Y : UU l} →
    gap-tower A ∘ cone-map-standard-sequential-limit {Y = Y} ~ id
  is-retraction-gap-tower x = refl

  is-section-gap-tower :
    {l : Level} {Y : UU l} →
    cone-map-standard-sequential-limit {Y = Y} ∘ gap-tower A ~ id
  is-section-gap-tower x = refl

  universal-property-standard-sequential-limit :
    {l : Level} →
    universal-property-sequential-limit l A (cone-standard-sequential-limit A)
  pr1 (pr1 (universal-property-standard-sequential-limit X)) = gap-tower A
  pr2 (pr1 (universal-property-standard-sequential-limit X)) =
    is-section-gap-tower
  pr1 (pr2 (universal-property-standard-sequential-limit X)) = gap-tower A
  pr2 (pr2 (universal-property-standard-sequential-limit X)) =
    is-retraction-gap-tower
```

### A cone over a tower is equal to the value of `cone-map-tower` at its own gap map

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  htpy-cone-up-pullback-standard-sequential-limit :
    (c : cone-tower A X) →
    htpy-cone-tower A
      ( cone-map-tower A (cone-standard-sequential-limit A) (gap-tower A c))
      ( c)
  pr1 (htpy-cone-up-pullback-standard-sequential-limit c) n = refl-htpy
  pr2 (htpy-cone-up-pullback-standard-sequential-limit c) n = right-unit-htpy
```

### A cone satisfies the universal property of the limit if and only if the gap map is an equivalence

```agda
module _
  {l1 l2 : Level} (A : tower l1) {X : UU l2}
  where

  is-sequential-limit-universal-property-sequential-limit :
    (c : cone-tower A X) →
    ({l : Level} → universal-property-sequential-limit l A c) →
    is-sequential-limit A c
  is-sequential-limit-universal-property-sequential-limit c =
    is-equiv-universal-property-sequential-limit-universal-property-sequential-limit
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-tower A c)
      ( htpy-cone-up-pullback-standard-sequential-limit A c)
      ( universal-property-standard-sequential-limit A)

  universal-property-is-sequential-limit :
    (c : cone-tower A X) → is-sequential-limit A c →
    {l : Level} → universal-property-sequential-limit l A c
  universal-property-is-sequential-limit c is-lim-c =
    universal-property-sequential-limit-universal-property-sequential-limit-is-equiv
      ( cone-standard-sequential-limit A)
      ( c)
      ( gap-tower A c)
      ( htpy-cone-up-pullback-standard-sequential-limit A c)
      ( is-lim-c)
      ( universal-property-standard-sequential-limit A)
```

## Table of files about sequential limits

The following table lists files that are about sequential limits as a general
concept.

{{#include tables/sequential-limits.md}}
