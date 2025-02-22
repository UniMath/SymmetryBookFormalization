# Transposing inequalities in posets along sections of order-preserving maps

```agda
module order-theory.transposition-inequalities-along-sections-of-order-preserving-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

Given a pair of posets `P` and `Q`, consider an
[order preserving map](order-theory.order-preserving-maps-posets.md)
`f : type-Poset P → type-Poset Q` and a map `g : type-Poset Q → type-Poset P` in
the converse direction, such that `g` is a [section](foundation.sections.md) of
`f`. Then there is a family of transposition maps

```text
x ≤ g y → f x ≤ y
```

indexed by `x : type-Poset P` and `y : type-Poset Q`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : hom-Poset P Q)
  (g : type-Poset Q → type-Poset P)
  where

  leq-transpose-is-section-hom-Poset :
    (map-hom-Poset P Q f ∘ g ~ id) → (x : type-Poset P) (y : type-Poset Q) →
    leq-Poset P x (g y) → leq-Poset Q (map-hom-Poset P Q f x) y
  leq-transpose-is-section-hom-Poset f-section-g x y x≤gy =
    tr
      ( leq-Poset Q (map-hom-Poset P Q f x))
      ( f-section-g y)
      ( preserves-order-hom-Poset P Q f x (g y) x≤gy)
```
