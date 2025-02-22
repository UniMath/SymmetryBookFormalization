# Transposing inequalities in posets along order-preserving retractions

```agda
module order-theory.transposition-inequalities-along-order-preserving-retractions-posets where
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

Given a pair of posets `P` and `Q`, consider a map
`f : type-Poset P → type-Poset Q` and an
[order preserving map](order-theory.order-preserving-maps-posets.md)
`g : type-Poset Q → type-Poset P` in the converse direction, such that `g` is a
[retraction](foundation.retractions.md) of `f`. Then there is a family of
transposition maps

```text
f x ≤ y → x ≤ g y
```

indexed by `x : type-Poset P` and `y : type-Poset Q`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : type-Poset P → type-Poset Q)
  (g : hom-Poset Q P)
  where

  leq-transpose-is-retraction-hom-Poset :
    (map-hom-Poset Q P g ∘ f ~ id) → (x : type-Poset P) (y : type-Poset Q) →
    leq-Poset Q (f x) y → leq-Poset P x (map-hom-Poset Q P g y)
  leq-transpose-is-retraction-hom-Poset f-retraction-g x y fx≤y =
    tr
      ( λ z → leq-Poset P z (map-hom-Poset Q P g y))
      ( f-retraction-g x)
      ( preserves-order-hom-Poset Q P g (f x) y fx≤y)
```
