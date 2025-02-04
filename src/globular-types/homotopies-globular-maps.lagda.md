# Homotopies of maps between globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.homotopies-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-pairs-of-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import globular-types.globular-equivalences
open import globular-types.globular-maps
open import globular-types.globular-types
```

</details>

## Idea

A
{{#concept "homotopy" Disambiguation="of globular maps of globular types" Agda=htpy-globular-map}}
`f ~ g` is a homotopy `H₀ : f₀ ~ g₀` together with a family of equivalences

```text
                  A₁ x y
                  /    \
                 /      \
                /        \
               ∨          ∨
  B₁ (f₀ x) (f₀ y) ---> B₁ (g₀ x) (g₀ y)
               tr-htpy B H
```

## Definitions

### Homotopies of maps between globular types

```agda
tr-pair-globular-map :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  (C : A → B → Globular-Type l3 l4) →
  {x y : A} (p : x ＝ y) {x' : B} {y' : B} (q : x' ＝ y') →
  globular-map (C x x') (C y y')
tr-pair-globular-map C {x} refl {x'} refl = id-globular-map (C x x')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  (C : A → B → Globular-Type l3 l4)
  where

  compute-0-cell-tr-pair-globular-map :
    {x y : A} (p : x ＝ y) {x' : B} {y' : B} (q : x' ＝ y') →
    tr-pair' (λ u v → 0-cell-Globular-Type (C u v)) p q ~
    0-cell-globular-map (tr-pair-globular-map C p q)
  compute-0-cell-tr-pair-globular-map refl refl = refl-htpy

record
  htpy-globular-map
    {l1 l2 l3 l4 : Level} {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
    (f g : globular-map A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    0-cell-htpy-globular-map :
      0-cell-globular-map f ~ 0-cell-globular-map g

    1-cell-htpy-globular-map-htpy-globular-map :
      {x y : 0-cell-Globular-Type A} →
      htpy-globular-map
        ( comp-globular-map
          ( tr-pair-globular-map
            ( 1-cell-globular-type-Globular-Type B)
            ( 0-cell-htpy-globular-map x)
            ( 0-cell-htpy-globular-map y))
          ( 1-cell-globular-map-globular-map f {x} {y}))
        ( 1-cell-globular-map-globular-map g {x} {y})

open htpy-globular-map public

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (f g : globular-map A B)
  where

  1-cell-htpy-globular-map :
    (H : htpy-globular-map f g) →
    {x y : 0-cell-Globular-Type A} →
    tr-pair'
      ( 1-cell-Globular-Type B)
      ( 0-cell-htpy-globular-map H x)
      ( 0-cell-htpy-globular-map H y) ∘
    1-cell-globular-map f {x} {y} ~
    1-cell-globular-map g {x} {y}
  1-cell-htpy-globular-map H {x} {y} =
    ( ( compute-0-cell-tr-pair-globular-map
        ( 1-cell-globular-type-Globular-Type B)
        ( 0-cell-htpy-globular-map H x)
        ( 0-cell-htpy-globular-map H y)) ·r
      ( 0-cell-globular-map (1-cell-globular-map-globular-map f))) ∙h
    ( 0-cell-htpy-globular-map (1-cell-htpy-globular-map-htpy-globular-map H))
```

### The concatenation of homotopies of globular maps

```agda
-- concat-htpy-globular-map :
--   {l1 l2 l3 l4 : Level}
--   {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
--   {f g h : globular-map A B} →
--   htpy-globular-map f g →
--   htpy-globular-map g h →
--   htpy-globular-map f h
-- 0-cell-htpy-globular-map (concat-htpy-globular-map H K) =
--   0-cell-htpy-globular-map H ∙h
--   0-cell-htpy-globular-map K
-- 1-cell-htpy-globular-map-htpy-globular-map (concat-htpy-globular-map H K) =
--   concat-htpy-globular-map
--     {!   !}
--     ( concat-htpy-globular-map
--       {!  1-cell-htpy-globular-map-htpy-globular-map H  !}
--       ( 1-cell-htpy-globular-map-htpy-globular-map K))
```

### The right unit law of globular map composition

```agda
-- left-unit-law-htpy-globular-map :
--   {l1 l2 l3 l4 : Level}
--   {A : Globular-Type l1 l2} {B : Globular-Type l3 l4} (f : globular-map A B) →
--   htpy-globular-map (comp-globular-map (id-globular-map B) f) f
-- 0-cell-htpy-globular-map (left-unit-law-htpy-globular-map f) = refl-htpy
-- 1-cell-htpy-globular-map-htpy-globular-map (left-unit-law-htpy-globular-map f) =
--   concat-htpy-globular-map
--     {!   !}
--     ( left-unit-law-htpy-globular-map (1-cell-globular-map-globular-map f))
```

### The reflexivity homotopy on a globular map

```text
refl-htpy-globular-map :
  {l1 l2 l3 l4 : Level} {A : Globular-Type l1 l2} {B : Globular-Type l3 l4} →
  (f : globular-map A B) → htpy-globular-map f f
0-cell-htpy-globular-map (refl-htpy-globular-map f) = refl-htpy
1-cell-htpy-globular-map-htpy-globular-map (refl-htpy-globular-map f) =
  left-unit-law-htpy-globular-map (1-cell-globular-map-globular-map f)
```

### Composition of maps of globular types

```text
comp-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  globular-map B C → globular-map A B → globular-map A C
comp-globular-map g f =
  λ where
  .0-cell-globular-map →
    0-cell-globular-map g ∘ 0-cell-globular-map f
  .1-cell-globular-map-globular-map →
    comp-globular-map
      ( 1-cell-globular-map-globular-map g)
      ( 1-cell-globular-map-globular-map f)
```
