# Fiber inclusions of maps

```agda
module synthetic-homotopy-theory.fiber-inclusions-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.unit-type
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Given a map `g : B → C` and an element `z : C`, then a
{{#concept "fiber inclusion" Disambiguation="of types" Agda=fiber-inclusion-of-map}}
of `g` at `z` is a map `f : A → B` such that the following is a
[commuting](foundation-core.commuting-squares-of-maps.md)
[pullback square](foundation.pullbacks.md)

```text
       f
  A ------> B
  |         |
  |         | g
  ∨    z    ∨
  * ------> C.
```

The following conditions are equivalent:

1. The map `f` is the fiber inclusion of `g` at `z`.
2. `g ∘ f` is constant at `z` with homotopy `H` and the induced map
   `x ↦ (f x , H x) : A → fiber g z` is an equivalence.
3. For every `y : B` there is an equivalence `(fiber f y) ≃ (z ＝ g y)`.

## Definitions

### The condition of being a fiber inclusion

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  map-fiber-fiber-inclusion-of-map : A → fiber g z
  map-fiber-fiber-inclusion-of-map x = (f x , H x)

  triangle-map-fiber-fiber-inclusion-of-map :
    gap g (point z) (f , terminal-map A , H) ~
    gap g (point z) (cone-fiber g z) ∘ map-fiber-fiber-inclusion-of-map
  triangle-map-fiber-fiber-inclusion-of-map = refl-htpy

  is-fiber-inclusion-of-map' : UU (l1 ⊔ l2 ⊔ l3)
  is-fiber-inclusion-of-map' = is-equiv map-fiber-fiber-inclusion-of-map
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B)
  where

  is-fiber-inclusion-of-map : UU (l1 ⊔ l2 ⊔ l3)
  is-fiber-inclusion-of-map =
    Σ ((x : A) → g (f x) ＝ z) (is-fiber-inclusion-of-map' g z f)
```

### The universal property of fiber inclusions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  universal-property-fiber-inclusion-of-map : UUω
  universal-property-fiber-inclusion-of-map =
    universal-property-pullback g (point z) (f , terminal-map A , H)
```

### The pullback property of fiber inclusions

```agda
pullback-condition-fiber-inclusion-of-map :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) →
  ((x : A) → g (f x) ＝ z) → UU (l1 ⊔ l2 ⊔ l3)
pullback-condition-fiber-inclusion-of-map {A = A} g z f H =
  is-pullback g (point z) (f , terminal-map A , H)
```

### The fiber property of fiber inclusions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  map-Id-fiber-fiber-inclusion-of-map : (y : B) → fiber f y → z ＝ g y
  map-Id-fiber-fiber-inclusion-of-map y (x , p) = inv (H x) ∙ ap g p

  triangle-map-Id-fiber-fiber-inclusion-of-map :
    (y : B) →
    map-Id-fiber-fiber-inclusion-of-map y ~
    map-compute-fiber-point z (g y) ∘
    map-fiber-vertical-map-cone g (point z) (f , terminal-map A , H) y
  triangle-map-Id-fiber-fiber-inclusion-of-map y = refl-htpy

  fiber-condition-fiber-inclusion-of-map : UU (l1 ⊔ l2 ⊔ l3)
  fiber-condition-fiber-inclusion-of-map =
    is-fiberwise-equiv map-Id-fiber-fiber-inclusion-of-map
```

### The type of fiber inclusions of a map at a point

```agda
fiber-inclusion-of-map :
  (l1 : Level) {l2 l3 : Level} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) → UU (lsuc l1 ⊔ l2 ⊔ l3)
fiber-inclusion-of-map l1 {B = B} g z =
  Σ (UU l1) (λ A → Σ (A → B) (is-fiber-inclusion-of-map g z))

module _
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3}
  {g : B → C} {z : C} (F : fiber-inclusion-of-map l1 g z)
  where

  type-fiber-inclusion-of-map : UU l1
  type-fiber-inclusion-of-map = pr1 F

  inclusion-fiber-inclusion-of-map : type-fiber-inclusion-of-map → B
  inclusion-fiber-inclusion-of-map = pr1 (pr2 F)

  compute-point-fiber-inclusion-of-map :
    (x : type-fiber-inclusion-of-map) →
    g (inclusion-fiber-inclusion-of-map x) ＝ z
  compute-point-fiber-inclusion-of-map = pr1 (pr2 (pr2 F))

  cone-fiber-inclusion-of-map : cone g (point z) type-fiber-inclusion-of-map
  cone-fiber-inclusion-of-map =
    ( inclusion-fiber-inclusion-of-map ,
      terminal-map type-fiber-inclusion-of-map ,
      compute-point-fiber-inclusion-of-map)

  is-fiber-inclusion-fiber-inclusion-of-map :
    is-fiber-inclusion-of-map' g z
      ( inclusion-fiber-inclusion-of-map)
      ( compute-point-fiber-inclusion-of-map)
  is-fiber-inclusion-fiber-inclusion-of-map = pr2 (pr2 (pr2 F))
```

## Properties

### A map is a fiber inclusion if and only if it satifies the pullback condition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  pullback-condition-is-fiber-inclusion-of-map :
    is-fiber-inclusion-of-map' g z f H →
    pullback-condition-fiber-inclusion-of-map g z f H
  pullback-condition-is-fiber-inclusion-of-map K =
    is-equiv-left-map-triangle
      ( gap g (point z) (f , terminal-map A , H))
      ( gap g (point z) (cone-fiber g z))
      ( map-fiber-fiber-inclusion-of-map g z f H)
      ( triangle-map-fiber-fiber-inclusion-of-map g z f H)
      ( K)
      ( is-pullback-cone-fiber g z)

  is-fiber-inclusion-pullback-condition-fiber-inclusion-of-map :
    pullback-condition-fiber-inclusion-of-map g z f H →
    is-fiber-inclusion-of-map' g z f H
  is-fiber-inclusion-pullback-condition-fiber-inclusion-of-map =
    is-equiv-top-map-triangle
      ( gap g (point z) (f , terminal-map A , H))
      ( gap g (point z) (cone-fiber g z))
      ( map-fiber-fiber-inclusion-of-map g z f H)
      ( triangle-map-fiber-fiber-inclusion-of-map g z f H)
      ( is-pullback-cone-fiber g z)
```

### A map satisfies the pullback condition of fiber inclusions if and only if it satisfies the fiber condition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  pullback-condition-fiber-condition-fiber-inclusion-of-map :
    fiber-condition-fiber-inclusion-of-map g z f H →
    pullback-condition-fiber-inclusion-of-map g z f H
  pullback-condition-fiber-condition-fiber-inclusion-of-map K =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
      ( g)
      ( point z)
      ( f , terminal-map A , H)
      ( λ y →
        is-equiv-top-map-triangle
          ( map-Id-fiber-fiber-inclusion-of-map g z f H y)
          ( map-compute-fiber-point z (g y))
          ( map-fiber-vertical-map-cone g (point z) (f , terminal-map A , H) y)
          ( triangle-map-Id-fiber-fiber-inclusion-of-map g z f H y)
          ( is-equiv-map-compute-fiber-point z (g y))
          ( K y))

  fiber-condition-pullback-condition-fiber-inclusion-of-map :
    pullback-condition-fiber-inclusion-of-map g z f H →
    fiber-condition-fiber-inclusion-of-map g z f H
  fiber-condition-pullback-condition-fiber-inclusion-of-map K y =
    is-equiv-left-map-triangle
      ( map-Id-fiber-fiber-inclusion-of-map g z f H y)
      ( map-compute-fiber-point z (g y))
      ( map-fiber-vertical-map-cone g (point z) (f , terminal-map A , H) y)
      ( triangle-map-Id-fiber-fiber-inclusion-of-map g z f H y)
      ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
        ( g)
        ( point z)
        ( f , terminal-map A , H)
        ( K)
        ( y))
      ( is-equiv-map-compute-fiber-point z (g y))
```

### A map is a fiber inclusion if and only if it satisfies the fiber condition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (z : C) (f : A → B) (H : (x : A) → g (f x) ＝ z)
  where

  fiber-condition-is-fiber-inclusion-of-map :
    is-fiber-inclusion-of-map' g z f H →
    fiber-condition-fiber-inclusion-of-map g z f H
  fiber-condition-is-fiber-inclusion-of-map =
    fiber-condition-pullback-condition-fiber-inclusion-of-map g z f H ∘
    pullback-condition-is-fiber-inclusion-of-map g z f H

  is-fiber-inclusion-fiber-condition-fiber-inclusion-of-map :
    fiber-condition-fiber-inclusion-of-map g z f H →
    is-fiber-inclusion-of-map' g z f H
  is-fiber-inclusion-fiber-condition-fiber-inclusion-of-map =
    is-fiber-inclusion-pullback-condition-fiber-inclusion-of-map g z f H ∘
    pullback-condition-fiber-condition-fiber-inclusion-of-map g z f H
```

### Fiber inclusions satisfy the conditions of being fiber inclusions

```agda
module _
  {l1 l2 l3 : Level} {B : UU l2} {C : UU l3} {g : B → C} {z : C}
  (F : fiber-inclusion-of-map l1 g z)
  where

  pullback-condition-fiber-inclusion-of-map' :
    pullback-condition-fiber-inclusion-of-map g z
      ( inclusion-fiber-inclusion-of-map F)
      ( compute-point-fiber-inclusion-of-map F)
  pullback-condition-fiber-inclusion-of-map' =
    pullback-condition-is-fiber-inclusion-of-map g z
      ( inclusion-fiber-inclusion-of-map F)
      ( compute-point-fiber-inclusion-of-map F)
      ( is-fiber-inclusion-fiber-inclusion-of-map F)

  universal-property-fiber-inclusion-of-map' :
    universal-property-fiber-inclusion-of-map g z
      ( inclusion-fiber-inclusion-of-map F)
      ( compute-point-fiber-inclusion-of-map F)
  universal-property-fiber-inclusion-of-map' =
    universal-property-pullback-is-pullback g (point z)
      ( cone-fiber-inclusion-of-map F)
      ( pullback-condition-fiber-inclusion-of-map')

  fiber-condition-fiber-inclusion-of-map' :
    fiber-condition-fiber-inclusion-of-map g z
      ( inclusion-fiber-inclusion-of-map F)
      ( compute-point-fiber-inclusion-of-map F)
  fiber-condition-fiber-inclusion-of-map' =
    fiber-condition-is-fiber-inclusion-of-map g z
      ( inclusion-fiber-inclusion-of-map F)
      ( compute-point-fiber-inclusion-of-map F)
      ( is-fiber-inclusion-fiber-inclusion-of-map F)
```

### The standard fiber inclusions are fiber inclusions

```agda
module _
  {l1 l2 : Level} {B : UU l1} {C : UU l2} (g : B → C) (z : C)
  where

  is-fiber-inclusion-inclusion-fiber :
    is-fiber-inclusion-of-map' g z
      ( inclusion-fiber g {z})
      ( compute-value-inclusion-fiber g {z})
  is-fiber-inclusion-inclusion-fiber = is-equiv-id

  fiber-inclusion-of-map-inclusion-fiber :
    fiber-inclusion-of-map (l1 ⊔ l2) g z
  fiber-inclusion-of-map-inclusion-fiber =
    ( fiber g z ,
      inclusion-fiber g {z} ,
      compute-value-inclusion-fiber g {z} ,
      is-fiber-inclusion-inclusion-fiber)
```

### Loop spaces are fiber inclusions of the point inclusion

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  is-fiber-inclusion-terminal-map-type-Ω :
    is-fiber-inclusion-of-map'
      ( point-point-Pointed-Type A)
      ( point-Pointed-Type A)
      ( terminal-map (type-Ω A))
      ( id)
  is-fiber-inclusion-terminal-map-type-Ω =
    is-fiber-inclusion-pullback-condition-fiber-inclusion-of-map
      ( point-point-Pointed-Type A)
      ( point-Pointed-Type A)
      ( terminal-map (type-Ω A))
      ( id)
      ( is-pullback-type-Ω A)

  fiber-inclusion-of-map-terminal-map-type-Ω :
    fiber-inclusion-of-map l (point-point-Pointed-Type A) (point-Pointed-Type A)
  fiber-inclusion-of-map-terminal-map-type-Ω =
    ( type-Ω A ,
      terminal-map (type-Ω A) ,
      id ,
      is-fiber-inclusion-terminal-map-type-Ω)
```
