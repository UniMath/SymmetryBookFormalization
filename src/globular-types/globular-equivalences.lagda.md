# Equivalences between globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
```

</details>

## Idea

A {{#concept "globular equivalence" Agda=globular-equiv}} `e` between
[globular types](globular-types.globular-types.md) `A` and `B` consists of an
[equivalence](foundation-core.equivalences.md) `e₀` of $0$-cells, and for every
pair of $n$-cells `x` and `y`, an equivalence of $(n+1)$-cells

```text
  eₙ₊₁ : Aₙ₊₁ x y ≃ Bₙ₊₁ (eₙ x) (eₙ y).
```

## Definitions

### The predicate on a globular map of being an equivalence

```agda
record
  is-equiv-globular-map
    {l1 l2 l3 l4 : Level}
    {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
    (f : globular-map A B) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive

  field
    is-equiv-0-cell-is-equiv-globular-map : is-equiv (0-cell-globular-map f)

    1-cell-is-equiv-globular-map :
      {x y : 0-cell-Globular-Type A} →
      is-equiv-globular-map (1-cell-globular-map-globular-map f {x} {y})

open is-equiv-globular-map public
```

### Equivalences between globular types

```agda
globular-equiv :
  {l1 l2 l3 l4 : Level} → Globular-Type l1 l2 → Globular-Type l3 l4 →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
globular-equiv A B = Σ (globular-map A B) (is-equiv-globular-map)

module _
  {l1 l2 l3 l4 : Level} {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  globular-map-globular-equiv : globular-map A B
  globular-map-globular-equiv = pr1 e

  is-equiv-globular-equiv : is-equiv-globular-map globular-map-globular-equiv
  is-equiv-globular-equiv = pr2 e

  0-cell-map-globular-equiv : 0-cell-Globular-Type A → 0-cell-Globular-Type B
  0-cell-map-globular-equiv =
    0-cell-globular-map globular-map-globular-equiv

  is-equiv-0-cell-map-globular-equiv : is-equiv 0-cell-map-globular-equiv
  is-equiv-0-cell-map-globular-equiv =
    is-equiv-0-cell-is-equiv-globular-map is-equiv-globular-equiv

  0-cell-globular-equiv : 0-cell-Globular-Type A ≃ 0-cell-Globular-Type B
  0-cell-globular-equiv =
    0-cell-map-globular-equiv , is-equiv-0-cell-map-globular-equiv

  1-cell-globular-map-globular-equiv :
    (x y : 0-cell-Globular-Type A) →
    globular-map
      ( 1-cell-globular-type-Globular-Type A x y)
      ( 1-cell-globular-type-Globular-Type B
        ( 0-cell-map-globular-equiv x)
        ( 0-cell-map-globular-equiv y))
  1-cell-globular-map-globular-equiv x y =
    1-cell-globular-map-globular-map globular-map-globular-equiv

  is-equiv-1-cell-globular-map-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    is-equiv-globular-map (1-cell-globular-map-globular-equiv x y)
  is-equiv-1-cell-globular-map-globular-equiv =
    1-cell-is-equiv-globular-map is-equiv-globular-equiv

  1-cell-globular-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    globular-equiv
      ( 1-cell-globular-type-Globular-Type A x y)
      ( 1-cell-globular-type-Globular-Type B
        ( 0-cell-map-globular-equiv x)
        ( 0-cell-map-globular-equiv y))
  1-cell-globular-equiv-globular-equiv {x} {y} =
    1-cell-globular-map-globular-equiv x y ,
    is-equiv-1-cell-globular-map-globular-equiv

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  1-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y ≃
    1-cell-Globular-Type B
      ( 0-cell-map-globular-equiv e x)
      ( 0-cell-map-globular-equiv e y)
  1-cell-equiv-globular-equiv =
    0-cell-globular-equiv (1-cell-globular-equiv-globular-equiv e)

  1-cell-map-globular-equiv :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y →
    1-cell-Globular-Type B
      ( 0-cell-map-globular-equiv e x)
      ( 0-cell-map-globular-equiv e y)
  1-cell-map-globular-equiv =
    0-cell-map-globular-equiv (1-cell-globular-equiv-globular-equiv e)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  2-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g ≃
    2-cell-Globular-Type B
      ( 1-cell-map-globular-equiv e f)
      ( 1-cell-map-globular-equiv e g)
  2-cell-equiv-globular-equiv =
    1-cell-equiv-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv e)

  2-cell-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g →
    2-cell-Globular-Type B
      ( 1-cell-map-globular-equiv e f)
      ( 1-cell-map-globular-equiv e g)
  2-cell-globular-equiv =
    1-cell-map-globular-equiv (1-cell-globular-equiv-globular-equiv e)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (e : globular-equiv A B)
  where

  3-cell-equiv-globular-equiv :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    {H K : 2-cell-Globular-Type A f g} →
    3-cell-Globular-Type A H K ≃
    3-cell-Globular-Type B
      ( 2-cell-globular-equiv e H)
      ( 2-cell-globular-equiv e K)
  3-cell-equiv-globular-equiv =
    2-cell-equiv-globular-equiv
      ( 1-cell-globular-equiv-globular-equiv e)
```

### The identity equivalence on a globular type

```agda
is-equiv-id-globular-map :
  {l1 l2 : Level} (A : Globular-Type l1 l2) →
  is-equiv-globular-map (id-globular-map A)
is-equiv-0-cell-is-equiv-globular-map (is-equiv-id-globular-map A) = is-equiv-id
1-cell-is-equiv-globular-map (is-equiv-id-globular-map A) =
  is-equiv-id-globular-map (1-cell-globular-type-Globular-Type A _ _)

id-globular-equiv :
  {l1 l2 : Level} (A : Globular-Type l1 l2) → globular-equiv A A
id-globular-equiv A = id-globular-map A , is-equiv-id-globular-map A
```

### Composition of equivalences of globular types

```agda
is-equiv-comp-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6}
  {g : globular-map B C}
  {f : globular-map A B} →
  is-equiv-globular-map g →
  is-equiv-globular-map f →
  is-equiv-globular-map (comp-globular-map g f)
is-equiv-0-cell-is-equiv-globular-map (is-equiv-comp-globular-map G F) =
  is-equiv-comp _ _
    ( is-equiv-0-cell-is-equiv-globular-map F)
    ( is-equiv-0-cell-is-equiv-globular-map G)
1-cell-is-equiv-globular-map (is-equiv-comp-globular-map G F) =
  is-equiv-comp-globular-map
    ( 1-cell-is-equiv-globular-map G)
    ( 1-cell-is-equiv-globular-map F)

comp-globular-equiv :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  globular-equiv B C → globular-equiv A B → globular-equiv A C
comp-globular-equiv g f =
  comp-globular-map
    ( globular-map-globular-equiv g)
    ( globular-map-globular-equiv f) ,
  is-equiv-comp-globular-map
    ( is-equiv-globular-equiv g)
    ( is-equiv-globular-equiv f)
```
