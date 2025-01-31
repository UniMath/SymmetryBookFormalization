# Contractible maps

```agda
module foundation-core.contractible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map is often said to satisfy a property `P` if each of its fibers satisfy
property `P`. Thus, we define contractible maps to be maps of which each fiber
is contractible. In other words, contractible maps are maps `f : A → B` such
that for each element `b : B` there is a unique `a : A` equipped with an
identification `(f a) ＝ b`, i.e., contractible maps are the type theoretic
bijections.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-map : (A → B) → UU (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fiber f y)
```

## Properties

### Any contractible map is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-contr-map f)
  where

  map-inv-is-contr-map : B → A
  map-inv-is-contr-map y = pr1 (center (H y))

  is-section-map-inv-is-contr-map :
    is-section f map-inv-is-contr-map
  is-section-map-inv-is-contr-map y = pr2 (center (H y))

  is-retraction-map-inv-is-contr-map :
    is-retraction f map-inv-is-contr-map
  is-retraction-map-inv-is-contr-map x =
    ap
      ( pr1 {B = λ z → (f z ＝ f x)})
      ( ( inv
          ( contraction
            ( H (f x))
            ( ( map-inv-is-contr-map (f x)) ,
              ( is-section-map-inv-is-contr-map (f x))))) ∙
        ( contraction (H (f x)) (x , refl)))

  section-is-contr-map : section f
  section-is-contr-map =
    ( map-inv-is-contr-map , is-section-map-inv-is-contr-map)

  retraction-is-contr-map : retraction f
  retraction-is-contr-map =
    ( map-inv-is-contr-map , is-retraction-map-inv-is-contr-map)

  abstract
    is-equiv-is-contr-map : is-equiv f
    is-equiv-is-contr-map =
      is-equiv-is-invertible
        ( map-inv-is-contr-map)
        ( is-section-map-inv-is-contr-map)
        ( is-retraction-map-inv-is-contr-map)
```

### Any coherently invertible map is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    center-fiber-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fiber f y
    pr1 (center-fiber-is-coherently-invertible H y) =
      map-inv-is-coherently-invertible H y
    pr2 (center-fiber-is-coherently-invertible H y) =
      is-section-map-inv-is-coherently-invertible H y

    contraction-fiber-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fiber f y) →
      (center-fiber-is-coherently-invertible H y) ＝ t
    contraction-fiber-is-coherently-invertible H y (x , refl) =
      eq-Eq-fiber f y
        ( is-retraction-map-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible :
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fiber-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fiber-is-coherently-invertible H y
```

### Any equivalence is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv =
      is-contr-map-is-coherently-invertible ∘ is-coherently-invertible-is-equiv
```

### The identity function is contractible

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-contr-map-id : is-contr-map (id {A = A})
    is-contr-map-id = is-torsorial-Id'
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
