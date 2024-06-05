# Descent data for type families of function types over pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.descent-data-function-types-over-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.postcomposition-functions
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Given two
[families with descent data](synthetic-homotopy-theory.families-descent-data-pushouts.md)
for [pushouts](synthetic-homotopy-theory.pushouts.md) `P ≈ (PA, PB, PS)` and
`R ≈ (RA, RB, RS)`, we show that
[fiberwise maps](foundation.families-of-maps.md) `(x : X) → P x → R x`
correspond to
[morphisms](synthetic-homotopy-theory.morphisms-descent-data-pushouts.md)
`(PA, PB, PS) → (RA, RB, RS)`.

**Proof:** We first characterize the type family `x ↦ (P x → R x)`. The
corresponding [descent data](synthetic-homotopy-theory.descent-data-pushouts.md)
consists of the type families

```text
  a ↦ (PA a → RA a)
  b ↦ (PB b → RB b),
```

and the gluing data sending `h : PA (fs) → RA (fs)` to
`(RS s ∘ h ∘ (PS s)⁻¹) : PB (gs) → RB (gs)`.

The fiberwise families then correspond to
[sections](synthetic-homotopy-theory.sections-descent-data-pushouts.md) of this
descent data, and it suffices to show that those correspond to morphisms. The
coherence datum of such a section has the type

```text
  (s : S) → RS s ∘ sA (fs) ∘ (RS s)⁻¹ = sB (gs),
```

which we can massage into a coherence of the morphism as

```text
  RS s ∘ sA (fs) ∘ (PS s)⁻¹ = sB (gs)
  ≃ RS s ∘ sA (fs) ∘ (PS s)⁻¹ ~ sB (gs)  by function extensionality
  ≃ RS s ∘ sA (fs) ~ sB (gs) ∘ PS s      by transposition of (PS s)
  ≃ sB (gs) ∘ PS s ~ RS s ∘ sA (fs)      by symmetry of homotopies.
```

## Definitions

### The type family of fiberwise functions with corresponding descent data for pushouts

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  (R : family-with-descent-data-pushout c l6)
  where

  family-cocone-family-with-descent-data-pushout-function-family :
    X → UU (l5 ⊔ l6)
  family-cocone-family-with-descent-data-pushout-function-family x =
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout R x

  descent-data-pushout-function-family :
    descent-data-pushout 𝒮 (l5 ⊔ l6)
  pr1 descent-data-pushout-function-family a =
    left-family-family-with-descent-data-pushout P a →
    left-family-family-with-descent-data-pushout R a
  pr1 (pr2 descent-data-pushout-function-family) b =
    right-family-family-with-descent-data-pushout P b →
    right-family-family-with-descent-data-pushout R b
  pr2 (pr2 descent-data-pushout-function-family) s =
    ( equiv-postcomp _
      ( equiv-family-family-with-descent-data-pushout R s)) ∘e
    ( equiv-precomp
      ( inv-equiv (equiv-family-family-with-descent-data-pushout P s))
      ( _))

  left-equiv-equiv-descent-data-pushout-function-family :
    (a : domain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( horizontal-map-cocone _ _ c a) →
      family-cocone-family-with-descent-data-pushout R
        ( horizontal-map-cocone _ _ c a)) ≃
    ( left-family-family-with-descent-data-pushout P a →
      left-family-family-with-descent-data-pushout R a)
  left-equiv-equiv-descent-data-pushout-function-family a =
    ( equiv-postcomp _
      ( left-equiv-family-with-descent-data-pushout R a)) ∘e
    ( equiv-precomp
      ( inv-equiv (left-equiv-family-with-descent-data-pushout P a))
      ( _))

  right-equiv-equiv-descent-data-pushout-function-family :
    (b : codomain-span-diagram 𝒮) →
    ( family-cocone-family-with-descent-data-pushout P
        ( vertical-map-cocone _ _ c b) →
      family-cocone-family-with-descent-data-pushout R
        ( vertical-map-cocone _ _ c b)) ≃
    ( right-family-family-with-descent-data-pushout P b →
      right-family-family-with-descent-data-pushout R b)
  right-equiv-equiv-descent-data-pushout-function-family b =
    ( equiv-postcomp _
      ( right-equiv-family-with-descent-data-pushout R b)) ∘e
    ( equiv-precomp
      ( inv-equiv (right-equiv-family-with-descent-data-pushout P b))
      ( _))

  coherence-equiv-descent-data-pushout-function-family :
    (s : spanning-type-span-diagram 𝒮) →
    coherence-square-maps
      ( map-equiv
        ( left-equiv-equiv-descent-data-pushout-function-family
          ( left-map-span-diagram 𝒮 s)))
      ( tr
        ( family-cocone-family-with-descent-data-pushout-function-family)
        ( coherence-square-cocone _ _ c s))
      ( map-family-descent-data-pushout descent-data-pushout-function-family s)
      ( map-equiv
        ( right-equiv-equiv-descent-data-pushout-function-family
          ( right-map-span-diagram 𝒮 s)))
  coherence-equiv-descent-data-pushout-function-family s =
    ( ( map-equiv
        ( right-equiv-equiv-descent-data-pushout-function-family
          ( right-map-span-diagram 𝒮 s))) ·l
      ( tr-function-type
        ( family-cocone-family-with-descent-data-pushout P)
        ( family-cocone-family-with-descent-data-pushout R)
        ( coherence-square-cocone _ _ c s))) ∙h
    ( λ h →
      eq-htpy
        ( horizontal-concat-htpy
          ( coherence-family-with-descent-data-pushout R s ·r h)
          ( coherence-square-maps-inv-equiv
            ( equiv-tr
              ( family-cocone-family-with-descent-data-pushout P)
              ( coherence-square-cocone _ _ c s))
            ( left-equiv-family-with-descent-data-pushout P
              ( left-map-span-diagram 𝒮 s))
            ( right-equiv-family-with-descent-data-pushout P
              ( right-map-span-diagram 𝒮 s))
            ( equiv-family-family-with-descent-data-pushout P s)
            ( inv-htpy (coherence-family-with-descent-data-pushout P s)))))

  equiv-descent-data-pushout-function-family :
    equiv-descent-data-pushout
      ( descent-data-family-cocone-span-diagram c
        ( family-cocone-family-with-descent-data-pushout-function-family))
      ( descent-data-pushout-function-family)
  pr1 equiv-descent-data-pushout-function-family =
    left-equiv-equiv-descent-data-pushout-function-family
  pr1 (pr2 equiv-descent-data-pushout-function-family) =
    right-equiv-equiv-descent-data-pushout-function-family
  pr2 (pr2 equiv-descent-data-pushout-function-family) =
    coherence-equiv-descent-data-pushout-function-family

  family-with-descent-data-pushout-function-family :
    family-with-descent-data-pushout c (l5 ⊔ l6)
  pr1 family-with-descent-data-pushout-function-family =
    family-cocone-family-with-descent-data-pushout-function-family
  pr1 (pr2 family-with-descent-data-pushout-function-family) =
    descent-data-pushout-function-family
  pr2 (pr2 family-with-descent-data-pushout-function-family) =
    equiv-descent-data-pushout-function-family
```

## Properties

### Sections of descent data for families of functions correspond to morphisms of descent data

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (P : family-with-descent-data-pushout c l5)
  (R : family-with-descent-data-pushout c l6)
  where

  hom-section-descent-data-pushout-function-family :
    section-descent-data-pushout (descent-data-pushout-function-family P R) →
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  pr1 (hom-section-descent-data-pushout-function-family t) =
    left-map-section-descent-data-pushout
      ( descent-data-pushout-function-family P R)
      ( t)
  pr1 (pr2 (hom-section-descent-data-pushout-function-family t)) =
    right-map-section-descent-data-pushout
      ( descent-data-pushout-function-family P R)
      ( t)
  pr2 (pr2 (hom-section-descent-data-pushout-function-family t)) s =
    inv-htpy
      ( map-inv-equiv
        ( equiv-coherence-triangle-maps-inv-top'
          ( ( map-family-family-with-descent-data-pushout R s) ∘
            ( left-map-section-descent-data-pushout
              ( descent-data-pushout-function-family P R)
              ( t)
              ( left-map-span-diagram 𝒮 s)))
          ( right-map-section-descent-data-pushout
            ( descent-data-pushout-function-family P R)
            ( t)
            ( right-map-span-diagram 𝒮 s))
          ( equiv-family-family-with-descent-data-pushout P s))
        ( htpy-eq
          ( coherence-section-descent-data-pushout
            ( descent-data-pushout-function-family P R)
            ( t)
            ( s))))

  abstract
    is-equiv-hom-section-descent-data-pushout-function-family :
      is-equiv hom-section-descent-data-pushout-function-family
    is-equiv-hom-section-descent-data-pushout-function-family =
      is-equiv-tot-is-fiberwise-equiv
        ( λ tA →
          is-equiv-tot-is-fiberwise-equiv
            ( λ tB →
              is-equiv-map-Π-is-fiberwise-equiv
                ( λ s →
                  is-equiv-comp _ _
                    ( funext _ _)
                    ( is-equiv-comp _ _
                      ( is-equiv-map-inv-equiv
                        ( equiv-coherence-triangle-maps-inv-top'
                          ( ( map-family-family-with-descent-data-pushout R s) ∘
                            ( tA (left-map-span-diagram 𝒮 s)))
                          ( tB (right-map-span-diagram 𝒮 s))
                          ( equiv-family-family-with-descent-data-pushout P s)))
                      ( is-equiv-inv-htpy _ _)))))

  hom-descent-data-map-family-cocone-span-diagram :
    ( (x : X) →
      family-cocone-family-with-descent-data-pushout P x →
      family-cocone-family-with-descent-data-pushout R x) →
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R)
  hom-descent-data-map-family-cocone-span-diagram =
    ( hom-section-descent-data-pushout-function-family) ∘
    ( section-descent-data-section-family-cocone-span-diagram
      ( family-with-descent-data-pushout-function-family P R))

  abstract
    is-equiv-hom-descent-data-map-family-cocone-span-diagram :
      universal-property-pushout _ _ c →
      is-equiv hom-descent-data-map-family-cocone-span-diagram
    is-equiv-hom-descent-data-map-family-cocone-span-diagram up-c =
      is-equiv-comp _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagram _
          ( up-c))
        ( is-equiv-hom-section-descent-data-pushout-function-family)
```

As a corollary, given a morphism `(hA, hB, hS) : (PA, PB, PS) → (RA, RB, RS)`,
there is a unique family of maps `h : (x : X) → P x → R x` such that its induced
morphism is homotopic to `(hA, hB, hS)`. The homotopy provides us in particular
with the component-wise [homotopies](foundation-core.homotopies.md)

```text
                 hA a                               hB a
          PA a --------> RA a                PB b --------> RB b
            |              ∧                   |              ∧
  (eᴾA a)⁻¹ |              | eᴿA a   (eᴾB b)⁻¹ |              | eᴿB b
            |              |                   |              |
            ∨              |                   ∨              |
         P (ia) ------> R (ia)              P (jb) ------> R (jb)
                h (ia)                             h (jb)
```

which we can turn into the computation rules

```text
              eᴾA a                           eᴾB a
      P (ia) -------> PA a            P (jb) -------> PB b
         |              |                |              |
  h (ia) |              | hA a    h (jb) |              | hB b
         |              |                |              |
         ∨              ∨                ∨              ∨
      R (ia) -------> RA a            R (jb) -------> RB b
              eᴿA a                           eᴿB b
```

by inverting the inverted equivalences.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (P : family-with-descent-data-pushout c l5)
  (R : family-with-descent-data-pushout c l6)
  (m :
    hom-descent-data-pushout
      ( descent-data-family-with-descent-data-pushout P)
      ( descent-data-family-with-descent-data-pushout R))
  where

  abstract
    uniqueness-map-hom-descent-data-pushout :
      is-contr
        ( Σ ( (x : X) →
              family-cocone-family-with-descent-data-pushout P x →
              family-cocone-family-with-descent-data-pushout R x)
            ( λ h →
              htpy-hom-descent-data-pushout
                ( descent-data-family-with-descent-data-pushout P)
                ( descent-data-family-with-descent-data-pushout R)
                ( hom-descent-data-map-family-cocone-span-diagram P R h)
                ( m)))
    uniqueness-map-hom-descent-data-pushout =
      is-contr-equiv'
        ( fiber (hom-descent-data-map-family-cocone-span-diagram P R) m)
        ( equiv-tot
          ( λ h → extensionality-hom-descent-data-pushout _ _ _ m))
        ( is-contr-map-is-equiv
          ( is-equiv-hom-descent-data-map-family-cocone-span-diagram P R up-c)
          ( m))

  map-hom-descent-data-pushout :
    (x : X) →
    family-cocone-family-with-descent-data-pushout P x →
    family-cocone-family-with-descent-data-pushout R x
  map-hom-descent-data-pushout =
    pr1 (center uniqueness-map-hom-descent-data-pushout)

  compute-left-map-map-hom-descent-data-pushout :
    (a : domain-span-diagram 𝒮) →
    coherence-square-maps
      ( left-map-family-with-descent-data-pushout P a)
      ( map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
      ( left-map-hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout R)
        ( m)
        ( a))
      ( left-map-family-with-descent-data-pushout R a)
  compute-left-map-map-hom-descent-data-pushout a =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( left-map-family-with-descent-data-pushout R a ∘
          map-hom-descent-data-pushout (horizontal-map-cocone _ _ c a))
        ( left-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
          ( m)
          ( a))
        ( left-equiv-family-with-descent-data-pushout P a))
      ( pr1 (pr2 (center uniqueness-map-hom-descent-data-pushout)) a)

  compute-right-map-map-hom-descent-data-pushout :
    (b : codomain-span-diagram 𝒮) →
    coherence-square-maps
      ( right-map-family-with-descent-data-pushout P b)
      ( map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
      ( right-map-hom-descent-data-pushout
        ( descent-data-family-with-descent-data-pushout P)
        ( descent-data-family-with-descent-data-pushout R)
        ( m)
        ( b))
      ( right-map-family-with-descent-data-pushout R b)
  compute-right-map-map-hom-descent-data-pushout b =
    map-inv-equiv
      ( equiv-coherence-triangle-maps-inv-top'
        ( right-map-family-with-descent-data-pushout R b ∘
          map-hom-descent-data-pushout (vertical-map-cocone _ _ c b))
        ( right-map-hom-descent-data-pushout
          ( descent-data-family-with-descent-data-pushout P)
          ( descent-data-family-with-descent-data-pushout R)
          ( m)
          ( b))
        ( right-equiv-family-with-descent-data-pushout P b))
      ( pr1 (pr2 (pr2 (center uniqueness-map-hom-descent-data-pushout))) b)
```
