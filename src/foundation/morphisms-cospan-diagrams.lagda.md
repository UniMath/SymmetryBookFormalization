# Morphisms of cospan diagrams

```agda
module foundation.morphisms-cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A
{{#concept "morphism of cospan diagrams" Disambiguation="of types" Agda=hom-cospan-diagram}}
is a commuting diagram of the form

```text
  A -----> X <----- B
  |        |        |
  |        |        |
  ∨        ∨        ∨
  A' ----> X' <---- B'.
```

## Definitions

### Morphisms of cospan diagrams

```agda
hom-cospan-diagram :
  {l1 l2 l3 l1' l2' l3' : Level} →
  cospan-diagram l1 l2 l3 →
  cospan-diagram l1' l2' l3' →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l1' ⊔ l2' ⊔ l3')
hom-cospan-diagram (A , B , X , f , g) (A' , B' , X' , f' , g') =
  Σ ( A → A')
    ( λ hA →
      Σ ( B → B')
        ( λ hB →
          Σ ( X → X')
            ( λ hX → (f' ∘ hA ~ hX ∘ f) × (g' ∘ hB ~ hX ∘ g))))

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  (h : hom-cospan-diagram 𝒮 𝒯)
  where

  left-map-hom-cospan-diagram :
    left-type-cospan-diagram 𝒮 → left-type-cospan-diagram 𝒯
  left-map-hom-cospan-diagram = pr1 h

  right-map-hom-cospan-diagram :
    right-type-cospan-diagram 𝒮 → right-type-cospan-diagram 𝒯
  right-map-hom-cospan-diagram = pr1 (pr2 h)

  cospanning-map-hom-cospan-diagram :
    cospanning-type-cospan-diagram 𝒮 → cospanning-type-cospan-diagram 𝒯
  cospanning-map-hom-cospan-diagram = pr1 (pr2 (pr2 h))

  left-square-hom-cospan-diagram :
    left-map-cospan-diagram 𝒯 ∘ left-map-hom-cospan-diagram ~
    cospanning-map-hom-cospan-diagram ∘ left-map-cospan-diagram 𝒮
  left-square-hom-cospan-diagram = pr1 (pr2 (pr2 (pr2 h)))

  right-square-hom-cospan-diagram :
    right-map-cospan-diagram 𝒯 ∘ right-map-hom-cospan-diagram ~
    cospanning-map-hom-cospan-diagram ∘ right-map-cospan-diagram 𝒮
  right-square-hom-cospan-diagram = pr2 (pr2 (pr2 (pr2 h)))
```

### Identity morphisms of cospan diagrams

```agda
id-hom-cospan-diagram :
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3) → hom-cospan-diagram 𝒮 𝒮
id-hom-cospan-diagram 𝒮 = (id , id , id , refl-htpy , refl-htpy)
```

### Composition of morphisms of cospan diagrams

```agda
module _
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  (ℛ : cospan-diagram l1'' l2'' l3'')
  where

  comp-hom-cospan-diagram :
    hom-cospan-diagram 𝒯 ℛ →
    hom-cospan-diagram 𝒮 𝒯 →
    hom-cospan-diagram 𝒮 ℛ
  comp-hom-cospan-diagram (hA , hB , hX , H , K) (hA' , hB' , hX' , H' , K') =
    ( hA ∘ hA' , hB ∘ hB' , hX ∘ hX' ,
      H ·r hA' ∙h hX ·l H' , K ·r hB' ∙h hX ·l K')
```

### Rotating cospan diagrams of cospan diagrams

```agda
module _
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  (ℛ : cospan-diagram l1'' l2'' l3'')
  where

  codomain-hom-cospan-diagram-rotate :
    (h : hom-cospan-diagram 𝒯 𝒮) (h' : hom-cospan-diagram ℛ 𝒮) →
    cospan-diagram l3' l3'' l3
  codomain-hom-cospan-diagram-rotate h h' =
    ( cospanning-type-cospan-diagram 𝒯 ,
      cospanning-type-cospan-diagram ℛ ,
      cospanning-type-cospan-diagram 𝒮 ,
      cospanning-map-hom-cospan-diagram 𝒯 𝒮 h ,
      cospanning-map-hom-cospan-diagram ℛ 𝒮 h')

  hom-cospan-diagram-rotate :
    (h : hom-cospan-diagram 𝒯 𝒮) (h' : hom-cospan-diagram ℛ 𝒮) →
    hom-cospan-diagram
      ( left-type-cospan-diagram 𝒯 ,
        left-type-cospan-diagram ℛ ,
        left-type-cospan-diagram 𝒮 ,
        left-map-hom-cospan-diagram 𝒯 𝒮 h ,
        left-map-hom-cospan-diagram ℛ 𝒮 h')
      ( codomain-hom-cospan-diagram-rotate h h')
  hom-cospan-diagram-rotate
    ( hA , hB , hX , HA , HB)
    ( hA' , hB' , hX' , HA' , HB') =
    ( left-map-cospan-diagram 𝒯 ,
      left-map-cospan-diagram ℛ ,
      left-map-cospan-diagram 𝒮 ,
      inv-htpy HA ,
      inv-htpy HA')

  hom-cospan-diagram-rotate' :
    (h : hom-cospan-diagram 𝒯 𝒮) (h' : hom-cospan-diagram ℛ 𝒮) →
    hom-cospan-diagram
      ( right-type-cospan-diagram 𝒯 ,
        right-type-cospan-diagram ℛ ,
        right-type-cospan-diagram 𝒮 ,
        right-map-hom-cospan-diagram 𝒯 𝒮 h ,
        right-map-hom-cospan-diagram ℛ 𝒮 h')
      ( codomain-hom-cospan-diagram-rotate h h')
  hom-cospan-diagram-rotate'
    ( hA , hB , hX , HA , HB)
    ( hA' , hB' , hX' , HA' , HB') =
    ( right-map-cospan-diagram 𝒯 ,
      right-map-cospan-diagram ℛ ,
      right-map-cospan-diagram 𝒮 ,
      inv-htpy HB ,
      inv-htpy HB')
```
