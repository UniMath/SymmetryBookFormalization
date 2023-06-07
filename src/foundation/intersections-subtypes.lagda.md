# Intersection of subtypes

```agda
module foundation.intersections-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.decidable-subtypes
open import foundation.large-locale-of-subtypes
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

The intersection of two subtypes `A` and `B` is the subtype that contains the
elements that are in `A` and in `B`.

## Definition

### The intersection of two subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  intersection-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  intersection-subtype = meet-power-set-Large-Locale
```

### The intersection of two decidable subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  intersection-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  intersection-decidable-subtype P Q x = conj-Decidable-Prop (P x) (Q x)
```

### The intersection of a family of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  intersection-fam-subtype :
    {I : UU l2} (P : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  intersection-fam-subtype {I} P x = Π-Prop I (λ i → P i x)
```
