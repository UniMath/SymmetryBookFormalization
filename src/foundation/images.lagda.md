# The image of a map

```agda
module foundation.images where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.propositional-truncations
open import foundation.slice
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.1-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The
{{#concept "image" Disambiguation="of a map" WD="image" WDID=Q860623 Agda=im}}
of a map is a type that satisfies the
[universal property of the image](foundation.universal-property-image.md) of a
map.

## Definitions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  subtype-im : subtype (l1 ⊔ l2) X
  subtype-im x = trunc-Prop (fiber f x)

  is-in-im : X → UU (l1 ⊔ l2)
  is-in-im = is-in-subtype subtype-im

  im : UU (l1 ⊔ l2)
  im = type-subtype subtype-im

  inclusion-im : im → X
  inclusion-im = inclusion-subtype subtype-im

  map-unit-im : A → im
  pr1 (map-unit-im a) = f a
  pr2 (map-unit-im a) = unit-trunc-Prop (a , refl)

  triangle-unit-im : coherence-triangle-maps f inclusion-im map-unit-im
  triangle-unit-im a = refl

  unit-im : hom-slice f inclusion-im
  pr1 unit-im = map-unit-im
  pr2 unit-im = triangle-unit-im
```

## Properties

### We characterize the identity type of `im f`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X)
  where

  Eq-im : im f → im f → UU l1
  Eq-im x y = (pr1 x ＝ pr1 y)

  refl-Eq-im : (x : im f) → Eq-im x x
  refl-Eq-im x = refl

  Eq-eq-im : (x y : im f) → x ＝ y → Eq-im x y
  Eq-eq-im x .x refl = refl-Eq-im x

  abstract
    is-torsorial-Eq-im :
      (x : im f) → is-torsorial (Eq-im x)
    is-torsorial-Eq-im x =
      is-torsorial-Eq-subtype
        ( is-torsorial-Id (pr1 x))
        ( λ x → is-prop-type-trunc-Prop)
        ( pr1 x)
        ( refl)
        ( pr2 x)

  abstract
    is-equiv-Eq-eq-im : (x y : im f) → is-equiv (Eq-eq-im x y)
    is-equiv-Eq-eq-im x =
      fundamental-theorem-id
        ( is-torsorial-Eq-im x)
        ( Eq-eq-im x)

  equiv-Eq-eq-im : (x y : im f) → (x ＝ y) ≃ Eq-im x y
  pr1 (equiv-Eq-eq-im x y) = Eq-eq-im x y
  pr2 (equiv-Eq-eq-im x y) = is-equiv-Eq-eq-im x y

  eq-Eq-im : (x y : im f) → Eq-im x y → x ＝ y
  eq-Eq-im x y = map-inv-is-equiv (is-equiv-Eq-eq-im x y)
```

### The image inclusion is an embedding

```agda
abstract
  is-emb-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-emb (inclusion-im f)
  is-emb-inclusion-im f = is-emb-inclusion-subtype (trunc-Prop ∘ fiber f)

emb-im :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → im f ↪ X
pr1 (emb-im f) = inclusion-im f
pr2 (emb-im f) = is-emb-inclusion-im f
```

### The image inclusion is injective

```agda
abstract
  is-injective-inclusion-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-injective (inclusion-im f)
  is-injective-inclusion-im f = is-injective-is-emb (is-emb-inclusion-im f)
```

### The unit map of the image is surjective

```agda
abstract
  is-surjective-map-unit-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-surjective (map-unit-im f)
  is-surjective-map-unit-im f (y , z) =
    apply-universal-property-trunc-Prop z
      ( trunc-Prop (fiber (map-unit-im f) (y , z)))
      ( α)
    where
    α : fiber f y → type-trunc-Prop (fiber (map-unit-im f) (y , z))
    α (x , p) = unit-trunc-Prop (x , eq-type-subtype (trunc-Prop ∘ fiber f) p)
```

### The image of a map into a truncated type is truncated

```agda
abstract
  is-trunc-im :
    {l1 l2 : Level} (k : 𝕋) {X : UU l1} {A : UU l2} (f : A → X) →
    is-trunc (succ-𝕋 k) X → is-trunc (succ-𝕋 k) (im f)
  is-trunc-im k f = is-trunc-emb k (emb-im f)

im-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋) (X : Truncated-Type l1 (succ-𝕋 k)) {A : UU l2}
  (f : A → type-Truncated-Type X) → Truncated-Type (l1 ⊔ l2) (succ-𝕋 k)
pr1 (im-Truncated-Type k X f) = im f
pr2 (im-Truncated-Type k X f) = is-trunc-im k f (is-trunc-type-Truncated-Type X)
```

### The image of a map into a proposition is a proposition

```agda
abstract
  is-prop-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-prop X → is-prop (im f)
  is-prop-im = is-trunc-im neg-two-𝕋

im-Prop :
    {l1 l2 : Level} (X : Prop l1) {A : UU l2}
    (f : A → type-Prop X) → Prop (l1 ⊔ l2)
im-Prop X f = im-Truncated-Type neg-two-𝕋 X f
```

### The image of a map into a set is a set

```agda
abstract
  is-set-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-set X → is-set (im f)
  is-set-im = is-trunc-im neg-one-𝕋

im-Set :
  {l1 l2 : Level} (X : Set l1) {A : UU l2}
  (f : A → type-Set X) → Set (l1 ⊔ l2)
im-Set X f = im-Truncated-Type (neg-one-𝕋) X f
```

### The image of a map into a 1-type is a 1-type

```agda
abstract
  is-1-type-im :
    {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    is-1-type X → is-1-type (im f)
  is-1-type-im = is-trunc-im zero-𝕋

im-1-Type :
  {l1 l2 : Level} (X : 1-Type l1) {A : UU l2}
  (f : A → type-1-Type X) → 1-Type (l1 ⊔ l2)
im-1-Type X f = im-Truncated-Type zero-𝕋 X f
```

## External links

- [Image (mathematics)](<https://en.wikipedia.org/wiki/Image_(mathematics)>) at
  Wikipedia
