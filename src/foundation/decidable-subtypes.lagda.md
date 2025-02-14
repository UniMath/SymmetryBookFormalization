# Decidable subtypes

```agda
module foundation.decidable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.1-types
open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.postcomposition-functions
open import foundation.propositional-maps
open import foundation.sets
open import foundation.structured-type-duality
open import foundation.subtypes
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import logic.double-negation-stable-subtypes
```

</details>

## Idea

A
{{#concept "decidable subtype" Disambiguation="of a type" Agda=is-decidable-subtype Agda=decidable-subtype}}
of a type consists of a family of
[decidable propositions](foundation-core.decidable-propositions.md) over it.

## Definitions

### Decidable subtypes

```agda
is-decidable-subtype-Prop :
  {l1 l2 : Level} {A : UU l1} → subtype l2 A → Prop (l1 ⊔ l2)
is-decidable-subtype-Prop {A = A} P =
  Π-Prop A (λ a → is-decidable-Prop (P a))

is-decidable-subtype : {l1 l2 : Level} {A : UU l1} → subtype l2 A → UU (l1 ⊔ l2)
is-decidable-subtype P = type-Prop (is-decidable-subtype-Prop P)

is-prop-is-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  is-prop (is-decidable-subtype P)
is-prop-is-decidable-subtype P = is-prop-type-Prop (is-decidable-subtype-Prop P)

decidable-subtype : {l1 : Level} (l : Level) (X : UU l1) → UU (l1 ⊔ lsuc l)
decidable-subtype l X = X → Decidable-Prop l
```

### The underlying subtype of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  subtype-decidable-subtype : subtype l2 A
  subtype-decidable-subtype a = prop-Decidable-Prop (P a)

  is-decidable-decidable-subtype :
    is-decidable-subtype subtype-decidable-subtype
  is-decidable-decidable-subtype a =
    is-decidable-Decidable-Prop (P a)

  is-in-decidable-subtype : A → UU l2
  is-in-decidable-subtype = is-in-subtype subtype-decidable-subtype

  is-prop-is-in-decidable-subtype :
    (a : A) → is-prop (is-in-decidable-subtype a)
  is-prop-is-in-decidable-subtype =
    is-prop-is-in-subtype subtype-decidable-subtype
```

### The underlying type of a decidable subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  type-decidable-subtype : UU (l1 ⊔ l2)
  type-decidable-subtype = type-subtype (subtype-decidable-subtype P)

  inclusion-decidable-subtype : type-decidable-subtype → A
  inclusion-decidable-subtype = inclusion-subtype (subtype-decidable-subtype P)

  is-emb-inclusion-decidable-subtype : is-emb inclusion-decidable-subtype
  is-emb-inclusion-decidable-subtype =
    is-emb-inclusion-subtype (subtype-decidable-subtype P)

  is-decidable-map-inclusion-decidable-subtype :
    is-decidable-map inclusion-decidable-subtype
  is-decidable-map-inclusion-decidable-subtype x =
    is-decidable-equiv
      ( equiv-fiber-pr1 (type-Decidable-Prop ∘ P) x)
      ( is-decidable-Decidable-Prop (P x))

  is-injective-inclusion-decidable-subtype :
    is-injective inclusion-decidable-subtype
  is-injective-inclusion-decidable-subtype =
    is-injective-inclusion-subtype (subtype-decidable-subtype P)

  emb-decidable-subtype : type-decidable-subtype ↪ A
  emb-decidable-subtype = emb-subtype (subtype-decidable-subtype P)

  is-decidable-emb-inclusion-decidable-subtype :
    is-decidable-emb inclusion-decidable-subtype
  is-decidable-emb-inclusion-decidable-subtype =
    ( is-emb-inclusion-decidable-subtype ,
      is-decidable-map-inclusion-decidable-subtype)

  decidable-emb-decidable-subtype : type-decidable-subtype ↪ᵈ A
  decidable-emb-decidable-subtype =
    ( inclusion-decidable-subtype ,
      is-decidable-emb-inclusion-decidable-subtype)
```

### The decidable subtype associated to a decidable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y)
  where

  decidable-subtype-decidable-emb : decidable-subtype (l1 ⊔ l2) Y
  pr1 (decidable-subtype-decidable-emb y) =
    fiber (map-decidable-emb f) y
  pr2 (decidable-subtype-decidable-emb y) =
    is-decidable-prop-map-is-decidable-emb
      ( is-decidable-emb-map-decidable-emb f)
      ( y)

  compute-type-decidable-type-decidable-emb :
    type-decidable-subtype decidable-subtype-decidable-emb ≃ X
  compute-type-decidable-type-decidable-emb =
    equiv-total-fiber (map-decidable-emb f)

  inv-compute-type-decidable-type-decidable-emb :
    X ≃ type-decidable-subtype decidable-subtype-decidable-emb
  inv-compute-type-decidable-type-decidable-emb =
    inv-equiv-total-fiber (map-decidable-emb f)
```

## Examples

### The decidable subtypes of left and right elements in a coproduct type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-left : (x : A + B) → is-decidable (is-left x)
  is-decidable-is-left (inl x) = is-decidable-unit
  is-decidable-is-left (inr x) = is-decidable-empty

  is-left-Decidable-Prop : A + B → Decidable-Prop lzero
  pr1 (is-left-Decidable-Prop x) = is-left x
  pr1 (pr2 (is-left-Decidable-Prop x)) = is-prop-is-left x
  pr2 (pr2 (is-left-Decidable-Prop x)) = is-decidable-is-left x

  is-decidable-is-right : (x : A + B) → is-decidable (is-right x)
  is-decidable-is-right (inl x) = is-decidable-empty
  is-decidable-is-right (inr x) = is-decidable-unit

  is-right-Decidable-Prop : A + B → Decidable-Prop lzero
  pr1 (is-right-Decidable-Prop x) = is-right x
  pr1 (pr2 (is-right-Decidable-Prop x)) = is-prop-is-right x
  pr2 (pr2 (is-right-Decidable-Prop x)) = is-decidable-is-right x
```

## Properties

### Types of decidable subtypes of any universe level are equivalent

```agda
module _
  {l1 : Level} (X : UU l1)
  where

  equiv-universes-decidable-subtype :
    (l l' : Level) → decidable-subtype l X ≃ decidable-subtype l' X
  equiv-universes-decidable-subtype l l' =
    equiv-Π
      ( λ _ → Decidable-Prop l')
      ( id-equiv)
      ( λ _ → equiv-universes-Decidable-Prop l l')

  iff-universes-decidable-subtype :
    (l l' : Level) (S : decidable-subtype l X) →
    ( (x : X) →
      type-Decidable-Prop (S x) ↔
      type-Decidable-Prop
        ( map-equiv (equiv-universes-decidable-subtype l l') S x))
  iff-universes-decidable-subtype l l' S x =
    tr
      ( λ P → type-Decidable-Prop (S x) ↔ type-Decidable-Prop P)
      ( inv
        ( compute-map-equiv-Π
          ( λ _ → Decidable-Prop l')
          ( id-equiv)
          ( λ _ → equiv-universes-Decidable-Prop l l')
          ( S)
          ( x)))
      ( iff-universes-Decidable-Prop l l' (S x))
```

### Decidable subtypes are double negation stable

```agda
is-double-negation-stable-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A) →
  is-double-negation-stable-subtype (subtype-decidable-subtype P)
is-double-negation-stable-decidable-subtype P x =
  double-negation-elim-is-decidable (is-decidable-decidable-subtype P x)
```

### A decidable subtype of a `k+1`-truncated type is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-trunc-type-decidable-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-decidable-subtype P)
    is-trunc-type-decidable-subtype =
      is-trunc-type-subtype k (subtype-decidable-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  abstract
    is-prop-type-decidable-subtype :
      is-prop A → is-prop (type-decidable-subtype P)
    is-prop-type-decidable-subtype =
      is-prop-type-subtype (subtype-decidable-subtype P)

  abstract
    is-set-type-decidable-subtype : is-set A → is-set (type-decidable-subtype P)
    is-set-type-decidable-subtype =
      is-set-type-subtype (subtype-decidable-subtype P)

  abstract
    is-1-type-type-decidable-subtype :
      is-1-type A → is-1-type (type-decidable-subtype P)
    is-1-type-type-decidable-subtype =
      is-1-type-type-subtype (subtype-decidable-subtype P)

prop-decidable-subprop :
  {l1 l2 : Level} (A : Prop l1) (P : decidable-subtype l2 (type-Prop A)) →
  Prop (l1 ⊔ l2)
prop-decidable-subprop A P = prop-subprop A (subtype-decidable-subtype P)

set-decidable-subset :
  {l1 l2 : Level} (A : Set l1) (P : decidable-subtype l2 (type-Set A)) →
  Set (l1 ⊔ l2)
set-decidable-subset A P = set-subset A (subtype-decidable-subtype P)
```

### The type of decidable subtypes of a type is a set

```agda
is-set-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} → is-set (decidable-subtype l2 X)
is-set-decidable-subtype =
  is-set-function-type is-set-Decidable-Prop
```

### Extensionality of the type of decidable subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-subtype l2 A)
  where

  has-same-elements-decidable-subtype :
    {l3 : Level} → decidable-subtype l3 A → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-decidable-subtype Q =
    has-same-elements-subtype
      ( subtype-decidable-subtype P)
      ( subtype-decidable-subtype Q)

  extensionality-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) ≃ has-same-elements-decidable-subtype Q
  extensionality-decidable-subtype =
    extensionality-Π P
      ( λ x Q → (type-Decidable-Prop (P x)) ↔ (type-Decidable-Prop Q))
      ( λ x Q → extensionality-Decidable-Prop (P x) Q)

  has-same-elements-eq-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    (P ＝ Q) → has-same-elements-decidable-subtype Q
  has-same-elements-eq-decidable-subtype Q =
    map-equiv (extensionality-decidable-subtype Q)

  eq-has-same-elements-decidable-subtype :
    (Q : decidable-subtype l2 A) →
    has-same-elements-decidable-subtype Q → P ＝ Q
  eq-has-same-elements-decidable-subtype Q =
    map-inv-equiv (extensionality-decidable-subtype Q)

  refl-extensionality-decidable-subtype :
    map-equiv (extensionality-decidable-subtype P) refl ＝ (λ x → pair id id)
  refl-extensionality-decidable-subtype = refl
```

### The type of decidable subtypes of `A` is equivalent to the type of all decidable embeddings into a type `A`

```agda
equiv-Fiber-Decidable-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Σ (UU (l1 ⊔ l)) (λ X → X ↪ᵈ A) ≃ (decidable-subtype (l1 ⊔ l) A)
equiv-Fiber-Decidable-Prop l A =
  ( equiv-Fiber-structure l is-decidable-prop A) ∘e
  ( equiv-tot
    ( λ X →
      equiv-tot
        ( λ f →
          ( inv-distributive-Π-Σ) ∘e
          ( equiv-product-left (equiv-is-prop-map-is-emb f)))))
```

### The type of decidable subtypes of `A` is equivalent to the type of all maps from `A` to booleans

```agda
equiv-decidable-subtype-map-bool :
  {l1 l2 : Level} → (A : UU l1) → decidable-subtype l2 A ≃ (A → bool)
equiv-decidable-subtype-map-bool A = equiv-postcomp A equiv-bool-Decidable-Prop
```
