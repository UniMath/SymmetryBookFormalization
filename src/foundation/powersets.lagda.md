# Powersets

```agda
module foundation.powersets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.identity-types
open import foundation.large-locale-of-propositions
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.sets

open import order-theory.bottom-elements-large-posets
open import order-theory.bottom-elements-posets
open import order-theory.dependent-products-large-meet-semilattices
open import order-theory.dependent-products-large-posets
open import order-theory.dependent-products-large-preorders
open import order-theory.dependent-products-large-suplattices
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.meet-semilattices
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.similarity-of-elements-large-posets
open import order-theory.suplattices
open import order-theory.top-elements-large-posets
open import order-theory.top-elements-posets
```

</details>

## Idea

The
{{#concept "powerset" Disambiguation="of a type" Agda=powerset WD="power set" WDID=Q205170}}
of a type is the [set](foundation-core.sets.md) of all
[subtypes](foundation-core.subtypes.md).

## Definition

```agda
powerset :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
powerset = subtype
```

## Properties

### The powerset is a set

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  is-set-powerset : {l2 : Level} → is-set (powerset l2 A)
  is-set-powerset = is-set-subtype

  powerset-Set : (l2 : Level) → Set (l1 ⊔ lsuc l2)
  powerset-Set l2 = subtype-Set l2 A
```

### The powerset large preorder

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Preorder :
    Large-Preorder (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  powerset-Large-Preorder = Π-Large-Preorder {I = A} (λ _ → Prop-Large-Preorder)

module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  powerset-Preorder : Preorder (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Preorder = preorder-Large-Preorder (powerset-Large-Preorder A) l2
```

### The powerset large poset

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Poset :
    Large-Poset (λ l → l1 ⊔ lsuc l) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  powerset-Large-Poset = Π-Large-Poset {I = A} (λ _ → Prop-Large-Poset)

module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  powerset-Poset : Poset (l1 ⊔ lsuc l2) (l1 ⊔ l2)
  powerset-Poset = poset-Large-Poset (powerset-Large-Poset A) l2
```

### The powerset poset has a top element

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  has-top-element-powerset-Large-Poset :
    has-top-element-Large-Poset (powerset-Large-Poset A)
  has-top-element-powerset-Large-Poset =
    has-top-element-Π-Large-Poset
      ( λ _ → Prop-Large-Poset)
      ( λ _ → has-top-element-Prop-Large-Locale)

  has-top-element-powerset-Poset :
    {l2 : Level} → has-top-element-Poset (powerset-Poset l2 A)
  has-top-element-powerset-Poset {l2} =
    (λ _ → raise-unit-Prop l2) , (λ _ _ _ → raise-star)
```

### The powerset poset has a bottom element

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  has-bottom-element-powerset-Large-Poset :
    has-bottom-element-Large-Poset (powerset-Large-Poset A)
  has-bottom-element-powerset-Large-Poset =
    has-bottom-element-Π-Large-Poset
      ( λ _ → Prop-Large-Poset)
      ( λ _ → has-bottom-element-Prop-Large-Locale)

  has-bottom-element-powerset-Poset :
    {l2 : Level} → has-bottom-element-Poset (powerset-Poset l2 A)
  has-bottom-element-powerset-Poset {l2} =
    (λ _ → raise-empty-Prop l2) , (λ _ _ → raise-ex-falso l2)
```

### The powerset meet semilattice

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Meet-Semilattice :
    Large-Meet-Semilattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ l2 ⊔ l3)
  powerset-Large-Meet-Semilattice =
    Π-Large-Meet-Semilattice {I = A} (λ _ → Prop-Large-Meet-Semilattice)
```

### The powerset suplattice

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  powerset-Large-Suplattice :
    Large-Suplattice (λ l2 → lsuc l2 ⊔ l1) (λ l2 l3 → l2 ⊔ l3 ⊔ l1) lzero
  powerset-Large-Suplattice =
    Π-Large-Suplattice {I = A} (λ _ → Prop-Large-Suplattice)

  powerset-Suplattice :
    (l2 l3 : Level) → Suplattice (l1 ⊔ lsuc l2 ⊔ lsuc l3) (l1 ⊔ l2 ⊔ l3) l2
  powerset-Suplattice = suplattice-Large-Suplattice powerset-Large-Suplattice
```

### Similarity of subtypes

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) (Q : subtype l3 A)
  where

  sim-prop-subtype : Prop (l1 ⊔ l2 ⊔ l3)
  sim-prop-subtype = sim-prop-Large-Poset (powerset-Large-Poset A) P Q

  sim-subtype : UU (l1 ⊔ l2 ⊔ l3)
  sim-subtype = type-Prop sim-prop-subtype

  has-same-elements-sim-subtype :
    sim-subtype → has-same-elements-subtype P Q
  pr1 (has-same-elements-sim-subtype s x) = pr1 s x
  pr2 (has-same-elements-sim-subtype s x) = pr2 s x

  sim-has-same-elements-subtype :
    has-same-elements-subtype P Q → sim-subtype
  pr1 (sim-has-same-elements-subtype s) x = forward-implication (s x)
  pr2 (sim-has-same-elements-subtype s) x = backward-implication (s x)
```

#### Similarity is reflexive

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  refl-sim-subtype : {l2 : Level} → (P : subtype l2 A) → sim-subtype P P
  refl-sim-subtype = refl-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is symmetric

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  symmetric-sim-subtype :
    {l2 l3 : Level} →
    (P : subtype l2 A) (Q : subtype l3 A) →
    sim-subtype P Q → sim-subtype Q P
  symmetric-sim-subtype = symmetric-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is transitive

```agda
  transitive-sim-subtype :
    {l2 l3 l4 : Level} →
    (P : subtype l2 A) →
    (Q : subtype l3 A) →
    (R : subtype l4 A) →
    sim-subtype Q R →
    sim-subtype P Q →
    sim-subtype P R
  transitive-sim-subtype = transitive-sim-Large-Poset (powerset-Large-Poset A)
```

#### Similarity is antisymmetric at the same universe level

```agda
  eq-sim-subtype :
    {l2 : Level} →
    (P Q : subtype l2 A) →
    sim-subtype P Q →
    P ＝ Q
  eq-sim-subtype = eq-sim-Large-Poset (powerset-Large-Poset A)
```

## See also

- [the large locale of subtypes](foundation.large-locale-of-subtypes.md)
- [images of subtypes](foundation.images-subtypes.md)

## External links

- [power object](https://ncatlab.org/nlab/show/power+object) at $n$Lab
- [power set](https://ncatlab.org/nlab/show/power+set) at $n$Lab
- [Power set](https://en.wikipedia.org/wiki/Power_set) at Wikipedia
