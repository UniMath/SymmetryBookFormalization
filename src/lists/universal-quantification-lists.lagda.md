# Universal quantification over the elements of lists

```agda
module lists.universal-quantification-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.elementhood-relation-lists
open import lists.lists
open import lists.permutation-lists

open import finite-group-theory.permutations-standard-finite-types
```

</details>

## Idea

Consider a predicate `P` on a type `X`, and consider a [list](lists.lists.md)
`l` of elements of `X`. The
{{#concept "universal quantification" Disambiguation="elements of a list" Agda=for-all-list}}
of `P` over the elements of `l` is the type of choices of elements `P x` for
each element `x ∈ l`. More specifically, the universal quantification `∀ l P` of
`P` over `l` is defined inductively by

```text
  ∀ nil P := unit
  ∀ (cons x l) P := (P x) × (∀ l P)
```

Alternatively, the universal quantification over the elements of a list can be
defined directly by

```text
  ∀ l P := (x : X) → x ∈ l → P x.
```

These definitions are [equivalent](foundation-core.equivalences.md). However,
note that the inductive definition of the universal quantification has the same
universe level as `P`, while the direct definition is of universe level
`l1 ⊔ l2`, where `l1` is the universe level of `X` and `l2` is the universe
level of `P`.

Note that the universal quantification over the elements of a list `l` is
equivalent to the type of [dependent lists](lists.dependent-lists.md) of
elements of `P` over `l`.

## Definitions

### Universal quantification over the elements of a list

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  for-all-list :
    (l : list X) (P : X → UU l2) → UU l2
  for-all-list nil P = raise-unit l2
  for-all-list (cons x l) P = P x × for-all-list l P

  for-all-nil-list :
    (P : X → UU l2) → for-all-list nil P
  for-all-nil-list P = raise-star

  head-for-all-cons-list :
    (x : X) (l : list X) (P : X → UU l2) → for-all-list (cons x l) P → P x
  head-for-all-cons-list x l P H = pr1 H

  tail-for-all-cons-list :
    (x : X) (l : list X) (P : X → UU l2) →
    for-all-list (cons x l) P → for-all-list l P
  tail-for-all-cons-list x l P H = pr2 H
```

### Universal quantification by a predicate valued in propositions

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-prop-for-all-list :
    (l : list X) (P : X → Prop l2) → is-prop (for-all-list l (type-Prop ∘ P))
  is-prop-for-all-list nil P =
    is-prop-raise-unit
  is-prop-for-all-list (cons x l) P =
    is-prop-product (is-prop-type-Prop (P x)) (is-prop-for-all-list l P)

  for-all-list-Prop :
    (l : list X) (P : X → Prop l2) → Prop l2
  pr1 (for-all-list-Prop l P) = for-all-list l (type-Prop ∘ P)
  pr2 (for-all-list-Prop l P) = is-prop-for-all-list l P
```

### Universal quantification over the elements of a list

```agda
module _
  {l1 l2 : Level} {X : UU l1} (l : list X) (P : X → UU l2)
  where

  for-all-elements-list : UU (l1 ⊔ l2)
  for-all-elements-list = (x : X) → x ∈-list l → P x

for-all-elements-nil-list :
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) → for-all-elements-list nil P
for-all-elements-nil-list P x ()

for-all-elements-cons-list :
  {l1 l2 : Level} {X : UU l1} (x : X) (l : list X) (P : X → UU l2) →
  P x → for-all-elements-list l P → for-all-elements-list (cons x l) P
for-all-elements-cons-list x l P a b .x (is-head .x .l) = a
for-all-elements-cons-list x l P a b y (is-in-tail .y .x .l H) = b y H

head-for-all-elements-cons-list :
  {l1 l2 : Level} {X : UU l1} (x : X) (l : list X) (P : X → UU l2) →
  for-all-elements-list (cons x l) P → P x
head-for-all-elements-cons-list x l P H = H x (is-head x l)

tail-for-all-elements-cons-list :
  {l1 l2 : Level} {X : UU l1} (x : X) (l : list X) (P : X → UU l2) →
  for-all-elements-list (cons x l) P → for-all-elements-list l P
tail-for-all-elements-cons-list x l P H y K = H y (is-in-tail y x l K)
```

## Properties

### The two definitions of universal quantification over the elements of a list are equivalent

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  is-contr-for-all-elements-nil-list :
    (P : X → UU l2) → is-contr (for-all-elements-list nil P)
  pr1 (is-contr-for-all-elements-nil-list P) =
    for-all-elements-nil-list P
  pr2 (is-contr-for-all-elements-nil-list P) H =
    eq-htpy (λ x → eq-htpy (λ K → ex-falso (is-empty-∈-nil-list x K)))

  compute-for-all-elements-nil-list :
    (P : X → UU l2) → for-all-elements-list nil P ≃ raise-unit l2
  compute-for-all-elements-nil-list P =
    equiv-is-contr
      ( is-contr-for-all-elements-nil-list P)
      ( is-contr-raise-unit)

  module _
    (x : X) (l : list X) (P : X → UU l2)
    where

    map-compute-for-all-elements-cons-list :
      P x × for-all-elements-list l P → for-all-elements-list (cons x l) P
    map-compute-for-all-elements-cons-list (a , b) =
      for-all-elements-cons-list x l P a b

    map-inv-compute-for-all-elements-cons-list :
      for-all-elements-list (cons x l) P → P x × for-all-elements-list l P
    pr1 (map-inv-compute-for-all-elements-cons-list H) =
      head-for-all-elements-cons-list x l P H
    pr2 (map-inv-compute-for-all-elements-cons-list H) =
      tail-for-all-elements-cons-list x l P H

    is-section-map-inv-compute-for-all-elements-cons-list' :
      (H : for-all-elements-list (cons x l) P) →
      (y : X) (K : y ∈-list cons x l) →
      map-compute-for-all-elements-cons-list
        ( map-inv-compute-for-all-elements-cons-list H)
        ( y)
        ( K) ＝
      H y K
    is-section-map-inv-compute-for-all-elements-cons-list' H y (is-head .y .l) =
      refl
    is-section-map-inv-compute-for-all-elements-cons-list' H y
      ( is-in-tail .y .x .l K) =
      refl

    is-section-map-inv-compute-for-all-elements-cons-list :
      is-section
        map-compute-for-all-elements-cons-list
        map-inv-compute-for-all-elements-cons-list
    is-section-map-inv-compute-for-all-elements-cons-list H =
      eq-htpy
        ( λ y →
          eq-htpy
            ( is-section-map-inv-compute-for-all-elements-cons-list' H y))

    is-retraction-map-inv-compute-for-all-elements-cons-list :
      is-retraction
        map-compute-for-all-elements-cons-list
        map-inv-compute-for-all-elements-cons-list
    is-retraction-map-inv-compute-for-all-elements-cons-list H =
      refl

    is-equiv-map-compute-for-all-elements-cons-list :
      is-equiv map-compute-for-all-elements-cons-list
    is-equiv-map-compute-for-all-elements-cons-list =
      is-equiv-is-invertible
        map-inv-compute-for-all-elements-cons-list
        is-section-map-inv-compute-for-all-elements-cons-list
        is-retraction-map-inv-compute-for-all-elements-cons-list

    compute-for-all-elements-cons-list :
      P x × for-all-elements-list l P ≃ for-all-elements-list (cons x l) P
    pr1 compute-for-all-elements-cons-list =
      map-compute-for-all-elements-cons-list
    pr2 compute-for-all-elements-cons-list =
      is-equiv-map-compute-for-all-elements-cons-list

  compute-for-all-list :
    (l : list X) (P : X → UU l2) →
    for-all-elements-list l P ≃ for-all-list l P
  compute-for-all-list nil P = compute-for-all-elements-nil-list P
  compute-for-all-list (cons x l) P =
    ( equiv-product id-equiv (compute-for-all-list l P)) ∘e
    ( inv-equiv (compute-for-all-elements-cons-list x l P))
```

### If a predicate implies another predicate, then its universal quantification over the elements of a list implies the universal-quantification of the other predicate

```agda
map-for-all-list :
  {l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3} →
  (l : list X) → ((x : X) → P x → Q x) →
  for-all-list l P → for-all-list l Q
map-for-all-list nil f H = raise-star
pr1 (map-for-all-list (cons x l) f (H , K)) = f _ H
pr2 (map-for-all-list (cons x l) f (H , K)) = map-for-all-list l f K
```

### If two lists satisfy a universally quantified predicate, then so does their concatenation

```agda
for-all-concat-list :
  {l1 l2 : Level} {X : UU l1} (l k : list X) (P : X → UU l2) →
  for-all-list l P → for-all-list k P → for-all-list (concat-list l k) P
for-all-concat-list nil k P H K = K
pr1 (for-all-concat-list (cons x l) k P H K) =
  head-for-all-cons-list x l P H
pr2 (for-all-concat-list (cons x l) k P H K) =
  for-all-concat-list l k P (tail-for-all-cons-list x l P H) K
```

### If a lists satisfies a universally quantified predicate, then so does any permutation of the list

```text
for-all-permute-list :
  {l1 l2 : Level} {X : UU l1}  (l : list X) (P : X → UU l2)
  (e : permutation (length-list l)) →
  for-all-list l P → for-all-list (permute-list l e) P
for-all-permute-list l P e H = {!!}
```
