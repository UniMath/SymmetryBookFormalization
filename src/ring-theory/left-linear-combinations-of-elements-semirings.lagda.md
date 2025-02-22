# Left linear combinations with respect to semirings

```agda
module ring-theory.left-linear-combinations-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.monoids-with-semiring-actions
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import structured-types.magmas
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$ and a type $A$. A {#concept "left linear combination"}} of elements of $R$ is a [list](lists.lists.md) of pairs $(r,a)$ consisting of an element $r:R$ and an element $a:A$.

Furthermore, if we are given an action $\mu : R \to A \to M$ taking values in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a left linear combination $((r_0,a_0),\ldots,(r_{n-1},a_{n-1}))$ by defining

$$
  ev((r_0,a_0),\ldots,(r_{n-1},a_{n-1})) := \sum_{i=0}^{n-1} \mu(r_i,a_i).
$$

To be explicit, left linear combinations of elements of a type $A$ have the semiring coefficients on the left.


## Definitions

### The type of left linear combinations

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2)
  where

  left-linear-combination-Semiring :
    UU (l1 ⊔ l2)
  left-linear-combination-Semiring =
    list (type-Semiring R × A)
```

### Multiplying linear combinations by a scalar

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {A : UU l2}
  where

  mul-left-linear-combination-Semiring :
    type-Semiring R →
    left-linear-combination-Semiring R A →
    left-linear-combination-Semiring R A
  mul-left-linear-combination-Semiring r =
    map-list (λ (s , a) → (mul-Semiring R r s , a))
```

### Evaluating left linear combinations of elements

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  ev-unital-magma-left-linear-combination-Semiring :
    (M : Unital-Magma l3) (μ : type-Semiring R → A → type-Unital-Magma M) →
    left-linear-combination-Semiring R A → type-Unital-Magma M
  ev-unital-magma-left-linear-combination-Semiring M μ nil =
    unit-Unital-Magma M
  ev-unital-magma-left-linear-combination-Semiring M μ (cons (r , a) l) =
    mul-Unital-Magma M
      ( μ r a)
      ( ev-unital-magma-left-linear-combination-Semiring M μ l)

  ev-monoid-left-linear-combination-Semiring :
    (M : Monoid l3) (μ : type-Semiring R → A → type-Monoid M) →
    left-linear-combination-Semiring R A → type-Monoid M
  ev-monoid-left-linear-combination-Semiring M =
    ev-unital-magma-left-linear-combination-Semiring (unital-magma-Monoid M)
```

### The predicate of being a left linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  is-left-linear-combination-Semiring :
     (M : Unital-Magma l3) (μ : type-Semiring R → A → type-Unital-Magma M) →
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-left-linear-combination-Semiring M μ =
    fiber (ev-unital-magma-left-linear-combination-Semiring R M μ)

  is-left-linear-combination-monoid-Semiring :
    (M : Monoid l3) (μ : type-Semiring R → A → type-Monoid M) →
    type-Monoid M → UU (l1 ⊔ l2 ⊔ l3)
  is-left-linear-combination-monoid-Semiring M =
    is-left-linear-combination-Semiring (unital-magma-Monoid M)
```

### The predicate of being a mere left linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Semiring R → A → type-Unital-Magma M)
  where

  is-mere-left-linear-combination-prop-Semiring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-left-linear-combination-prop-Semiring x =
    trunc-Prop (is-left-linear-combination-Semiring R M μ x)

  is-mere-left-linear-combination-Semiring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-left-linear-combination-Semiring x =
    type-trunc-Prop (is-left-linear-combination-Semiring R M μ x)

  is-prop-is-mere-left-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-left-linear-combination-Semiring x)
  is-prop-is-mere-left-linear-combination-Semiring x =
    is-prop-type-trunc-Prop
```

### Left linear combinations of subsets of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  left-linear-combination-subset-Semiring :
    UU (l1 ⊔ l2)
  left-linear-combination-subset-Semiring =
    left-linear-combination-Semiring R (type-subset-Semiring R S)

  ev-left-linear-combination-subset-Semiring :
    left-linear-combination-subset-Semiring → type-Semiring R
  ev-left-linear-combination-subset-Semiring =
    ev-unital-magma-left-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ r s → mul-Semiring R r (inclusion-subset-Semiring R S s))

  is-left-linear-combination-subset-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-left-linear-combination-subset-Semiring =
    is-left-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ r s → mul-Semiring R r (inclusion-subset-Semiring R S s))

  is-mere-left-linear-combination-prop-subset-Semiring :
    type-Semiring R → Prop (l1 ⊔ l2)
  is-mere-left-linear-combination-prop-subset-Semiring =
    is-mere-left-linear-combination-prop-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ r s → mul-Semiring R r (inclusion-subset-Semiring R S s))
```

### Left linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {I : UU l2} (a : I → type-Semiring R)
  where

  left-linear-combination-family-of-elements-Semiring :
    UU (l1 ⊔ l2)
  left-linear-combination-family-of-elements-Semiring =
    left-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)

  ev-unital-magma-left-linear-combination-family-of-elements-Semiring :
    left-linear-combination-family-of-elements-Semiring → type-Semiring R
  ev-unital-magma-left-linear-combination-family-of-elements-Semiring =
    ev-left-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)

  is-left-linear-combination-family-of-elements-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-left-linear-combination-family-of-elements-Semiring =
    is-left-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)
```

## Properties

### Given a left action of a semiring $R$ on a type $A$ with values in a monoid, the evaluation function preserves concatenation

We assume a monoid here, because we need associativity for the multiplicative operation of the monoid.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid l3)
  (μ : type-Semiring R → A → type-Monoid M)
  where

  preserves-concat-ev-monoid-left-linear-combination-Semiring :
    (u v : left-linear-combination-Semiring R A) →
    ev-monoid-left-linear-combination-Semiring R M
      ( μ)
      ( concat-list u v) ＝
    mul-Monoid M
      ( ev-monoid-left-linear-combination-Semiring R M μ u)
      ( ev-monoid-left-linear-combination-Semiring R M μ v)
  preserves-concat-ev-monoid-left-linear-combination-Semiring nil v =
    inv
      ( left-unit-law-mul-Monoid M
        ( ev-monoid-left-linear-combination-Semiring R M μ v))
  preserves-concat-ev-monoid-left-linear-combination-Semiring
    ( cons (r , s) u) v =
    ( ap
      ( mul-Monoid M (μ r s))
      ( preserves-concat-ev-monoid-left-linear-combination-Semiring u v)) ∙
    ( inv
      ( associative-mul-Monoid M
        ( μ r s)
        ( ev-monoid-left-linear-combination-Semiring R M μ u)
        ( ev-monoid-left-linear-combination-Semiring R M μ v)))

  is-left-linear-combination-mul-monoid-Semiring :
    (x y : type-Monoid M) →
    is-left-linear-combination-monoid-Semiring R M μ x →
    is-left-linear-combination-monoid-Semiring R M μ y →
    is-left-linear-combination-monoid-Semiring R M μ (mul-Monoid M x y)
  is-left-linear-combination-mul-monoid-Semiring x y (u , refl) (v , refl) =
    ( concat-list u v ,
      preserves-concat-ev-monoid-left-linear-combination-Semiring u v)
```

### Evaluation of linear combinations preserves scalar multiplication

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid-With-Left-Semiring-Action l3 R)
  (μ : type-Semiring R → A → type-Monoid-With-Left-Semiring-Action R M)
  (α :
    (s r : type-Semiring R) (a : A) →
    μ (mul-Semiring R s r) a ＝
    action-Monoid-With-Left-Semiring-Action R M s (μ r a))
  where

  preserves-mul-ev-left-linear-combination-Semiring :
    (r : type-Semiring R) (u : left-linear-combination-Semiring R A) →
    ev-monoid-left-linear-combination-Semiring R
      ( monoid-Monoid-With-Left-Semiring-Action R M)
      ( μ)
      ( mul-left-linear-combination-Semiring R r u) ＝
    action-Monoid-With-Left-Semiring-Action R M r
      ( ev-monoid-left-linear-combination-Semiring R
        ( monoid-Monoid-With-Left-Semiring-Action R M)
        ( μ)
        ( u))
  preserves-mul-ev-left-linear-combination-Semiring r nil =
    inv (right-absorption-law-action-Monoid-With-Left-Semiring-Action R M r)
  preserves-mul-ev-left-linear-combination-Semiring r (cons (s , a) u) =
    ap-binary
      ( mul-Monoid-With-Left-Semiring-Action R M)
      ( α r s a)
      ( preserves-mul-ev-left-linear-combination-Semiring r u) ∙
    inv
      ( left-distributive-action-mul-Monoid-With-Left-Semiring-Action R M r
        ( μ s a)
        ( ev-monoid-left-linear-combination-Semiring R
          ( monoid-Monoid-With-Left-Semiring-Action R M)
          ( μ)
          ( u)))

  is-left-linear-combination-action-Semiring :
    (r : type-Semiring R) (x : type-Monoid-With-Left-Semiring-Action R M) →
    is-left-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Left-Semiring-Action R M)
      ( μ)
      ( x) →
    is-left-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Left-Semiring-Action R M)
      ( μ)
      ( action-Monoid-With-Left-Semiring-Action R M r x)
  is-left-linear-combination-action-Semiring r x (u , refl) =
    ( mul-left-linear-combination-Semiring R r u ,
      preserves-mul-ev-left-linear-combination-Semiring r u)
```
