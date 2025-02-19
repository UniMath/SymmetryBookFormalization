# Right linear combinations with respect to semirings

```agda
module ring-theory.right-linear-combinations-of-elements-semirings where
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

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists

open import ring-theory.monoids-with-right-semiring-actions
open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import structured-types.magmas
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$ and a type $A$. A {#concept
"right linear combination"}} of elements of $R$ is a [list](lists.lists.md) of
pairs $(a,r)$ consisting of an element $a:A$ and an element $r:R$.

Furthermore, if we are given an action $\mu : A \to R \to M$ taking values in a
[unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a
right linear combination $((a_0,r_0),\ldots,(a_{n-1},r_{n-1}))$ by defining

$$
  ev((a_0,r_0),\ldots,(a_{n-1},r_{n-1})) := \sum_{i=0}^{n-1} \mu(a_i,r_i).
$$

To be explicit, right linear combinations of elements of a type $A$ have the
semiring coefficients on the right.

## Definitions

### The type of right linear combinations

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2)
  where

  right-linear-combination-Semiring :
    UU (l1 ⊔ l2)
  right-linear-combination-Semiring =
    list (A × type-Semiring R)
```

### Multiplying right linear combinations by a scalar

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {A : UU l2}
  where

  mul-right-linear-combination-Semiring :
    right-linear-combination-Semiring R A →
    type-Semiring R →
    right-linear-combination-Semiring R A
  mul-right-linear-combination-Semiring l r =
    map-list (λ (a , s) → (a , mul-Semiring R s r)) l
```

### Evaluating right linear combinations of elements in unital magmas

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  ev-unital-magma-right-linear-combination-Semiring :
    (M : Unital-Magma l3) (μ : A → type-Semiring R → type-Unital-Magma M) →
    right-linear-combination-Semiring R A → type-Unital-Magma M
  ev-unital-magma-right-linear-combination-Semiring M μ nil =
    unit-Unital-Magma M
  ev-unital-magma-right-linear-combination-Semiring M μ (cons (a , r) l) =
    mul-Unital-Magma M
      ( μ a r)
      ( ev-unital-magma-right-linear-combination-Semiring M μ l)

  ev-monoid-right-linear-combination-Semiring :
    (M : Monoid l3) (μ : A → type-Semiring R → type-Monoid M) →
    right-linear-combination-Semiring R A → type-Monoid M
  ev-monoid-right-linear-combination-Semiring M =
    ev-unital-magma-right-linear-combination-Semiring
      ( unital-magma-Monoid M)
```

### The predicate of being a right linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2}
  where

  is-right-linear-combination-Semiring :
    (M : Unital-Magma l3) (μ : A → type-Semiring R → type-Unital-Magma M) →
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-right-linear-combination-Semiring M μ =
    fiber (ev-unital-magma-right-linear-combination-Semiring R M μ)

  is-right-linear-combination-monoid-Semiring :
    (M : Monoid l3) (μ : A → type-Semiring R → type-Monoid M) →
    type-Monoid M → UU (l1 ⊔ l2 ⊔ l3)
  is-right-linear-combination-monoid-Semiring M =
    is-right-linear-combination-Semiring (unital-magma-Monoid M)
```

### The predicate of being a mere right linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Semiring R → type-Unital-Magma M)
  where

  is-mere-right-linear-combination-prop-Semiring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-right-linear-combination-prop-Semiring x =
    trunc-Prop (is-right-linear-combination-Semiring R M μ x)

  is-mere-right-linear-combination-Semiring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-right-linear-combination-Semiring x =
    type-trunc-Prop (is-right-linear-combination-Semiring R M μ x)

  is-prop-is-mere-right-linear-combination-Semiring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-right-linear-combination-Semiring x)
  is-prop-is-mere-right-linear-combination-Semiring x =
    is-prop-type-trunc-Prop
```

### Right linear combinations of subsets of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  right-linear-combination-subset-Semiring :
    UU (l1 ⊔ l2)
  right-linear-combination-subset-Semiring =
    right-linear-combination-Semiring R (type-subset-Semiring R S)

  ev-right-linear-combination-subset-Semiring :
    right-linear-combination-subset-Semiring → type-Semiring R
  ev-right-linear-combination-subset-Semiring =
    ev-unital-magma-right-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ s → mul-Semiring R (inclusion-subset-Semiring R S s))

  is-right-linear-combination-subset-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-right-linear-combination-subset-Semiring =
    is-right-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ s → mul-Semiring R (inclusion-subset-Semiring R S s))

  is-mere-right-linear-combination-prop-subset-Semiring :
    type-Semiring R → Prop (l1 ⊔ l2)
  is-mere-right-linear-combination-prop-subset-Semiring =
    is-mere-right-linear-combination-prop-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ s r → mul-Semiring R (inclusion-subset-Semiring R S s) r)
```

### Right linear combinations of families of elements in a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) {I : UU l2} (a : I → type-Semiring R)
  where

  right-linear-combination-family-of-elements-Semiring :
    UU (l1 ⊔ l2)
  right-linear-combination-family-of-elements-Semiring =
    right-linear-combination-subset-Semiring R (trunc-Prop ∘ fiber a)

  ev-right-linear-combination-family-of-elements-Semiring :
    right-linear-combination-family-of-elements-Semiring → type-Semiring R
  ev-right-linear-combination-family-of-elements-Semiring =
    ev-right-linear-combination-subset-Semiring R
      ( trunc-Prop ∘ fiber a)

  is-right-linear-combination-family-of-elements-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-right-linear-combination-family-of-elements-Semiring =
    is-right-linear-combination-subset-Semiring R
      ( trunc-Prop ∘ fiber a)
```

## Properties

### Given a right action of a semiring $R$ on a type $A$ with values in a monoid, the evaluation function preserves concatenation

We assume a monoid here, because we need associativity for the multiplicative
operation of the monoid.

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid l3)
  (μ : A → type-Semiring R → type-Monoid M)
  where

  preserves-concat-ev-monoid-right-linear-combination-Semiring :
    (u v : right-linear-combination-Semiring R A) →
    ev-monoid-right-linear-combination-Semiring R M
      ( μ)
      ( concat-list u v) ＝
    mul-Monoid M
      ( ev-monoid-right-linear-combination-Semiring R M μ u)
      ( ev-monoid-right-linear-combination-Semiring R M μ v)
  preserves-concat-ev-monoid-right-linear-combination-Semiring nil v =
    inv
      ( left-unit-law-mul-Monoid M
        ( ev-monoid-right-linear-combination-Semiring R M μ v))
  preserves-concat-ev-monoid-right-linear-combination-Semiring
    ( cons (r , s) u) v =
    ( ap
      ( mul-Monoid M (μ r s))
      ( preserves-concat-ev-monoid-right-linear-combination-Semiring u v)) ∙
    ( inv
      ( associative-mul-Monoid M
        ( μ r s)
        ( ev-monoid-right-linear-combination-Semiring R M μ u)
        ( ev-monoid-right-linear-combination-Semiring R M μ v)))

  is-right-linear-combination-mul-monoid-Semiring :
    (x y : type-Monoid M) →
    is-right-linear-combination-monoid-Semiring R M μ x →
    is-right-linear-combination-monoid-Semiring R M μ y →
    is-right-linear-combination-monoid-Semiring R M μ (mul-Monoid M x y)
  is-right-linear-combination-mul-monoid-Semiring x y (u , refl) (v , refl) =
    ( concat-list u v ,
      preserves-concat-ev-monoid-right-linear-combination-Semiring u v)
```

### Evaluation of linear combinations preserves scalar multiplication

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Monoid-With-Right-Semiring-Action l3 R)
  (μ : A → type-Semiring R → type-Monoid-With-Right-Semiring-Action R M)
  (α :
    (a : A) (r s : type-Semiring R) →
    μ a (mul-Semiring R r s) ＝
    action-Monoid-With-Right-Semiring-Action R M (μ a r) s)
  where

  preserves-mul-ev-right-linear-combination-Semiring :
    (u : right-linear-combination-Semiring R A) (r : type-Semiring R) →
    ev-monoid-right-linear-combination-Semiring R
      ( monoid-Monoid-With-Right-Semiring-Action R M)
      ( μ)
      ( mul-right-linear-combination-Semiring R u r) ＝
    action-Monoid-With-Right-Semiring-Action R M
      ( ev-monoid-right-linear-combination-Semiring R
        ( monoid-Monoid-With-Right-Semiring-Action R M)
        ( μ)
        ( u))
      ( r)
  preserves-mul-ev-right-linear-combination-Semiring nil r =
    inv (right-absorption-law-action-Monoid-With-Right-Semiring-Action R M r)
  preserves-mul-ev-right-linear-combination-Semiring (cons (a , s) u) r =
    ap-binary
      ( mul-Monoid-With-Right-Semiring-Action R M)
      ( α a s r)
      ( preserves-mul-ev-right-linear-combination-Semiring u r) ∙
    inv
      ( right-distributive-action-mul-Monoid-With-Right-Semiring-Action R M
        ( μ a s)
        ( ev-monoid-right-linear-combination-Semiring R
          ( monoid-Monoid-With-Right-Semiring-Action R M)
          ( μ)
          ( u))
        ( r))

  is-right-linear-combination-action-Semiring :
    (x : type-Monoid-With-Right-Semiring-Action R M) (r : type-Semiring R) →
    is-right-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Right-Semiring-Action R M)
      ( μ)
      ( x) →
    is-right-linear-combination-monoid-Semiring R
      ( monoid-Monoid-With-Right-Semiring-Action R M)
      ( μ)
      ( action-Monoid-With-Right-Semiring-Action R M x r)
  is-right-linear-combination-action-Semiring x r (u , refl) =
    ( mul-right-linear-combination-Semiring R u r ,
      preserves-mul-ev-right-linear-combination-Semiring u r)
```
