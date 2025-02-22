# Right linear combinations with respect to semirings

```agda
module ring-theory.right-linear-combinations-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.semirings
open import ring-theory.subsets-semirings

open import lists.lists

open import structured-types.magmas
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$ and a type $A$. A {#concept "right linear combination"}} of elements of $R$ is a [list](lists.lists.md) of pairs $(a,r)$ consisting of an element $a:A$ and an element $r:R$.

Furthermore, if we are given an action $\mu : A \to R \to M$ taking values in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a right linear combination $((a_0,r_0),\ldots,(a_{n-1},r_{n-1}))$ by defining

$$
  ev((a_0,r_0),\ldots,(a_{n-1},r_{n-1})) := \sum_{i=0}^{n-1} \mu(a_i,r_i).
$$

To be explicit, right linear combinations of elements of a type $A$ have the semiring coefficients on the right.

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

### Evaluating right linear combinations of elements in unital magmas

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Semiring R → type-Unital-Magma M)
  where

  ev-right-linear-combination-Semiring :
    right-linear-combination-Semiring R A → type-Unital-Magma M
  ev-right-linear-combination-Semiring nil =
    unit-Unital-Magma M
  ev-right-linear-combination-Semiring (cons (a , r) l) =
    mul-Unital-Magma M (μ a r) (ev-right-linear-combination-Semiring l)
```

### The predicate of being a right linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Semiring R → type-Unital-Magma M)
  where

  is-right-linear-combination-Semiring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-right-linear-combination-Semiring =
    fiber (ev-right-linear-combination-Semiring R M μ)
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
    ev-right-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ s → mul-Semiring R (inclusion-subset-Semiring R S s))

  is-right-linear-combination-subset-Semiring :
    type-Semiring R → UU (l1 ⊔ l2)
  is-right-linear-combination-subset-Semiring =
    is-right-linear-combination-Semiring R
      ( additive-unital-magma-Semiring R)
      ( λ s → mul-Semiring R (inclusion-subset-Semiring R S s))
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
