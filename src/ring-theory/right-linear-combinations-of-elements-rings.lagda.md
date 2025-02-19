# Right linear combinations with respect to rings

```agda
module ring-theory.right-linear-combinations-of-elements-rings where
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

open import lists.lists

open import ring-theory.rings
open import ring-theory.subsets-rings

open import structured-types.magmas
```

</details>

## Idea

Consider a [ring](ring-theory.rings.md) $R$ and a type $A$. A {#concept "right
linear combination"}} of elements of $R$ is a [list](lists.lists.md) of pairs
$(a,r)$ consisting of an element $a:A$ and an element $r:R$.

Furthermore, if we are given an action $\mu : A \to R \to M$ taking values in a
[unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a
right linear combination $((a_0,r_0),\ldots,(a_{n-1},r_{n-1}))$ by defining

$$
  ev((a_0,r_0),\ldots,(a_{n-1},r_{n-1})) := \sum_{i=0}^{n-1} \mu(a_i,r_i).
$$

To be explicit, right linear combinations of elements of a type $A$ have the
ring coefficients on the right.

## Definitions

### The type of right linear combinations

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : UU l2)
  where

  right-linear-combination-Ring :
    UU (l1 ⊔ l2)
  right-linear-combination-Ring =
    list (A × type-Ring R)
```

### Evaluating right linear combinations of elements in unital magmas

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Ring R → type-Unital-Magma M)
  where

  ev-right-linear-combination-Ring :
    right-linear-combination-Ring R A → type-Unital-Magma M
  ev-right-linear-combination-Ring nil =
    unit-Unital-Magma M
  ev-right-linear-combination-Ring (cons (a , r) l) =
    mul-Unital-Magma M (μ a r) (ev-right-linear-combination-Ring l)
```

### The predicate of being a right linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Ring R → type-Unital-Magma M)
  where

  is-right-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-right-linear-combination-Ring =
    fiber (ev-right-linear-combination-Ring R M μ)
```

### The predicate of being a mere right linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : A → type-Ring R → type-Unital-Magma M)
  where

  is-mere-right-linear-combination-prop-Ring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-right-linear-combination-prop-Ring x =
    trunc-Prop (is-right-linear-combination-Ring R M μ x)

  is-mere-right-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-right-linear-combination-Ring x =
    type-trunc-Prop (is-right-linear-combination-Ring R M μ x)

  is-prop-is-mere-right-linear-combination-Ring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-right-linear-combination-Ring x)
  is-prop-is-mere-right-linear-combination-Ring x =
    is-prop-type-trunc-Prop
```

### Right linear combinations of subsets of a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  right-linear-combination-subset-Ring :
    UU (l1 ⊔ l2)
  right-linear-combination-subset-Ring =
    right-linear-combination-Ring R (type-subset-Ring R S)

  ev-right-linear-combination-subset-Ring :
    right-linear-combination-subset-Ring → type-Ring R
  ev-right-linear-combination-subset-Ring =
    ev-right-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ s → mul-Ring R (inclusion-subset-Ring R S s))

  is-right-linear-combination-subset-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-right-linear-combination-subset-Ring =
    is-right-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ s → mul-Ring R (inclusion-subset-Ring R S s))
```

### Right linear combinations of families of elements in a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) {I : UU l2} (a : I → type-Ring R)
  where

  right-linear-combination-family-of-elements-Ring :
    UU (l1 ⊔ l2)
  right-linear-combination-family-of-elements-Ring =
    right-linear-combination-subset-Ring R (trunc-Prop ∘ fiber a)

  ev-right-linear-combination-family-of-elements-Ring :
    right-linear-combination-family-of-elements-Ring → type-Ring R
  ev-right-linear-combination-family-of-elements-Ring =
    ev-right-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)

  is-right-linear-combination-family-of-elements-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-right-linear-combination-family-of-elements-Ring =
    is-right-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)
```
