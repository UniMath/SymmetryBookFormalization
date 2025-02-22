# Left linear combinations with respect to rings

```agda
module ring-theory.left-linear-combinations-of-elements-rings where
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

open import ring-theory.rings
open import ring-theory.subsets-rings

open import lists.lists

open import structured-types.magmas
```

</details>

## Idea

Consider a [ring](ring-theory.rings.md) $R$ and a type $A$. A {#concept "left linear combination"}} of elements of $R$ is a [list](lists.lists.md) of pairs $(r,a)$ consisting of an element $r:R$ and an element $a:A$.

Furthermore, if we are given an action $\mu : R \to A \to M$ taking values in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate a left linear combination $((r_0,a_0),\ldots,(r_{n-1},a_{n-1}))$ by defining

$$
  ev((r_0,a_0),\ldots,(r_{n-1},a_{n-1})) := \sum_{i=0}^{n-1} \mu(r_i,a_i).
$$

To be explicit, left linear combinations of elements of a type $A$ have the ring coefficients on the left.


## Definitions

### The type of left linear combinations

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : UU l2)
  where

  left-linear-combination-Ring :
    UU (l1 ⊔ l2)
  left-linear-combination-Ring =
    list (type-Ring R × A)
```

### Evaluating left linear combinations of elements in unital magmas

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Unital-Magma M)
  where

  ev-left-linear-combination-Ring :
    left-linear-combination-Ring R A → type-Unital-Magma M
  ev-left-linear-combination-Ring nil =
    unit-Unital-Magma M
  ev-left-linear-combination-Ring (cons (r , a) l) =
    mul-Unital-Magma M (μ r a) (ev-left-linear-combination-Ring l)
```

### The predicate of being a left linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Unital-Magma M)
  where

  is-left-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-left-linear-combination-Ring =
    fiber (ev-left-linear-combination-Ring R M μ)
```

### The predicate of being a mere left linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Unital-Magma M)
  where

  is-mere-left-linear-combination-prop-Ring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-left-linear-combination-prop-Ring x =
    trunc-Prop (is-left-linear-combination-Ring R M μ x)

  is-mere-left-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-left-linear-combination-Ring x =
    type-trunc-Prop (is-left-linear-combination-Ring R M μ x)

  is-prop-is-mere-left-linear-combination-Ring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-left-linear-combination-Ring x)
  is-prop-is-mere-left-linear-combination-Ring x =
    is-prop-type-trunc-Prop
```

### Left linear combinations of subsets of a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  left-linear-combination-subset-Ring :
    UU (l1 ⊔ l2)
  left-linear-combination-subset-Ring =
    left-linear-combination-Ring R (type-subset-Ring R S)

  ev-left-linear-combination-subset-Ring :
    left-linear-combination-subset-Ring → type-Ring R
  ev-left-linear-combination-subset-Ring =
    ev-left-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ r s → mul-Ring R r (inclusion-subset-Ring R S s))

  is-left-linear-combination-subset-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-left-linear-combination-subset-Ring =
    is-left-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ r s → mul-Ring R r (inclusion-subset-Ring R S s))
```

### Left linear combinations of families of elements in a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) {I : UU l2} (a : I → type-Ring R)
  where

  left-linear-combination-family-of-elements-Ring :
    UU (l1 ⊔ l2)
  left-linear-combination-family-of-elements-Ring =
    left-linear-combination-subset-Ring R (trunc-Prop ∘ fiber a)

  ev-left-linear-combination-family-of-elements-Ring :
    left-linear-combination-family-of-elements-Ring → type-Ring R
  ev-left-linear-combination-family-of-elements-Ring =
    ev-left-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)

  is-left-linear-combination-family-of-elements-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-left-linear-combination-family-of-elements-Ring =
    is-left-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)
```
