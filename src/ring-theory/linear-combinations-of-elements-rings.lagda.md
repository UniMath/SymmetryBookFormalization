# Linear combinations with respect to rings

```agda
module ring-theory.linear-combinations-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import lists.lists

open import ring-theory.rings
open import ring-theory.subsets-rings

open import structured-types.magmas
```

</details>

## Idea

Consider a [ring](ring-theory.rings.md) $R$ and a type $A$. A {#concept "linear
combination"}} of elements of $A$ is a [list](lists.lists.md) of pairs $(r,a,s)$
consisting of an element $r,s:R$ and an element $a:A$.

Furthermore, if we are given an action $\mu : R \to A \to R \to M$ taking values
in a [unital magma](structured-types.magmas.md) $(M,+,0)$, then we can evaluate
a linear combination $((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1}))$ by
defining

$$
  ev((r_0,a_0,s_0),\ldots,(r_{n-1},a_{n-1},s_{n-1})) :=
  \sum_{i=0}^{n-1} \mu(r_i,a_i,s_i).
$$

To be explicit, linear combinations of elements of a type $A$ have the ring
coefficients on both sides.

## Definitions

### The type of linear combinations

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : UU l2)
  where

  linear-combination-Ring :
    UU (l1 ⊔ l2)
  linear-combination-Ring =
    list (type-Ring R × A × type-Ring R)
```

### Evaluating linear combinations of elements in unital magmas

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Ring R → type-Unital-Magma M)
  where

  ev-linear-combination-Ring :
    linear-combination-Ring R A → type-Unital-Magma M
  ev-linear-combination-Ring nil =
    unit-Unital-Magma M
  ev-linear-combination-Ring (cons (r , a , s) l) =
    mul-Unital-Magma M (μ r a s) (ev-linear-combination-Ring l)
```

### The predicate of being a linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Ring R → type-Unital-Magma M)
  where

  is-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-linear-combination-Ring =
    fiber (ev-linear-combination-Ring R M μ)
```

### The predicate of being a mere linear combination

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  {A : UU l2} (M : Unital-Magma l3)
  (μ : type-Ring R → A → type-Ring R → type-Unital-Magma M)
  where

  is-mere-linear-combination-prop-Ring :
    type-Unital-Magma M → Prop (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-prop-Ring x =
    trunc-Prop (is-linear-combination-Ring R M μ x)

  is-mere-linear-combination-Ring :
    type-Unital-Magma M → UU (l1 ⊔ l2 ⊔ l3)
  is-mere-linear-combination-Ring x =
    type-trunc-Prop (is-linear-combination-Ring R M μ x)

  is-prop-is-mere-linear-combination-Ring :
    (x : type-Unital-Magma M) →
    is-prop (is-mere-linear-combination-Ring x)
  is-prop-is-mere-linear-combination-Ring x =
    is-prop-type-trunc-Prop
```

### Linear combinations of subsets of a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  linear-combination-subset-Ring :
    UU (l1 ⊔ l2)
  linear-combination-subset-Ring =
    linear-combination-Ring R (type-subset-Ring R S)

  ev-linear-combination-subset-Ring :
    linear-combination-subset-Ring → type-Ring R
  ev-linear-combination-subset-Ring =
    ev-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ r s →
        mul-Ring R (mul-Ring R r (inclusion-subset-Ring R S s)))

  is-linear-combination-subset-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-linear-combination-subset-Ring =
    is-linear-combination-Ring R
      ( additive-unital-magma-Ring R)
      ( λ r s →
        mul-Ring R (mul-Ring R r (inclusion-subset-Ring R S s)))
```

### Linear combinations of families of elements in a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) {I : UU l2} (a : I → type-Ring R)
  where

  linear-combination-family-of-elements-Ring :
    UU (l1 ⊔ l2)
  linear-combination-family-of-elements-Ring =
    linear-combination-subset-Ring R (trunc-Prop ∘ fiber a)

  ev-linear-combination-family-of-elements-Ring :
    linear-combination-family-of-elements-Ring → type-Ring R
  ev-linear-combination-family-of-elements-Ring =
    ev-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)

  is-linear-combination-family-of-elements-Ring :
    type-Ring R → UU (l1 ⊔ l2)
  is-linear-combination-family-of-elements-Ring =
    is-linear-combination-subset-Ring R
      ( trunc-Prop ∘ fiber a)
```

### Linear combinations of a single element in a ring

Even though left linear combinations and right linear combinations of a single
element $a$ in a ring $R$ can always be written in the form $(r,a)$ or $(a,r)$,
resepectively, i.e., any element of the form $r_0a + \cdots + r_{n-1}a$ is equal
to an element of the form $ra$ and similar for right linear combinations, the
two-sided case is a bit different in that there might be rings in which an
element of the form

$$
  r_0as_0 + \cdots + r_{n-1}as_{n-1}
$$

is not equal to an element of the form $ras$, because the distributivity laws
don't apply in this more general case.

```agda
module _
  {l1 : Level} (R : Ring l1) (a : type-Ring R)
  where

  linear-combination-element-Ring :
    UU l1
  linear-combination-element-Ring =
    linear-combination-subset-Ring R (λ y → Id-Prop (set-Ring R) y a)

  ev-linear-combination-element-Ring :
    linear-combination-element-Ring → type-Ring R
  ev-linear-combination-element-Ring =
    ev-linear-combination-subset-Ring R
      ( λ y → Id-Prop (set-Ring R) y a)

  is-linear-combination-element-Ring :
    type-Ring R → UU l1
  is-linear-combination-element-Ring =
    is-linear-combination-subset-Ring R
      ( λ y → Id-Prop (set-Ring R) y a)
```
