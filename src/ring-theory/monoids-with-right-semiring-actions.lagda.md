# Monoids with right semiring actions

```agda
module ring-theory.monoids-with-right-semiring-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.semirings
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$. A
{{#concept "monoid with a right semiring action" Agda=Monoid-With-Right-Semiring-Action}}
from $R$ consists of a [monoid](group-theory.monoids.md) $M$ and a binary
operation $\mu : R \to M \to M$ satisfying the axioms of a ring action:

1. The action distributes from the right over monoid multiplication:
   $$
     (xy)^r = (x^r)(y^r).
   $$
2. The action distributes from the right over addition in the semiring:
   $$
     x^{r+s} = (x^r)(x^s).
   $$
3. Associativity of the action
   $$
     x^{rs} = (x^r)^s.
   $$
4. The unit element of the semiring acts as the identity
   $$
     x^1 = x.
   $$
5. The unit element of the monoid absorbs any action
   $$
     1^r = 1.
   $$

## Definitions

### Right actions of semirings on monoids

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid l2)
  where

  right-action-semiring-Monoid : UU (l1 ⊔ l2)
  right-action-semiring-Monoid =
    Σ ( type-Monoid M → type-Semiring R → type-Monoid M)
      ( λ μ →
        ( (x y : type-Monoid M) (r : type-Semiring R) →
          μ (mul-Monoid M x y) r ＝ mul-Monoid M (μ x r) (μ y r)) ×
        ( (x : type-Monoid M) (r s : type-Semiring R) →
          μ x (add-Semiring R r s) ＝ mul-Monoid M (μ x r) (μ x s)) ×
        ( (x : type-Monoid M) (r s : type-Semiring R) →
          μ x (mul-Semiring R r s) ＝ μ (μ x r) s) ×
        ( (x : type-Monoid M) → μ x (one-Semiring R) ＝ x) ×
        ( (r : type-Semiring R) → μ (unit-Monoid M) r ＝ unit-Monoid M))
```

### Monoids with right semiring actions

```agda
Monoid-With-Right-Semiring-Action :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
Monoid-With-Right-Semiring-Action l2 R =
  Σ ( Monoid l2) (right-action-semiring-Monoid R)

module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid-With-Right-Semiring-Action l2 R)
  where

  monoid-Monoid-With-Right-Semiring-Action :
    Monoid l2
  monoid-Monoid-With-Right-Semiring-Action =
    pr1 M

  set-Monoid-With-Right-Semiring-Action :
    Set l2
  set-Monoid-With-Right-Semiring-Action =
    set-Monoid monoid-Monoid-With-Right-Semiring-Action

  type-Monoid-With-Right-Semiring-Action :
    UU l2
  type-Monoid-With-Right-Semiring-Action =
    type-Monoid monoid-Monoid-With-Right-Semiring-Action

  is-set-type-Monoid-With-Right-Semiring-Action :
    is-set type-Monoid-With-Right-Semiring-Action
  is-set-type-Monoid-With-Right-Semiring-Action =
    is-set-type-Monoid monoid-Monoid-With-Right-Semiring-Action

  mul-Monoid-With-Right-Semiring-Action :
    (x y : type-Monoid-With-Right-Semiring-Action) →
    type-Monoid-With-Right-Semiring-Action
  mul-Monoid-With-Right-Semiring-Action =
    mul-Monoid monoid-Monoid-With-Right-Semiring-Action

  associative-mul-Monoid-With-Right-Semiring-Action :
    (x y z : type-Monoid-With-Right-Semiring-Action) →
    mul-Monoid-With-Right-Semiring-Action
      ( mul-Monoid-With-Right-Semiring-Action x y)
      ( z) ＝
    mul-Monoid-With-Right-Semiring-Action
      ( x)
      ( mul-Monoid-With-Right-Semiring-Action y z)
  associative-mul-Monoid-With-Right-Semiring-Action =
    associative-mul-Monoid monoid-Monoid-With-Right-Semiring-Action

  unit-Monoid-With-Right-Semiring-Action :
    type-Monoid-With-Right-Semiring-Action
  unit-Monoid-With-Right-Semiring-Action =
    unit-Monoid monoid-Monoid-With-Right-Semiring-Action

  left-unit-law-mul-Monoid-With-Right-Semiring-Action :
    (x : type-Monoid-With-Right-Semiring-Action) →
    mul-Monoid-With-Right-Semiring-Action
      ( unit-Monoid-With-Right-Semiring-Action)
      ( x) ＝
    x
  left-unit-law-mul-Monoid-With-Right-Semiring-Action =
    left-unit-law-mul-Monoid monoid-Monoid-With-Right-Semiring-Action

  right-unit-law-mul-Monoid-With-Right-Semiring-Action :
    (x : type-Monoid-With-Right-Semiring-Action) →
    mul-Monoid-With-Right-Semiring-Action
      ( x)
      ( unit-Monoid-With-Right-Semiring-Action) ＝
    ( x)
  right-unit-law-mul-Monoid-With-Right-Semiring-Action =
    right-unit-law-mul-Monoid monoid-Monoid-With-Right-Semiring-Action

  action-Monoid-With-Right-Semiring-Action :
    type-Monoid-With-Right-Semiring-Action → type-Semiring R →
    type-Monoid-With-Right-Semiring-Action
  action-Monoid-With-Right-Semiring-Action =
    pr1 (pr2 M)

  right-distributive-action-mul-Monoid-With-Right-Semiring-Action :
    (x y : type-Monoid-With-Right-Semiring-Action) (r : type-Semiring R) →
    action-Monoid-With-Right-Semiring-Action
      ( mul-Monoid-With-Right-Semiring-Action x y)
      ( r) ＝
    mul-Monoid-With-Right-Semiring-Action
      ( action-Monoid-With-Right-Semiring-Action x r)
      ( action-Monoid-With-Right-Semiring-Action y r)
  right-distributive-action-mul-Monoid-With-Right-Semiring-Action =
    pr1 (pr2 (pr2 M))

  right-distributive-action-add-Monoid-With-Right-Semiring-Action :
    (x : type-Monoid-With-Right-Semiring-Action) (r s : type-Semiring R) →
    action-Monoid-With-Right-Semiring-Action x (add-Semiring R r s) ＝
    mul-Monoid-With-Right-Semiring-Action
      ( action-Monoid-With-Right-Semiring-Action x r)
      ( action-Monoid-With-Right-Semiring-Action x s)
  right-distributive-action-add-Monoid-With-Right-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 M)))

  associative-action-Monoid-With-Right-Semiring-Action :
    (x : type-Monoid-With-Right-Semiring-Action) (r s : type-Semiring R) →
    action-Monoid-With-Right-Semiring-Action x (mul-Semiring R r s) ＝
    action-Monoid-With-Right-Semiring-Action
      ( action-Monoid-With-Right-Semiring-Action x r)
      ( s)
  associative-action-Monoid-With-Right-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 M))))

  right-unit-law-action-Monoid-With-Right-Semiring-Action :
    (x : type-Monoid-With-Right-Semiring-Action) →
    action-Monoid-With-Right-Semiring-Action x (one-Semiring R) ＝ x
  right-unit-law-action-Monoid-With-Right-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))

  right-absorption-law-action-Monoid-With-Right-Semiring-Action :
    (r : type-Semiring R) →
    action-Monoid-With-Right-Semiring-Action
      ( unit-Monoid-With-Right-Semiring-Action)
      ( r) ＝
    unit-Monoid-With-Right-Semiring-Action
  right-absorption-law-action-Monoid-With-Right-Semiring-Action =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))
```

## Properties

### The underlying additive monoid of a semiring is a monoid with a right semiring action

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  additive-monoid-with-right-semiring-action-Semiring :
    Monoid-With-Right-Semiring-Action l1 R
  additive-monoid-with-right-semiring-action-Semiring =
    ( ( additive-monoid-Semiring R) ,
      ( mul-Semiring R) ,
      ( right-distributive-mul-add-Semiring R) ,
      ( left-distributive-mul-add-Semiring R) ,
      ( λ x y z → inv (associative-mul-Semiring R x y z)) ,
      ( right-unit-law-mul-Semiring R) ,
      ( left-zero-law-mul-Semiring R))
```
