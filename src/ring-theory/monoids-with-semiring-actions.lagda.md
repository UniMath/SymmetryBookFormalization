# Monoids with semiring actions

```agda
module ring-theory.monoids-with-semiring-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.semirings
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$.
A {{#concept "monoid with a left semiring action" Agda=Monoid-With-Left-Semiring-Action}}
from $R$ consists of a [monoid](group-theory.monoids.md) $M$ and a binary operation $\mu : R \to M \to M$ satisfying the axioms of a ring action:

1. The action distributes from the left over monoid multiplication:
   $$
     r(xy) = (rx)(ry).
   $$
2. The action distributes from the right over addition in the semiring:
   $$
     (r+s)x = (rx)(sx).
   $$
3. Associativity of the action
   $$
     (sr)x = s(rx).
   $$
4. The unit element of the semiring acts as the identity
   $$
     1x = x.
   $$
5. The unit element of the monoid absorbs any action
   $$
     r1 = 1.
   $$

## Definitions

### Left actions of semirings on monoids

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid l2)
  where

  left-action-semiring-Monoid : UU (l1 ⊔ l2)
  left-action-semiring-Monoid =
    Σ ( type-Semiring R → type-Monoid M → type-Monoid M)
      ( λ μ →
        ( (r : type-Semiring R) (x y : type-Monoid M) →
          μ r (mul-Monoid M x y) ＝ mul-Monoid M (μ r x) (μ r y)) ×
        ( (r s : type-Semiring R) (x : type-Monoid M) →
          μ (add-Semiring R r s) x ＝ mul-Monoid M (μ r x) (μ s x)) ×
        ( (s r : type-Semiring R) (x : type-Monoid M) →
          μ (mul-Semiring R s r) x ＝ μ s (μ r x)) ×
        ( (x : type-Monoid M) → μ (one-Semiring R) x ＝ x) ×
        ( (r : type-Semiring R) → μ r (unit-Monoid M) ＝ unit-Monoid M))
```

### Monoids with left semiring actions

```agda
Monoid-With-Left-Semiring-Action :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
Monoid-With-Left-Semiring-Action l2 R =
  Σ ( Monoid l2) (left-action-semiring-Monoid R)

module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid-With-Left-Semiring-Action l2 R)
  where

  monoid-Monoid-With-Left-Semiring-Action :
    Monoid l2
  monoid-Monoid-With-Left-Semiring-Action =
    pr1 M

  set-Monoid-With-Left-Semiring-Action :
    Set l2
  set-Monoid-With-Left-Semiring-Action =
    set-Monoid monoid-Monoid-With-Left-Semiring-Action

  type-Monoid-With-Left-Semiring-Action :
    UU l2
  type-Monoid-With-Left-Semiring-Action =
    type-Monoid monoid-Monoid-With-Left-Semiring-Action

  is-set-type-Monoid-With-Left-Semiring-Action :
    is-set type-Monoid-With-Left-Semiring-Action
  is-set-type-Monoid-With-Left-Semiring-Action =
    is-set-type-Monoid monoid-Monoid-With-Left-Semiring-Action

  mul-Monoid-With-Left-Semiring-Action :
    (x y : type-Monoid-With-Left-Semiring-Action) → type-Monoid-With-Left-Semiring-Action
  mul-Monoid-With-Left-Semiring-Action =
    mul-Monoid monoid-Monoid-With-Left-Semiring-Action

  associative-mul-Monoid-With-Left-Semiring-Action :
    (x y z : type-Monoid-With-Left-Semiring-Action) →
    mul-Monoid-With-Left-Semiring-Action (mul-Monoid-With-Left-Semiring-Action x y) z ＝
    mul-Monoid-With-Left-Semiring-Action x (mul-Monoid-With-Left-Semiring-Action y z)
  associative-mul-Monoid-With-Left-Semiring-Action =
    associative-mul-Monoid monoid-Monoid-With-Left-Semiring-Action

  unit-Monoid-With-Left-Semiring-Action :
    type-Monoid-With-Left-Semiring-Action
  unit-Monoid-With-Left-Semiring-Action =
    unit-Monoid monoid-Monoid-With-Left-Semiring-Action

  left-unit-law-mul-Monoid-With-Left-Semiring-Action :
    (x : type-Monoid-With-Left-Semiring-Action) →
    mul-Monoid-With-Left-Semiring-Action
      ( unit-Monoid-With-Left-Semiring-Action)
      ( x) ＝
    x
  left-unit-law-mul-Monoid-With-Left-Semiring-Action =
    left-unit-law-mul-Monoid monoid-Monoid-With-Left-Semiring-Action

  right-unit-law-mul-Monoid-With-Left-Semiring-Action :
    (x : type-Monoid-With-Left-Semiring-Action) →
    mul-Monoid-With-Left-Semiring-Action
      ( x)
      ( unit-Monoid-With-Left-Semiring-Action) ＝
    ( x)
  right-unit-law-mul-Monoid-With-Left-Semiring-Action =
    right-unit-law-mul-Monoid monoid-Monoid-With-Left-Semiring-Action

  action-Monoid-With-Left-Semiring-Action :
    type-Semiring R → type-Monoid-With-Left-Semiring-Action →
    type-Monoid-With-Left-Semiring-Action
  action-Monoid-With-Left-Semiring-Action =
    pr1 (pr2 M)

  left-distributive-action-mul-Monoid-With-Left-Semiring-Action :
    (r : type-Semiring R) (x y : type-Monoid-With-Left-Semiring-Action) →
    action-Monoid-With-Left-Semiring-Action r
      ( mul-Monoid-With-Left-Semiring-Action x y) ＝
    mul-Monoid-With-Left-Semiring-Action
      ( action-Monoid-With-Left-Semiring-Action r x)
      ( action-Monoid-With-Left-Semiring-Action r y)
  left-distributive-action-mul-Monoid-With-Left-Semiring-Action =
    pr1 (pr2 (pr2 M))

  right-distributive-action-add-Monoid-With-Left-Semiring-Action :
    (r s : type-Semiring R) (x : type-Monoid-With-Left-Semiring-Action) →
    action-Monoid-With-Left-Semiring-Action (add-Semiring R r s) x ＝
    mul-Monoid-With-Left-Semiring-Action
      ( action-Monoid-With-Left-Semiring-Action r x)
      ( action-Monoid-With-Left-Semiring-Action s x)
  right-distributive-action-add-Monoid-With-Left-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 M)))

  associative-action-Monoid-With-Left-Semiring-Action :
    (s r : type-Semiring R) (x : type-Monoid-With-Left-Semiring-Action) →
    action-Monoid-With-Left-Semiring-Action (mul-Semiring R s r) x ＝
    action-Monoid-With-Left-Semiring-Action s
      ( action-Monoid-With-Left-Semiring-Action r x)
  associative-action-Monoid-With-Left-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 M))))

  left-unit-law-action-Monoid-With-Left-Semiring-Action :
    (x : type-Monoid-With-Left-Semiring-Action) →
    action-Monoid-With-Left-Semiring-Action (one-Semiring R) x ＝ x
  left-unit-law-action-Monoid-With-Left-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))

  right-absorption-law-action-Monoid-With-Left-Semiring-Action :
    (r : type-Semiring R) →
    action-Monoid-With-Left-Semiring-Action r
      ( unit-Monoid-With-Left-Semiring-Action) ＝
    unit-Monoid-With-Left-Semiring-Action
  right-absorption-law-action-Monoid-With-Left-Semiring-Action =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))
```

## Properties

### The underlying additive monoid of a semiring is a monoid with a left semiring action

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  additive-monoid-with-left-semiring-action-Semiring :
    Monoid-With-Left-Semiring-Action l1 R
  additive-monoid-with-left-semiring-action-Semiring =
    ( additive-monoid-Semiring R ,
      mul-Semiring R ,
      left-distributive-mul-add-Semiring R ,
      right-distributive-mul-add-Semiring R ,
      associative-mul-Semiring R ,
      left-unit-law-mul-Semiring R ,
      right-zero-law-mul-Semiring R)
```
