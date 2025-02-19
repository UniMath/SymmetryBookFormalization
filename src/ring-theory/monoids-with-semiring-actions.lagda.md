# Monoids with semiring actions

```agda
module ring-theory.monoids-with-semiring-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
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

Consider a [semiring](ring-theory.semirings.md) $R$. A
{{#concept "monoid with a semiring action" Agda=Monoid-With-Semiring-Action}}
from $R$ consists of a [monoid](group-theory.monoids.md) $M$ and a binary
operation $\mu : R \to M \to M$ satisfying the axioms of a ring action:

1. The action distributes from the left over monoid multiplication:
   $$
     {}^r(xy)^s = ({}^rx^s)({}^ry^s).
   $$
2. The action distributes from the right over addition in the semiring:
   $$
     {}^{r+s}x^{t} = ({}^rx^t)({}^sx^t).
   $$
3. The action distributes from the left over addition in the semiring:
   $$
     {}^rx^{s+t} = ({}^rx^s)({}^rx^t).
   $$
4. Associativity of the action
   $$
     {}^{sr}x^{tu} = {}^s({}^rx^t)^u.
   $$
5. The unit element of the semiring acts as the identity
   $$
     {}^1x^1 = x.
   $$
6. The unit element of the monoid absorbs any action
   $$
     {}^r1^s = 1.
   $$

## Definitions

### Actions of semirings on monoids

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid l2)
  where

  action-semiring-Monoid : UU (l1 ⊔ l2)
  action-semiring-Monoid =
    Σ ( type-Semiring R → type-Monoid M → type-Semiring R → type-Monoid M)
      ( λ μ →
        ( (r : type-Semiring R) (x y : type-Monoid M) (s : type-Semiring R) →
          μ r (mul-Monoid M x y) s ＝ mul-Monoid M (μ r x s) (μ r y s)) ×
        ( (r s : type-Semiring R) (x : type-Monoid M) (t : type-Semiring R) →
          μ (add-Semiring R r s) x t ＝ mul-Monoid M (μ r x t) (μ s x t)) ×
        ( (r : type-Semiring R) (x : type-Monoid M) (s t : type-Semiring R) →
          μ r x (add-Semiring R s t) ＝ mul-Monoid M (μ r x s) (μ r x t)) ×
        ( (s r : type-Semiring R) (x : type-Monoid M) (t u : type-Semiring R) →
          μ (mul-Semiring R s r) x (mul-Semiring R t u) ＝ μ s (μ r x t) u) ×
        ( (x : type-Monoid M) → μ (one-Semiring R) x (one-Semiring R) ＝ x) ×
        ( (r s : type-Semiring R) → μ r (unit-Monoid M) s ＝ unit-Monoid M))
```

### Monoids with semiring actions

```agda
Monoid-With-Semiring-Action :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
Monoid-With-Semiring-Action l2 R =
  Σ ( Monoid l2) (action-semiring-Monoid R)

module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid-With-Semiring-Action l2 R)
  where

  monoid-Monoid-With-Semiring-Action :
    Monoid l2
  monoid-Monoid-With-Semiring-Action =
    pr1 M

  set-Monoid-With-Semiring-Action :
    Set l2
  set-Monoid-With-Semiring-Action =
    set-Monoid monoid-Monoid-With-Semiring-Action

  type-Monoid-With-Semiring-Action :
    UU l2
  type-Monoid-With-Semiring-Action =
    type-Monoid monoid-Monoid-With-Semiring-Action

  is-set-type-Monoid-With-Semiring-Action :
    is-set type-Monoid-With-Semiring-Action
  is-set-type-Monoid-With-Semiring-Action =
    is-set-type-Monoid monoid-Monoid-With-Semiring-Action

  mul-Monoid-With-Semiring-Action :
    (x y : type-Monoid-With-Semiring-Action) →
    type-Monoid-With-Semiring-Action
  mul-Monoid-With-Semiring-Action =
    mul-Monoid monoid-Monoid-With-Semiring-Action

  associative-mul-Monoid-With-Semiring-Action :
    (x y z : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action
      ( mul-Monoid-With-Semiring-Action x y)
      ( z) ＝
    mul-Monoid-With-Semiring-Action
      ( x)
      ( mul-Monoid-With-Semiring-Action y z)
  associative-mul-Monoid-With-Semiring-Action =
    associative-mul-Monoid monoid-Monoid-With-Semiring-Action

  unit-Monoid-With-Semiring-Action :
    type-Monoid-With-Semiring-Action
  unit-Monoid-With-Semiring-Action =
    unit-Monoid monoid-Monoid-With-Semiring-Action

  left-unit-law-mul-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action
      ( unit-Monoid-With-Semiring-Action)
      ( x) ＝
    x
  left-unit-law-mul-Monoid-With-Semiring-Action =
    left-unit-law-mul-Monoid monoid-Monoid-With-Semiring-Action

  right-unit-law-mul-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action
      ( x)
      ( unit-Monoid-With-Semiring-Action) ＝
    ( x)
  right-unit-law-mul-Monoid-With-Semiring-Action =
    right-unit-law-mul-Monoid monoid-Monoid-With-Semiring-Action

  action-Monoid-With-Semiring-Action :
    type-Semiring R → type-Monoid-With-Semiring-Action → type-Semiring R →
    type-Monoid-With-Semiring-Action
  action-Monoid-With-Semiring-Action =
    pr1 (pr2 M)

  inner-distributive-action-mul-Monoid-With-Semiring-Action :
    (r : type-Semiring R) (x y : type-Monoid-With-Semiring-Action)
    (s : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( r)
      ( mul-Monoid-With-Semiring-Action x y)
      ( s) ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x s)
      ( action-Monoid-With-Semiring-Action r y s)
  inner-distributive-action-mul-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 M))

  right-distributive-action-add-Monoid-With-Semiring-Action :
    (r s : type-Semiring R) (x : type-Monoid-With-Semiring-Action)
    (t : type-Semiring R) →
    action-Monoid-With-Semiring-Action (add-Semiring R r s) x t ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x t)
      ( action-Monoid-With-Semiring-Action s x t)
  right-distributive-action-add-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 M)))

  left-distributive-action-add-Monoid-With-Semiring-Action :
    (r : type-Semiring R) (x : type-Monoid-With-Semiring-Action)
    (s t : type-Semiring R) →
    action-Monoid-With-Semiring-Action r x (add-Semiring R s t) ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x s)
      ( action-Monoid-With-Semiring-Action r x t)
  left-distributive-action-add-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 M))))

  associative-action-Monoid-With-Semiring-Action :
    (s r : type-Semiring R)
    (x : type-Monoid-With-Semiring-Action)
    (t u : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( mul-Semiring R s r)
      ( x)
      ( mul-Semiring R t u) ＝
    action-Monoid-With-Semiring-Action
      ( s)
      ( action-Monoid-With-Semiring-Action r x t)
      ( u)
  associative-action-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))

  unit-law-action-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    action-Monoid-With-Semiring-Action (one-Semiring R) x (one-Semiring R) ＝ x
  unit-law-action-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))

  absorption-law-action-Monoid-With-Semiring-Action :
    (r s : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( r)
      ( unit-Monoid-With-Semiring-Action)
      ( s) ＝
    unit-Monoid-With-Semiring-Action
  absorption-law-action-Monoid-With-Semiring-Action =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))
```

## Properties

### The underlying additive monoid of a semiring is a monoid with a semiring action

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  action-additive-monoid-with-semiring-action-Semiring :
    (r x s : type-Semiring R) → type-Semiring R
  action-additive-monoid-with-semiring-action-Semiring r x s =
    mul-Semiring R (mul-Semiring R r x) s

  inner-distributive-action-additive-monoid-with-semiring-action-Semiring :
    (r x y s : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( r)
      ( add-Semiring R x y)
      ( s) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x s)
      ( action-additive-monoid-with-semiring-action-Semiring r y s)
  inner-distributive-action-additive-monoid-with-semiring-action-Semiring
    r x y s =
    ap
      ( λ t → mul-Semiring R t s)
      ( left-distributive-mul-add-Semiring R r x y) ∙
    right-distributive-mul-add-Semiring R
      ( mul-Semiring R r x)
      ( mul-Semiring R r y)
      ( s)

  right-distributive-action-mul-additive-monoid-with-semiring-action-Semiring :
    (r s x t : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( add-Semiring R r s)
      ( x)
      ( t) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x t)
      ( action-additive-monoid-with-semiring-action-Semiring s x t)
  right-distributive-action-mul-additive-monoid-with-semiring-action-Semiring
    r s x t =
    ap
      ( λ u → mul-Semiring R u t)
      ( right-distributive-mul-add-Semiring R r s x) ∙
    right-distributive-mul-add-Semiring R
      ( mul-Semiring R r x)
      ( mul-Semiring R s x)
      ( t)

  left-distributive-action-mul-additive-monoid-with-semiring-action-Semiring :
    (r x s t : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( r)
      ( x)
      ( add-Semiring R s t) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x s)
      ( action-additive-monoid-with-semiring-action-Semiring r x t)
  left-distributive-action-mul-additive-monoid-with-semiring-action-Semiring
    r x s t =
    left-distributive-mul-add-Semiring R (mul-Semiring R r x) s t

  associative-action-additive-monoid-with-semiring-action-Semiring :
    (s r x t u : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( mul-Semiring R s r)
      ( x)
      ( mul-Semiring R t u) ＝
    action-additive-monoid-with-semiring-action-Semiring
      ( s)
      ( action-additive-monoid-with-semiring-action-Semiring r x t)
      ( u)
  associative-action-additive-monoid-with-semiring-action-Semiring s r x t u =
    inv
      ( associative-mul-Semiring R
        ( mul-Semiring R (mul-Semiring R s r) x)
        ( t)
        ( u)) ∙
    ap
      ( λ v → mul-Semiring R v u)
      ( ap (λ v → mul-Semiring R v t) (associative-mul-Semiring R s r x) ∙
        associative-mul-Semiring R s (mul-Semiring R r x) t)

  unit-law-action-monoid-with-semiring-action-Semiring :
    (x : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( one-Semiring R)
      ( x)
      ( one-Semiring R) ＝
    x
  unit-law-action-monoid-with-semiring-action-Semiring x =
    right-unit-law-mul-Semiring R (mul-Semiring R (one-Semiring R) x) ∙
    left-unit-law-mul-Semiring R x

  absorption-law-action-monoid-with-semiring-action-Semiring :
    (r s : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( r)
      ( zero-Semiring R)
      ( s) ＝
    zero-Semiring R
  absorption-law-action-monoid-with-semiring-action-Semiring r s =
    ap (λ t → mul-Semiring R t s) (right-zero-law-mul-Semiring R r) ∙
    left-zero-law-mul-Semiring R s

  additive-monoid-with-semiring-action-Semiring :
    Monoid-With-Semiring-Action l1 R
  additive-monoid-with-semiring-action-Semiring =
    ( additive-monoid-Semiring R ,
      action-additive-monoid-with-semiring-action-Semiring ,
      inner-distributive-action-additive-monoid-with-semiring-action-Semiring ,
      right-distributive-action-mul-additive-monoid-with-semiring-action-Semiring ,
      left-distributive-action-mul-additive-monoid-with-semiring-action-Semiring ,
      associative-action-additive-monoid-with-semiring-action-Semiring ,
      unit-law-action-monoid-with-semiring-action-Semiring ,
      absorption-law-action-monoid-with-semiring-action-Semiring)
```
