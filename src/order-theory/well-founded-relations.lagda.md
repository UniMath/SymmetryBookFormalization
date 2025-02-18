# Well-founded relations

```agda
module order-theory.well-founded-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.accessible-elements-relations
open import order-theory.preorders
```

</details>

## Idea

Given a type `X` equipped with a
[binary relation](foundation.binary-relations.md) `_∈_ : X → X → Type` we say
that the relation `_∈_` is
{{#concept "well-founded" Disambiguation="binary relation" WDID=Q338021 WD="well-founded relation" Agda=is-well-founded-Relation Agda=Well-Founded-Relation}}
if all elements of `X` are
[accessible](order-theory.accessible-elements-relations.md) with respect to
`_∈_`.

Well-founded relations satisfy an induction principle: In order to construct an
element of `P x` for all `x : X` it suffices to construct an element of `P y`
for all elements `y ∈ x`. More precisely, the **well-founded induction
principle** is a function

```text
  (x : X) → ((y : X) → (y ∈ x) → P y) → P x.
```

## Definitions

### The predicate of being a well-founded relation

```agda
module _
  {l1 l2 : Level} {X : UU l1} (_∈_ : Relation l2 X)
  where

  is-well-founded-prop-Relation : Prop (l1 ⊔ l2)
  is-well-founded-prop-Relation =
    Π-Prop X (is-accessible-element-prop-Relation _∈_)

  is-well-founded-Relation : UU (l1 ⊔ l2)
  is-well-founded-Relation = (x : X) → is-accessible-element-Relation _∈_ x
```

### Well-founded relations

```agda
Well-Founded-Relation : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Well-Founded-Relation l X = Σ (Relation l X) is-well-founded-Relation

module _
  {l1 l2 : Level} {X : UU l1} (R : Well-Founded-Relation l2 X)
  where

  rel-Well-Founded-Relation : Relation l2 X
  rel-Well-Founded-Relation = pr1 R

  is-well-founded-Well-Founded-Relation :
    is-well-founded-Relation rel-Well-Founded-Relation
  is-well-founded-Well-Founded-Relation = pr2 R
```

### Well-founded induction

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} ((_∈_ , w) : Well-Founded-Relation l2 X)
  (P : X → UU l3)
  where

  ind-Well-Founded-Relation :
    ({x : X} → ({y : X} → y ∈ x → P y) → P x) → (x : X) → P x
  ind-Well-Founded-Relation IH x =
    ind-accessible-element-Relation _∈_ P (λ _ → IH) (w x)
```

## Properties

### A well-founded relation is asymmetric, and thus irreflexive

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R@(_∈_ , w) : Well-Founded-Relation l2 X)
  where

  is-asymmetric-le-Well-Founded-Relation : is-asymmetric _∈_
  is-asymmetric-le-Well-Founded-Relation x y =
    is-asymmetric-is-accessible-element-Relation _∈_ (w x)

  is-irreflexive-le-Well-Founded-Relation : is-irreflexive _∈_
  is-irreflexive-le-Well-Founded-Relation =
    is-irreflexive-is-asymmetric _∈_ is-asymmetric-le-Well-Founded-Relation
```

### The associated reflexive relation of a well-founded relation

Given a well-founded relation $∈$ on $X$ there is an associated reflexive
relation given by

$$
  (x ≤ y) := (u : X) → (u ∈ x) → (u ∈ y).
$$

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R@(_∈_ , w) : Well-Founded-Relation l2 X)
  where

  leq-Well-Founded-Relation : Relation (l1 ⊔ l2) X
  leq-Well-Founded-Relation x y = (u : X) → u ∈ x → u ∈ y

  refl-leq-Well-Founded-Relation : is-reflexive leq-Well-Founded-Relation
  refl-leq-Well-Founded-Relation x u = id

  leq-eq-Well-Founded-Relation :
    {x y : X} → x ＝ y → leq-Well-Founded-Relation x y
  leq-eq-Well-Founded-Relation {x} refl = refl-leq-Well-Founded-Relation x

  transitive-leq-Well-Founded-Relation : is-transitive leq-Well-Founded-Relation
  transitive-leq-Well-Founded-Relation x y z f g t H = f t (g t H)
```

## See also

- A well-founded relation that is transitive is a
  [transitive well-founded relation](order-theory.transitive-well-founded-relations.md).
