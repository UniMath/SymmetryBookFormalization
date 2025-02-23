# Metric spaces

## Idea

Metric spaces are types [structured](foundation.structure.md) with a concept of
distance on its elements.

Since we operate in a constructive setting, the concept of distance is captured
by considering upper bounds on the distance between points, rather than by a
distance function as in the classical approach. Thus, a metric space `A` is
defined by a family of _neighborhood_
[relations](foundation.binary-relations.md) on it indexed by the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`ℚ⁺`,

```text
  N : ℚ⁺ → A → A → Prop l
```

that satisfies certain axioms. Constructing a proof of `N d x y` amounts to
saying that _`d` is an upper bound on the distance from `x` to `y`_.

The neighborhood relation on a metric space must satisfy the following axioms:

- **Reflexivity.** Every positive rational `d` is an upper bound on the distance
  from `x` to itself.
- **Symmetry.** If `d` is an upper bound on the distance from `x` to `y`, then
  `d` is an upper bound on the distance from `y` to `x`.
- **Triangularity.** If `d` is an upper bound on the distance from `x` to `y`,
  and `d'` is an upper bound on the distance from `y` to `z`, then `d + d'` is
  an upper bound on the distance from `x` to `z`.

Finally, we ask that our metric spaces are **extensional**, which amounts to the
property of **indistinguishability of identicals**

- If every positive rational `d` is an upper bound on the distance from `x` to
  `y`, then `x` and `y` are [equal](foundation-core.identity-types.md).

## Instances of metric spaces

{{#include tables/metric-spaces.md}}

## Modules in the metric spaces namespace

```agda
module metric-spaces where

open import metric-spaces.category-of-metric-spaces-and-isometries public
open import metric-spaces.category-of-metric-spaces-and-short-functions public
open import metric-spaces.cauchy-approximations-metric-spaces public
open import metric-spaces.cauchy-approximations-premetric-spaces public
open import metric-spaces.cauchy-sequences-complete-metric-spaces public
open import metric-spaces.cauchy-sequences-metric-spaces public
open import metric-spaces.closed-premetric-structures public
open import metric-spaces.complete-metric-spaces public
open import metric-spaces.convergent-cauchy-approximations-metric-spaces public
open import metric-spaces.dependent-products-metric-spaces public
open import metric-spaces.discrete-premetric-structures public
open import metric-spaces.equality-of-metric-spaces public
open import metric-spaces.equality-of-premetric-spaces public
open import metric-spaces.extensional-premetric-structures public
open import metric-spaces.functions-metric-spaces public
open import metric-spaces.functor-category-set-functions-isometry-metric-spaces public
open import metric-spaces.functor-category-short-isometry-metric-spaces public
open import metric-spaces.induced-premetric-structures-on-preimages public
open import metric-spaces.isometric-equivalences-premetric-spaces public
open import metric-spaces.isometries-metric-spaces public
open import metric-spaces.isometries-premetric-spaces public
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces public
open import metric-spaces.metric-space-of-cauchy-approximations-in-a-metric-space public
open import metric-spaces.metric-space-of-convergent-cauchy-approximations-in-a-metric-space public
open import metric-spaces.metric-space-of-rational-numbers public
open import metric-spaces.metric-space-of-rational-numbers-with-open-neighborhoods public
open import metric-spaces.metric-spaces public
open import metric-spaces.metric-structures public
open import metric-spaces.monotonic-premetric-structures public
open import metric-spaces.ordering-premetric-structures public
open import metric-spaces.precategory-of-metric-spaces-and-functions public
open import metric-spaces.precategory-of-metric-spaces-and-isometries public
open import metric-spaces.precategory-of-metric-spaces-and-short-functions public
open import metric-spaces.premetric-spaces public
open import metric-spaces.premetric-structures public
open import metric-spaces.pseudometric-spaces public
open import metric-spaces.pseudometric-structures public
open import metric-spaces.reflexive-premetric-structures public
open import metric-spaces.saturated-metric-spaces public
open import metric-spaces.short-functions-metric-spaces public
open import metric-spaces.short-functions-premetric-spaces public
open import metric-spaces.subspaces-metric-spaces public
open import metric-spaces.symmetric-premetric-structures public
open import metric-spaces.triangular-premetric-structures public
```

## References

Our setup for metric space theory closely follows {{#cite Booij20PhD}}.

{{#bibliography}} {{#reference Booij20PhD}}
