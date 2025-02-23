# Cauchy sequences in complete metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-complete-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-sequences-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [Cauchy sequence](metric-spaces.cauchy-sequences-metric-spaces.md) in a
[complete metric space](metric-spaces.complete-metric-spaces.md) is a Cauchy
sequence in the underlying metric space, and always has a limit.

## Definition

```agda
module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  where

  cauchy-sequence-Complete-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequence-Complete-Metric-Space =
    cauchy-sequence-Metric-Space (metric-space-Complete-Metric-Space M)

  is-limit-cauchy-sequence-Complete-Metric-Space :
    cauchy-sequence-Complete-Metric-Space →
    type-Complete-Metric-Space M →
    UU l2
  is-limit-cauchy-sequence-Complete-Metric-Space x l =
    is-limit-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Space M)
      ( x)
      ( l)
```

## Properties

### Every Cauchy sequence in a complete metric space has a limit

```agda
module _
  {l1 l2 : Level} (M : Complete-Metric-Space l1 l2)
  (x : cauchy-sequence-Complete-Metric-Space M)
  where

  limit-cauchy-sequence-Complete-Metric-Space : type-Complete-Metric-Space M
  limit-cauchy-sequence-Complete-Metric-Space =
    pr1
      ( is-complete-metric-space-Complete-Metric-Space
        ( M)
        ( cauchy-approximation-cauchy-sequence-Metric-Space
          ( metric-space-Complete-Metric-Space M)
          ( x)))

  is-limit-limit-cauchy-sequence-Complete-Metric-Space :
    is-limit-cauchy-sequence-Complete-Metric-Space
      ( M)
      ( x)
      ( limit-cauchy-sequence-Complete-Metric-Space)
  is-limit-limit-cauchy-sequence-Complete-Metric-Space =
    is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Space M)
      ( x)
      ( limit-cauchy-sequence-Complete-Metric-Space)
      ( pr2
        ( is-complete-metric-space-Complete-Metric-Space
          ( M)
          ( cauchy-approximation-cauchy-sequence-Metric-Space
            ( metric-space-Complete-Metric-Space M)
            ( x))))

  has-limit-cauchy-sequence-Complete-Metric-Space :
    has-limit-cauchy-sequence-Metric-Space
      ( metric-space-Complete-Metric-Space M)
      ( x)
  has-limit-cauchy-sequence-Complete-Metric-Space =
    limit-cauchy-sequence-Complete-Metric-Space ,
    is-limit-limit-cauchy-sequence-Complete-Metric-Space
```

### If every Cauchy sequence has a limit in a metric space, the metric space is complete

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-sequences-have-limits-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequences-have-limits-Metric-Space =
    (x : cauchy-sequence-Metric-Space M) →
    has-limit-cauchy-sequence-Metric-Space M x

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (H : cauchy-sequences-have-limits-Metric-Space M)
  where

  is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space :
    is-complete-Metric-Space M
  is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space x =
    let
      (lim , lim-is-seq-lim) =
        H (cauchy-sequence-cauchy-approximation-Metric-Space M x)
    in
      lim ,
      is-limit-cauchy-approximation-limit-cauchy-sequence-cauchy-approximation-Metric-Space
        ( M)
        ( x)
        ( lim)
        ( lim-is-seq-lim)

  complete-metric-space-cauchy-sequences-have-limits-Metric-Space :
    Complete-Metric-Space l1 l2
  complete-metric-space-cauchy-sequences-have-limits-Metric-Space =
    M , is-complete-metric-space-cauchy-sequences-have-limits-Metric-Space
```
