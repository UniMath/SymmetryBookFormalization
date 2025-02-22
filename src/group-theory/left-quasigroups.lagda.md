# Left quasigroups

```agda
module group-theory.left-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.sets
```

</details>

## Idea

{{#concept "Left quasigroups" Agda=left-Quasigroup}} are
[sets](foundation-core.sets.md) - say, `Q` - equipped with two binary
operations - say, `*` and `/` - such that for `x y : type-Set Q`, the following
hold:

```text
  y ＝ x / (x * y)
  y ＝ x * (x / y)
```

## Definitions

```agda
module _
  {l : Level} (Q : Set l) (mul left-div : type-Set Q → type-Set Q → type-Set Q)
  where

  is-left-cancellative-left-div : UU l
  is-left-cancellative-left-div = (x y : type-Set Q) → y ＝ mul x (left-div x y)

  is-prop-is-left-cancellative-left-div : is-prop is-left-cancellative-left-div
  is-prop-is-left-cancellative-left-div =
    is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set Q y (mul x (left-div x y))))

  is-right-cancellative-left-div : UU l
  is-right-cancellative-left-div = (x y : type-Set Q) → y ＝ left-div x (mul x y)

  is-prop-is-right-cancellative-left-div :
    is-prop is-right-cancellative-left-div
  is-prop-is-right-cancellative-left-div =
    is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set Q y (left-div x (mul x y))))

  is-left-Quasigroup : UU l
  is-left-Quasigroup =
    is-left-cancellative-left-div × is-right-cancellative-left-div

  is-prop-is-left-Quasigroup : is-prop is-left-Quasigroup
  is-prop-is-left-Quasigroup =
    is-prop-Σ is-prop-is-left-cancellative-left-div
      ( λ _ → is-prop-is-right-cancellative-left-div)

left-Quasigroup : (l : Level) → UU (lsuc l)
left-Quasigroup l =
  Σ ( Set l)
    ( λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
    ( λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
    ( λ left-div → is-left-Quasigroup Q mul left-div)))
```
