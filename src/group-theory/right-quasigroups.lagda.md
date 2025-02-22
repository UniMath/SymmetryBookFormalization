# Right quasigroups

```agda
module group-theory.right-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Idea

{{#concept "Right quasigroups" Agda=right-Quasigroup}} are sets - say, `Q` -
equipped with two operations - say, `*` and `/` - such that for
`x y : type-Set Q`, the following hold:

```text
  y ＝ (y * x) \ x
  y ＝ (y \ x) * x
```

## Definitions

```agda
module _
  {l : Level} (Q : Set l) (mul right-div : type-Set Q → type-Set Q → type-Set Q)
  where

  is-left-cancellative-right-div : UU l
  is-left-cancellative-right-div =
    (x y : type-Set Q) → y ＝ mul (right-div y x) x

  is-prop-is-left-cancellative-right-div :
    is-prop is-left-cancellative-right-div
  is-prop-is-left-cancellative-right-div =
    is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set Q y (mul (right-div y x) x)))

  is-right-cancellative-right-div : UU l
  is-right-cancellative-right-div =
    (x y : type-Set Q) → y ＝ right-div (mul y x) x

  is-prop-is-right-cancellative-right-div :
    is-prop is-right-cancellative-right-div
  is-prop-is-right-cancellative-right-div =
    is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set Q y (right-div (mul y x) x)))

  is-right-Quasigroup : UU l
  is-right-Quasigroup =
    is-left-cancellative-right-div × is-right-cancellative-right-div

  is-prop-is-right-Quasigroup : is-prop is-right-Quasigroup
  is-prop-is-right-Quasigroup =
    is-prop-Σ is-prop-is-left-cancellative-right-div
      ( λ _ → is-prop-is-right-cancellative-right-div)

right-Quasigroup : (l : Level) → UU (lsuc l)
right-Quasigroup l =
  Σ ( Set l)
    ( λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
    ( λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
    ( λ right-div → is-right-Quasigroup Q mul right-div)))
```
