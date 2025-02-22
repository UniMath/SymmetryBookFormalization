# Units in quasigroups

```agda
module group-theory.units-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.quasigroups
```

</details>

## Idea

There are notions of {{#concept "left units" Agda=has-left-unit-Quasigroup}} and
{{#concept "right units" Agda=has-right-unit-Quasigroup}} for
[quasigroups](quasigroups.quasigroups.md). It turns out that the spaces of left
and right units in a quasigroup `Q` are propositions, and even better, if `Q`
has both a left and right unit, then they coincide.

## Definitions

### Left units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  is-left-unit-Quasigroup : (e : type-Quasigroup Q) → UU l
  is-left-unit-Quasigroup e = (x : type-Quasigroup Q) → mul-Quasigroup Q e x ＝ x

  is-prop-is-left-unit-Quasigroup : (e : type-Quasigroup Q) → is-prop (is-left-unit-Quasigroup e)
  is-prop-is-left-unit-Quasigroup e = is-prop-Π (λ x → is-set-Quasigroup Q (mul-Quasigroup Q e x) x)

  has-left-unit-Quasigroup : UU l
  has-left-unit-Quasigroup = Σ (type-Quasigroup Q) λ e → is-left-unit-Quasigroup e

  left-units-agree-Quasigroup : (e f : type-Quasigroup Q) → is-left-unit-Quasigroup e → is-left-unit-Quasigroup f → e ＝ f
  left-units-agree-Quasigroup e f e-left-unit f-left-unit = equational-reasoning
    e
    ＝ {!   !}
      by {!   !}
    ＝ {!   !}
      by {!   !}
    ＝ f
      by {!   !}
```

### Right units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where
```

### Units in quasigroups

Recall that a **unit** is both a left and right unit.

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where
```
