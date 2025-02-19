# Units in quasigroups

```agda
module group-theory.units-quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

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
```

### Right units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where
```
