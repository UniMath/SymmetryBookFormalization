# Quasigroups

```agda
module group-theory.quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.left-quasigroups
open import group-theory.right-quasigroups

open import structured-types.magmas
```

</details>

## Idea

{{#concept "Quasigroups" Agda=Quasigroup}} are both
[left](group-theory.left-quasigroups.md) and
[right](group-theory.right-quasigroups.md) quasigroups with a compatible
multiplication.

## Definitions

```agda
Quasigroup : (l : Level) → UU (lsuc l)
Quasigroup l =
  Σ (Set l) λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
  (λ left-div → Σ (type-Set Q → type-Set Q → type-Set Q) (λ right-div →
  is-left-Quasigroup Q mul left-div × is-right-Quasigroup Q mul right-div)))

module _
  {l : Level} (Q : Quasigroup l)
  where

  set-Quasigroup : Set l
  set-Quasigroup = pr1 Q

  type-Quasigroup : UU l
  type-Quasigroup = type-Set set-Quasigroup

  is-set-Quasigroup : is-set type-Quasigroup
  is-set-Quasigroup = is-set-type-Set set-Quasigroup

  mul-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  mul-Quasigroup = pr1 (pr2 Q)

  left-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  left-div-Quasigroup = pr1 (pr2 (pr2 Q))

  right-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  right-div-Quasigroup = pr1 (pr2 (pr2 (pr2 Q)))

  is-left-cancellative-left-div-Quasigroup :
    is-left-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-left-cancellative-left-div-Quasigroup = pr1 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-left-div-Quasigroup :
    is-right-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-right-cancellative-left-div-Quasigroup =
    pr2 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-left-cancellative-right-div-Quasigroup :
    is-left-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-left-cancellative-right-div-Quasigroup =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-right-div-Quasigroup :
    is-right-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-right-cancellative-right-div-Quasigroup =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))
```
