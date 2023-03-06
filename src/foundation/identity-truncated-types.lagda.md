#  Identity types of truncated types

<details><summary>Imports</summary>
```agda
module foundation.identity-truncated-types where
open import foundation-core.equivalences
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.univalence
```
</details>

### The type of identity of truncated types is truncated

```agda
module _
  {l : Level} {A B : UU l}
  where

  is-trunc-id-is-trunc :
    (k : 𝕋) → is-trunc k A → is-trunc k B → is-trunc k (A ＝ B)
  is-trunc-id-is-trunc k is-trunc-A is-trunc-B =
    is-trunc-equiv k
      ( A ≃ B)
      ( equiv-univalence)
      ( is-trunc-equiv-is-trunc k is-trunc-A is-trunc-B)
```
