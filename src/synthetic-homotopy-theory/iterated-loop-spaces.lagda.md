# Iterated loop spaces

<details><summary>Imports</summary>
```agda
module synthetic-homotopy-theory.iterated-loop-spaces where

open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```
</details>

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
```
