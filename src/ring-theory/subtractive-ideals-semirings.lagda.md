# Subtractive ideals of semirings

```agda
module ring-theory.subtractive-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An [ideal](ring-theory.ideals-semirings.md) $I$ of a
[semiring](ring-theory.semirings.md) $R$ is said to be a
{{#concept "subtractive ideal" Disambiguation="semirings" Agda=is-subtractive-ideal-Semiring}}
if for every $a,b : R$ such that $a\in S$ and $a+b \in S$, we have $b \in S$.

## Definitions

### Subtractive subsets of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : subset-Semiring l2 R)
  where

  is-subtractive-subset-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-subset-Semiring =
    (a b : type-Semiring R) →
    is-in-subtype I a → is-in-subtype I (add-Semiring R a b) → is-in-subtype I b
```

### Subtractive ideals of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  is-subtractive-ideal-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-ideal-Semiring =
    is-subtractive-subset-Semiring R (subset-ideal-Semiring R I)
```

### Subtractive left ideals of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  is-subtractive-left-ideal-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-left-ideal-Semiring =
    is-subtractive-subset-Semiring R (subset-left-ideal-Semiring R I)
```

### Subtractive right ideals of a semiring

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  is-subtractive-right-ideal-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-right-ideal-Semiring =
    is-subtractive-subset-Semiring R (subset-right-ideal-Semiring R I)
```
