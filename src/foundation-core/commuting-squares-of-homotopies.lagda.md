# Commuting squares of homotopies

```agda
module foundation-core.commuting-squares-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

A square of [homotopies](foundation-core.homotopies.md)

```text
          top
      f ------> g
      |         |
 left |         | right
      v         v
      h ------> i
        bottom
```

is said to be a {{#concept "commuting square" Disambiguation="homotopies"}} of
homotopies if there is a homotopy `left ∙h bottom ~ top ∙h right `. Such a
homotopy is called a
{{#concept "coherence" Disambiguation="commuting square of homotopies" Agda=coherence-square-homotopies}}
of the square.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h i : (x : A) → B x}
  (top : f ~ g) (left : f ~ h) (right : g ~ i) (bottom : h ~ i)
  where

  coherence-square-homotopies : UU (l1 ⊔ l2)
  coherence-square-homotopies =
    left ∙h bottom ~ top ∙h right

  coherence-square-homotopies' : UU (l1 ⊔ l2)
  coherence-square-homotopies' =
    top ∙h right ~ left ∙h bottom
```
