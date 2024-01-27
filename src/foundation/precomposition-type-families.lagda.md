# Precomposition of type families

```agda
module foundation.precomposition-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopy-induction
open import foundation.transport-along-homotopies
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Any map `f : A → B` induces a
{{#concept "precomposition operation" Disambiguation="type families"}}

```text
  (B → 𝒰) → (A → 𝒰)
```

given by [precomposing](foundation-core.precomposition-functions.md) any
`Q : B → 𝒰` to `Q ∘ f : A → 𝒰`.

## Definitions

### The precomposition operation on type familes

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  precomp-family : {l : Level} → (B → UU l) → (A → UU l)
  precomp-family Q = Q ∘ f
```

## Properties

### Transport in precomposed type families

TODO

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  {X : UU l4} {g : X → A}
  where

  statement-tr-precomp-family :
    {h : X → A} (H : g ~ h) → UU (l3 ⊔ l4)
  statement-tr-precomp-family H =
    tr-htpy (λ _ → precomp-family f Q) H ~ tr-htpy (λ _ → Q) (f ·l H)

  tr-precomp-family :
    {h : X → A} (H : g ~ h) →
    statement-tr-precomp-family H
  tr-precomp-family =
    ind-htpy g
      ( λ h → statement-tr-precomp-family)
      ( refl-htpy)

  abstract
    compute-tr-precomp-family :
      tr-precomp-family refl-htpy ＝
      refl-htpy
    compute-tr-precomp-family =
      compute-ind-htpy g
        ( λ h → statement-tr-precomp-family)
        ( refl-htpy)
```
