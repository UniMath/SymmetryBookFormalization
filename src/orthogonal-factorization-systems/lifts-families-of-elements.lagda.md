# Lifts of families of elements

```agda
module orthogonal-factorization-systems.lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.precomposition-type-families
open import foundation.transport-along-homotopies
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Consider a type family

```text
  B : (i : I) → A i → 𝒰
```

and a family of elements `a : (i : I) → A i`.

A {{#concept "dependent lift" Disambiguation="family of elements"}} of the
family of elements `a` to the type family `B` is a family of elements

```text
  (i : I) → B i (a i).
```

An important special case occurs when `a : I → A` is a family of elements of a
fixed type `A`, and `B` is a type family over `A`. In this case, a
{{#concept "lift" Disambiguation="family of elements"}} of the family of
elements `a` is a family of elements

```text
  (i : I) → B (a i).
```

## Definitions

### Dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (B : (i : I) → A i → UU l3)
  (a : (i : I) → A i)
  where

  dependent-lift-family-of-elements : UU (l1 ⊔ l3)
  dependent-lift-family-of-elements = (i : I) → B i (a i)
```

### Lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) (a : I → A)
  where

  lift-family-of-elements : UU (l1 ⊔ l3)
  lift-family-of-elements = dependent-lift-family-of-elements (λ _ → B) a
```

### Total space of dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} (A : I → UU l2) (B : (i : I) → A i → UU l3)
  where

  total-dependent-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  total-dependent-lift-family-of-elements =
    Σ ( (i : I) → A i)
      ( dependent-lift-family-of-elements B)
```

### Total space of lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} (I : UU l1) {A : UU l2} (B : A → UU l3)
  where

  total-lift-family-of-elements : UU (l1 ⊔ l2 ⊔ l3)
  total-lift-family-of-elements =
    total-dependent-lift-family-of-elements (λ (_ : I) → A) (λ _ → B)
```

### Dependent lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  (C : (i : I) (x : A i) → B i x → UU l4) (a : (i : I) → A i)
  where

  dependent-lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  dependent-lift-binary-family-of-elements =
    dependent-lift-family-of-elements (λ i x → (y : B i x) → C i x y) a
```

### Lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  {C : (x : A) → B x → UU l4} (a : I → A)
  where

  lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  lift-binary-family-of-elements =
    dependent-lift-binary-family-of-elements (λ _ → C) a
```

## Properties

### Transport in lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (B : A → UU l3) (a : I → A)
  {J : UU l4} {f : J → I}
  where

  statement-tr-lift-family-of-elements : {g : J → I} (H : f ~ g) → UU (l3 ⊔ l4)
  statement-tr-lift-family-of-elements H =
    tr (lift-family-of-elements B) (htpy-precomp H A a) ~
    tr-htpy (λ _ → precomp-family a B) H

  tr-lift-family-of-elements-refl-htpy :
    statement-tr-lift-family-of-elements refl-htpy
  tr-lift-family-of-elements-refl-htpy b =
    ap
      ( λ p → tr (lift-family-of-elements B) p b)
      ( compute-htpy-precomp-refl-htpy f A a)

  tr-lift-family-of-elements :
    {g : J → I} (H : f ~ g) → statement-tr-lift-family-of-elements H
  tr-lift-family-of-elements =
    ind-htpy f
      ( λ g → statement-tr-lift-family-of-elements)
      ( tr-lift-family-of-elements-refl-htpy)

  abstract
    compute-tr-lift-family-of-elements :
      tr-lift-family-of-elements refl-htpy ＝
      tr-lift-family-of-elements-refl-htpy
    compute-tr-lift-family-of-elements =
      compute-ind-htpy f
        ( λ g → statement-tr-lift-family-of-elements)
        ( tr-lift-family-of-elements-refl-htpy)
```

## See also

- [Double lifts of families of elements](orthogonal-factorization-systems.double-lifts-families-of-elements.md)
- [Lifts of maps](orthogonal-factorization-systems.lifts-of-maps.md)
