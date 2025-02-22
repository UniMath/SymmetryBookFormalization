# Dependent lists

```agda
module lists.dependent-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

Consider a dependent type `B` over a type `A`, and let `l` be a [list](lists.lists.md)` of elements of `A`. A {{#concept "dependent list" Agda=dependent-list}} of elements of `B` over `l` consists of a choice of an element `B x` for every element of `l`. More formally, the type `dependent-list B l` of dependent lists is a data type with constructors

```text
  nil-dependent-list : dependent-list B nil
  cons-dependent-list : B x → dependent-list B l → dependent-list B (cons x l)
```

Note that the type `dependent-list B l` is [equivalent](foundation-core.equivalences.md) to the [universal quantification](lists.universal-quantification-lists.md) over the elements of `l` at `B`.

## Definitions

### Dependent lists

```agda
module _
  {l1 l2 : Level} {A : UU l2} (B : A → UU l2)
  where

  data dependent-list : (l : list A) → UU (l1 ⊔ l2)
    where
    nil-dependent-list :
      dependent-list nil
    cons-dependent-list :
      (a : A) (l : list A) → B a → dependent-list l → dependent-list (cons a l)
```

