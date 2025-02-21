# Double negation stable equality

```agda
module foundation.double-negation-stable-equality where

open import foundation-core.double-negation-stable-equality public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.homotopies

open import logic.double-negation-dense-maps
open import logic.double-negation-dense-subtypes
```

</details>

## Idea

A type `A` is said to have
{{#concept "double negation stable equality" Disambiguation="type" Agda=has-double-negation-stable-equality}}
if `x ＝ y` has
[double negation elimination](logic.double-negation-elimination.md) for every
`x y : A`. By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
types with double negation stable equality are [sets](foundation-core.sets.md).

## Properties

## Homotopies of maps into types with double negation stable equality

Given a double negation dense subtype `P ⊆ X` and two functions `f` and
`g : X → Y` into a type `Y` with double negation stable equality. Then if `f`
and `g` are homotopic on `P`, they are homotopic on all of `X`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : X → UU l2} {X' : UU l3} (i : X' ↠¬¬ X)
  where

  abstract
    htpy-htpy-double-negation-dense-map' :
      {f g : (x : X) → Y x}
      (K :
        (x : X') →
        f (map-double-negation-dense-map i x) ＝
        g (map-double-negation-dense-map i x)) →
      (x : X) → ¬¬ (f x ＝ g x)
    htpy-htpy-double-negation-dense-map' {f} {g} K x =
      map-double-negation
        ( λ where (x' , refl) → K x')
        ( is-double-negation-dense-map-double-negation-dense-map i x)

  htpy-htpy-double-negation-dense-map :
    (H : (x : X) → has-double-negation-stable-equality (Y x))
    {f g : (x : X) → Y x}
    (K :
      (x : X') →
      f (map-double-negation-dense-map i x) ＝
      g (map-double-negation-dense-map i x)) →
    f ~ g
  htpy-htpy-double-negation-dense-map H {f} {g} K x =
    H x (f x) (g x) (htpy-htpy-double-negation-dense-map' {f} {g} K x)

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : X → UU l2}
  (P : double-negation-dense-subtype l3 X)
  (H : (x : X) → has-double-negation-stable-equality (Y x))
  where

  htpy-htpy-on-double-negation-dense-subtype :
    {f g : (x : X) → Y x}
    (K :
      (x : type-double-negation-dense-subtype P) →
      f (inclusion-double-negation-dense-subtype P x) ＝
      g (inclusion-double-negation-dense-subtype P x)) →
    f ~ g
  htpy-htpy-on-double-negation-dense-subtype =
    htpy-htpy-double-negation-dense-map
      ( double-negation-dense-inclusion-double-negation-dense-subtype P)
      ( H)
```

As a corollary, if `f` is constant on `P`, it is constant on all of `X`. This is
Lemma 3.4 in {{#cite Esc13}}

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (P : double-negation-dense-subtype l3 X)
  (H : has-double-negation-stable-equality Y)
  where

  htpy-const-htpy-const-on-double-negation-dense-subtype :
    (f : X → Y) (y : Y)
    (K :
      (x : type-double-negation-dense-subtype P) →
      f (inclusion-double-negation-dense-subtype P x) ＝ y) →
    (x : X) → f x ＝ y
  htpy-const-htpy-const-on-double-negation-dense-subtype f y =
    htpy-htpy-on-double-negation-dense-subtype P (λ _ → H)
```

## See also

- Every type with a
  [tight apartness relation](foundation.tight-apartness-relations.md) has double
  negation stable equality. Conversely, every type with double negation stable
  equality has a tight, symmetric, antireflexive relation. However, this
  relation need not be cotransitive.

## References

{{#bibliography}}

## External links

- [double negation stable equality](https://ncatlab.org/nlab/show/decidable+equality)
  at $n$Lab
