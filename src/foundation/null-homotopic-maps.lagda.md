# Null-homotopic maps

```agda
module foundation.null-homotopic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identifications
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-empty-type
open import foundation.universe-levels
open import foundation.weakly-constant-maps

open import foundation-core.equivalences
open import foundation-core.homotopies
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "null-homotopic" Disambiguation="map of types" Agda=is-null-homotopic}},
or _constant_, if there is an element `y : B` such for every `x : A` we have
`f x ＝ y`. In other words, `f` is null-homotopic if it is
[homotopic](foundation-core.homotopies.md) to a
[constant](foundation-core.constant-maps.md) function.

## Definition

### The type of null-homotopies of a map

```agda
is-null-homotopic :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-null-homotopic {A = A} {B} f = Σ B (λ y → (x : A) → f x ＝ y)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-null-homotopic f)
  where

  center-is-null-homotopic : B
  center-is-null-homotopic = pr1 H

  contraction-is-null-homotopic : (x : A) → f x ＝ center-is-null-homotopic
  contraction-is-null-homotopic = pr2 H
```

## Properties

### Characterizing equality of null-homotopies

Two null-homotopies `H` and `K` are equal if there is an
[equality](foundation-core.identity-types.md) of base points `p : H₀ ＝ K₀` such
that for every `x : A` we have a
[commuting triangle of identifications](foundation.commuting-triangles-of-identifications.md)

```text
        f x
        / \
   H₁x /   \ K₁x
      ∨     ∨
    H₀ ----> K₀.
         p
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-htpy-is-null-homotopic :
    (H K : is-null-homotopic f)
    (p : center-is-null-homotopic H ＝ center-is-null-homotopic K) →
    UU (l1 ⊔ l2)
  coherence-htpy-is-null-homotopic H K p =
    (x : A) →
    coherence-triangle-identifications
      ( contraction-is-null-homotopic K x)
      ( p)
      ( contraction-is-null-homotopic H x)

  htpy-is-null-homotopic : (H K : is-null-homotopic f) → UU (l1 ⊔ l2)
  htpy-is-null-homotopic H K =
    Σ ( center-is-null-homotopic H ＝ center-is-null-homotopic K)
      ( coherence-htpy-is-null-homotopic H K)

  refl-htpy-is-null-homotopic :
    (H : is-null-homotopic f) → htpy-is-null-homotopic H H
  refl-htpy-is-null-homotopic H = (refl , inv-htpy-right-unit-htpy)

  htpy-eq-is-null-homotopic :
    (H K : is-null-homotopic f) → H ＝ K → htpy-is-null-homotopic H K
  htpy-eq-is-null-homotopic H .H refl = refl-htpy-is-null-homotopic H

  is-torsorial-htpy-is-null-homotopic :
    (H : is-null-homotopic f) → is-torsorial (htpy-is-null-homotopic H)
  is-torsorial-htpy-is-null-homotopic H =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (center-is-null-homotopic H))
      ( center-is-null-homotopic H , refl)
      ( is-torsorial-htpy' (contraction-is-null-homotopic H ∙h refl-htpy))

  is-equiv-htpy-eq-is-null-homotopic :
    (H K : is-null-homotopic f) → is-equiv (htpy-eq-is-null-homotopic H K)
  is-equiv-htpy-eq-is-null-homotopic H =
    fundamental-theorem-id
      ( is-torsorial-htpy-is-null-homotopic H)
      ( htpy-eq-is-null-homotopic H)

  extensionality-htpy-is-null-homotopic :
    (H K : is-null-homotopic f) → (H ＝ K) ≃ htpy-is-null-homotopic H K
  extensionality-htpy-is-null-homotopic H K =
    ( htpy-eq-is-null-homotopic H K , is-equiv-htpy-eq-is-null-homotopic H K)

  eq-htpy-is-null-homotopic :
    (H K : is-null-homotopic f) → htpy-is-null-homotopic H K → H ＝ K
  eq-htpy-is-null-homotopic H K =
    map-inv-is-equiv (is-equiv-htpy-eq-is-null-homotopic H K)
```

### If the domain is empty the type of null-homotopies is equivalent to elements of `B`

```agda
module _
  {l : Level} {B : UU l} {f : empty → B}
  where

  compute-is-null-homotopic-empty-domain : is-null-homotopic f ≃ B
  compute-is-null-homotopic-empty-domain =
    right-unit-law-Σ-is-contr
      ( λ y → dependent-universal-property-empty' (λ x → f x ＝ y))
```

### If the domain has an element then the center of the null-homotopy is unique

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  eq-center-is-null-homotopic-has-element-domain :
    A →
    (H K : is-null-homotopic f) →
    center-is-null-homotopic H ＝ center-is-null-homotopic K
  eq-center-is-null-homotopic-has-element-domain a H K =
    inv (contraction-is-null-homotopic H a) ∙ contraction-is-null-homotopic K a
```

### If the codomain is a set and the domain has an element then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-set-B : is-set B) (a : A)
  {f : A → B}
  where

  all-elements-equal-is-null-homotopic-has-element-domain-is-set-codomain :
    all-elements-equal (is-null-homotopic f)
  all-elements-equal-is-null-homotopic-has-element-domain-is-set-codomain H K =
    eq-htpy-is-null-homotopic H K
      ( ( eq-center-is-null-homotopic-has-element-domain a H K) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-is-null-homotopic K))))

  is-prop-is-null-homotopic-has-element-domain-is-set-codomain :
    is-prop (is-null-homotopic f)
  is-prop-is-null-homotopic-has-element-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-null-homotopic-has-element-domain-is-set-codomain)
```

### If the codomain is a set and the domain is inhabited then being null-homotopic is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (a : is-inhabited A) (is-set-B : is-set B)
  {f : A → B}
  where

  eq-center-is-null-homotopic-is-inhabited-domain-is-set-codomain :
    (H K : is-null-homotopic f) →
    center-is-null-homotopic H ＝ center-is-null-homotopic K
  eq-center-is-null-homotopic-is-inhabited-domain-is-set-codomain H K =
    rec-trunc-Prop
      ( Id-Prop
        ( B , is-set-B)
        ( center-is-null-homotopic H)
        ( center-is-null-homotopic K))
      ( λ x → eq-center-is-null-homotopic-has-element-domain x H K)
      ( a)

  all-elements-equal-is-null-homotopic-is-inhabited-domain-is-set-codomain :
    all-elements-equal (is-null-homotopic f)
  all-elements-equal-is-null-homotopic-is-inhabited-domain-is-set-codomain H K =
    eq-htpy-is-null-homotopic H K
      ( ( eq-center-is-null-homotopic-is-inhabited-domain-is-set-codomain H K) ,
        ( λ x → eq-is-prop (is-set-B (f x) (center-is-null-homotopic K))))

  is-prop-is-null-homotopic-is-inhabited-domain-is-set-codomain :
    is-prop (is-null-homotopic f)
  is-prop-is-null-homotopic-is-inhabited-domain-is-set-codomain =
    is-prop-all-elements-equal
      ( all-elements-equal-is-null-homotopic-is-inhabited-domain-is-set-codomain)
```

### Null-homotopic maps from `A` to `B` are in correspondence with elements of `B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  compute-null-homotopic-map : Σ (A → B) (is-null-homotopic) ≃ B
  compute-null-homotopic-map =
    equivalence-reasoning
      Σ (A → B) (is-null-homotopic)
      ≃ Σ B (λ b → Σ (A → B) (λ f → f ~ const A b)) by equiv-left-swap-Σ
      ≃ B by right-unit-law-Σ-is-contr (λ b → is-torsorial-htpy' (const A b))
```

### Null-homotopic maps are weakly constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-weakly-constant-is-null-homotopic :
    is-null-homotopic f → is-weakly-constant f
  is-weakly-constant-is-null-homotopic (b , H) x y = H x ∙ inv (H y)
```

## See also

- [Weakly constant maps](foundation.weakly-constant-maps.md)

## External links

- [null homotopy](https://ncatlab.org/nlab/show/null+homotopy) at $n$Lab
