# Dependent suspension structures

```agda
module synthetic-homotopy-theory.dependent-suspension-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.conjugation-loops
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

This is the dependent analog of
[suspension structures](synthetic-homotopy-theory.suspension-structures.md). The
relation between
[suspension structures](synthetic-homotopy-theory.suspension-structures.md) and
dependent suspension structures mirrors the relation between
[cocones under a span](synthetic-homotopy-theory.cocones-under-spans.md) and
[dependent cocones under a span](synthetic-homotopy-theory.dependent-cocones-under-spans.md).

Fix a type `X` and consider a suspension cocone `(f , g , h)` with nadir `Y`.
Given a type family `P : Y → UU`, a dependent suspension cocone on `P` over
`(f , g , h)` consists of dependent functions

```text
north : (t : unit) → P (f t)

south : (t : unit) → P (g t)
```

together with a family of dependent identifications

```text
merid : (x : X) → dependent-identification P (h x) ((north ∘ (const X unit star)) x) (south ∘ (const X unit star) x)
```

Using the [universal property of `unit`](foundation.unit-type.md) and the
previous characterization of suspension cocones (to be found in the file
[synthetic-homotopy-theory.suspension-structures](synthetic-homotopy-theory.suspension-structures.md)),
we can characterize dependent cocones over a suspension cocone as equivalent to
the following:

For a suspension structure `(N , S , m)`, a dependent suspension structure in
`P` over (N , S , m)` is given by points

```text
north : P N

south : P S
```

and a family of dependent identifications

```text
meridian : (x : X) → dependent-identification P (m x) north south
```

## Definition

### Dependent Suspension Cocones

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  (c : suspension-cocone X Y)
  where

  dependent-suspension-cocone : UU (l1 ⊔ l3)
  dependent-suspension-cocone =
    dependent-cocone
      ( const X unit star)
      ( const X unit star)
      ( c)
      ( B)
```

### Dependent Suspension Structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (ss : suspension-structure X Y)
  (B : Y → UU l3)
  where

  dependent-suspension-structure : UU (l1 ⊔ l3)
  dependent-suspension-structure =
    Σ ( B (north-suspension-structure ss))
      ( λ N →
        Σ ( B (south-suspension-structure ss))
          ( λ S →
            (x : X) →
            dependent-identification
              ( B)
              ( meridian-suspension-structure ss x)
              ( N)
              ( S)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {B : Y → UU l3}
  {ss : suspension-structure X Y}
  (d-ss : dependent-suspension-structure ss B)
  where

  north-dependent-suspension-structure : B (north-suspension-structure ss)
  north-dependent-suspension-structure = pr1 (d-ss)

  south-dependent-suspension-structure : B (south-suspension-structure ss)
  south-dependent-suspension-structure = (pr1 ∘ pr2) (d-ss)

  meridian-dependent-suspension-structure :
    (x : X) →
    dependent-identification
      ( B)
      ( meridian-suspension-structure ss x)
      ( north-dependent-suspension-structure)
      ( south-dependent-suspension-structure)
  meridian-dependent-suspension-structure = (pr2 ∘ pr2) (d-ss)
```

## Properties

#### Equivalence between dependent suspension structures and dependent suspension cocones

Soon TODO

#### Characterizing equality of dependent suspension structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {ss : suspension-structure X Y}
  (d-ss d-ss' : dependent-suspension-structure ss B)
  where

  htpy-dependent-suspension-structure : UU (l1 ⊔ l3)
  htpy-dependent-suspension-structure =
    Σ ( north-dependent-suspension-structure d-ss ＝
        north-dependent-suspension-structure d-ss')
      ( λ N-htpy →
        Σ ( south-dependent-suspension-structure d-ss ＝
            south-dependent-suspension-structure d-ss')
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( meridian-dependent-suspension-structure d-ss x)
              ( S-htpy)
              ( ap
                ( tr B (meridian-suspension-structure ss x))
                ( N-htpy))
              ( meridian-dependent-suspension-structure d-ss' x)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {ss : suspension-structure X Y}
  (d-ss : dependent-suspension-structure ss B)
  where

  extensionality-dependent-suspension-structure :
    ( d-ss' : dependent-suspension-structure ss B) →
    ( d-ss ＝ d-ss') ≃
    ( htpy-dependent-suspension-structure B d-ss d-ss')
  extensionality-dependent-suspension-structure =
    extensionality-Σ
      ( λ (S , m) (N-htpy) →
        Σ (south-dependent-suspension-structure d-ss ＝ S)
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( meridian-dependent-suspension-structure d-ss x)
              ( S-htpy)
              ( ap (tr B (meridian-suspension-structure ss x)) N-htpy)
              ( m x)))
      ( refl)
      ( refl , λ x → right-unit)
      ( λ N → id-equiv)
      ( extensionality-Σ
        ( λ m S-htpy →
          (x : X) →
          ( meridian-dependent-suspension-structure d-ss x ∙ S-htpy) ＝
          ( m x))
        ( refl)
        ( λ x → right-unit)
        ( λ S → id-equiv)
        ( λ m →
          equiv-concat-htpy right-unit-htpy m ∘e inv-equiv equiv-eq-htpy))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {ss : suspension-structure X Y}
  {d-ss d-ss' : dependent-suspension-structure ss B}
  where

  htpy-eq-dependent-suspension-structure :
    (d-ss ＝ d-ss') →
    htpy-dependent-suspension-structure B d-ss d-ss'
  htpy-eq-dependent-suspension-structure =
    map-equiv
      ( extensionality-dependent-suspension-structure B d-ss d-ss')

  eq-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-ss d-ss' →
    d-ss ＝ d-ss'
  eq-htpy-dependent-suspension-structure =
    map-inv-equiv
      ( extensionality-dependent-suspension-structure B d-ss d-ss')

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {ss : suspension-structure X Y}
  (d-ss : dependent-suspension-structure ss B)
  where

  refl-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-ss d-ss
  pr1 refl-htpy-dependent-suspension-structure = refl
  pr1 (pr2 refl-htpy-dependent-suspension-structure) = refl
  pr2 (pr2 refl-htpy-dependent-suspension-structure) x = right-unit

  is-refl-refl-htpy-dependent-suspension-structure :
    refl-htpy-dependent-suspension-structure ＝
    htpy-eq-dependent-suspension-structure B refl
  is-refl-refl-htpy-dependent-suspension-structure = refl
```
