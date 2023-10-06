# Dependent descent for the circle

```agda
module synthetic-homotopy-theory.dependent-descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import structured-types.dependent-types-equipped-with-automorphisms

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
```

</details>

## Idea

The **dependent descent property of the circle** asserts that a family over a
family `P` over the [circle](synthetic-homotopy-theory.circle.md) is [equivalently](foundation-core.equivalences.md) described by **dependent descent
data** over the descent data of `P`, which is defined as a
[dependent type with an automorphism](structured-types.dependent-types-equipped-with-automorphisms.md)

### Dependent descent data for the circle

The equivalence extends to the dependent case, where given a type family `A`
over the circle with descent data `(X, e)`, a type family
`B : (t : 𝕊¹) → A t → U` is equivalent to a type family `R : X → U` equipped
with a family of equivalences `k : (x : X) → R(x) ≃ R(e(x))`. The pair `(R, k)`
is called **dependent descent data** for the circle over `A`. Intuitively, this
states that the types over points of `X` belonging to the same connected
component in the total space `Σ 𝕊¹ A` are equivalent.

```agda
dependent-descent-data-circle :
  {l1 : Level} (l2 : Level) →
  descent-data-circle l1 → UU (l1 ⊔ lsuc l2)
dependent-descent-data-circle l2 P =
  Dependent-Type-With-Automorphism l2 P

module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  ( Q : dependent-descent-data-circle l2 P)
  where

  type-dependent-descent-data-circle : type-descent-data-circle P → UU l2
  type-dependent-descent-data-circle =
    family-Dependent-Type-With-Automorphism P Q

  dependent-automorphism-dependent-descent-data-circle :
    equiv-fam
      ( type-dependent-descent-data-circle)
      ( type-dependent-descent-data-circle ∘ (map-descent-data-circle P))
  dependent-automorphism-dependent-descent-data-circle =
    dependent-automorphism-Dependent-Type-With-Automorphism P Q

  map-dependent-descent-data-circle :
    { x : type-descent-data-circle P} →
    ( type-dependent-descent-data-circle x) →
    ( type-dependent-descent-data-circle (map-descent-data-circle P x))
  map-dependent-descent-data-circle =
    map-Dependent-Type-With-Automorphism P Q
```

### Canonical dependent descent data for a family over a family over the circle

```agda
dependent-descent-data-double-family-circle :
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S) →
  ( A : family-with-descent-data-circle l l2) →
  ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3) →
  dependent-descent-data-circle l3
    ( descent-data-family-with-descent-data-circle A)
pr1 (dependent-descent-data-double-family-circle l A B) x =
  B (base-free-loop l) (map-equiv-family-with-descent-data-circle A x)
pr2 (dependent-descent-data-double-family-circle l A B) x =
  equiv-tr
    ( ind-Σ B)
    ( eq-pair-Σ
      ( loop-free-loop l)
      ( inv (coherence-square-family-with-descent-data-circle A x)))
```

### The identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 l3 : Level} (P : descent-data-circle l1)
  where

  equiv-dependent-descent-data-circle :
    dependent-descent-data-circle l2 P → dependent-descent-data-circle l3 P →
    UU (l1 ⊔ l2 ⊔ l3)
  equiv-dependent-descent-data-circle =
    equiv-Dependent-Type-With-Automorphism P

module _
  { l1 l2 l3 : Level} (P : descent-data-circle l1)
  ( Q : dependent-descent-data-circle l2 P)
  ( T : dependent-descent-data-circle l3 P)
  ( α : equiv-dependent-descent-data-circle P Q T)
  where

  equiv-equiv-dependent-descent-data-circle :
    equiv-fam
      ( type-dependent-descent-data-circle P Q)
      ( type-dependent-descent-data-circle P T)
  equiv-equiv-dependent-descent-data-circle =
    equiv-equiv-Dependent-Type-With-Automorphism P Q T α

  map-equiv-dependent-descent-data-circle :
    { x : type-descent-data-circle P} →
    ( type-dependent-descent-data-circle P Q x) →
    ( type-dependent-descent-data-circle P T x)
  map-equiv-dependent-descent-data-circle =
    map-equiv-Dependent-Type-With-Automorphism P Q T α

  coherence-square-equiv-dependent-descent-data-circle :
    ( x : type-descent-data-circle P) →
    coherence-square-maps
      ( map-equiv-dependent-descent-data-circle)
      ( map-dependent-descent-data-circle P Q)
      ( map-dependent-descent-data-circle P T)
      ( map-equiv-dependent-descent-data-circle)
  coherence-square-equiv-dependent-descent-data-circle =
    coherence-square-equiv-Dependent-Type-With-Automorphism P Q T α
```

### A dependent family over the circle with corresponding dependent descent data

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  family-for-dependent-descent-data-circle :
    { l3 : Level} →
    dependent-descent-data-circle l3
      ( descent-data-family-with-descent-data-circle A) →
    UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-for-dependent-descent-data-circle {l3} Q =
    Σ ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3)
      ( λ B →
        equiv-dependent-descent-data-circle
          ( descent-data-family-with-descent-data-circle A)
          ( Q)
          ( dependent-descent-data-double-family-circle l A B))

  dependent-descent-data-circle-for-family :
    { l3 : Level} →
    ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3) →
    UU (l2 ⊔ lsuc l3)
  dependent-descent-data-circle-for-family {l3} B =
    Σ ( dependent-descent-data-circle l3
        ( descent-data-family-with-descent-data-circle A))
      ( λ Q →
        equiv-dependent-descent-data-circle
          ( descent-data-family-with-descent-data-circle A)
          ( Q)
          ( dependent-descent-data-double-family-circle l A B))

  family-with-dependent-descent-data-circle :
    ( l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-with-dependent-descent-data-circle l3 =
    Σ ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3)
      dependent-descent-data-circle-for-family

module _
  { l1 l2 l3 : Level} {S : UU l1} {l : free-loop S}
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-dependent-descent-data-circle l A l3)
  where

  double-family-with-dependent-descent-data-circle :
    ( x : S) → (family-family-with-descent-data-circle A x) → UU l3
  double-family-with-dependent-descent-data-circle = pr1 B

  dependent-descent-data-for-family-with-dependent-descent-data-circle :
    dependent-descent-data-circle-for-family l A
      double-family-with-dependent-descent-data-circle
  dependent-descent-data-for-family-with-dependent-descent-data-circle = pr2 B

  dependent-descent-data-family-with-dependent-descent-data-circle :
    dependent-descent-data-circle l3
      ( descent-data-family-with-descent-data-circle A)
  dependent-descent-data-family-with-dependent-descent-data-circle =
    pr1 dependent-descent-data-for-family-with-dependent-descent-data-circle

  type-family-with-dependent-descent-data-circle :
    type-family-with-descent-data-circle A → UU l3
  type-family-with-dependent-descent-data-circle =
    type-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  dependent-automorphism-family-with-dependent-descent-data-circle :
    equiv-fam
    ( type-family-with-dependent-descent-data-circle)
    ( type-family-with-dependent-descent-data-circle ∘
      ( map-aut-family-with-descent-data-circle A))
  dependent-automorphism-family-with-dependent-descent-data-circle =
    dependent-automorphism-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  map-dependent-automorphism-family-with-dependent-descent-data-circle :
    { x : type-family-with-descent-data-circle A} →
    ( type-family-with-dependent-descent-data-circle x) →
    ( type-family-with-dependent-descent-data-circle
      ( map-aut-family-with-descent-data-circle A x))
  map-dependent-automorphism-family-with-dependent-descent-data-circle =
    map-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  eq-family-with-dependent-descent-data-circle :
    equiv-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( dependent-descent-data-double-family-circle l A
        ( double-family-with-dependent-descent-data-circle))
  eq-family-with-dependent-descent-data-circle =
    pr2 dependent-descent-data-for-family-with-dependent-descent-data-circle

  equiv-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    ( type-family-with-dependent-descent-data-circle x) ≃
    ( double-family-with-dependent-descent-data-circle
      ( base-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x))
  equiv-family-with-dependent-descent-data-circle =
    equiv-equiv-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( dependent-descent-data-double-family-circle l A
        ( double-family-with-dependent-descent-data-circle))
      ( eq-family-with-dependent-descent-data-circle)

  map-equiv-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    ( type-family-with-dependent-descent-data-circle x) →
    ( double-family-with-dependent-descent-data-circle
      ( base-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x))
  map-equiv-family-with-dependent-descent-data-circle x =
    map-equiv (equiv-family-with-dependent-descent-data-circle x)

  coherence-square-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    coherence-square-maps
      ( map-equiv-family-with-dependent-descent-data-circle x)
      ( map-dependent-automorphism-family-with-dependent-descent-data-circle)
      ( tr
        ( ind-Σ (double-family-with-dependent-descent-data-circle))
        ( eq-pair-Σ
          ( loop-free-loop l)
          ( inv (coherence-square-family-with-descent-data-circle A x))))
      ( map-equiv-family-with-dependent-descent-data-circle
        ( map-aut-family-with-descent-data-circle A x))
  coherence-square-family-with-dependent-descent-data-circle =
    coherence-square-equiv-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( dependent-descent-data-double-family-circle l A
        ( double-family-with-dependent-descent-data-circle))
      ( eq-family-with-dependent-descent-data-circle)

  family-for-family-with-dependent-descent-data-circle :
    family-for-dependent-descent-data-circle l A
      dependent-descent-data-family-with-dependent-descent-data-circle
  pr1 family-for-family-with-dependent-descent-data-circle =
    double-family-with-dependent-descent-data-circle
  pr2 family-for-family-with-dependent-descent-data-circle =
    eq-family-with-dependent-descent-data-circle
```

## Properties

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  where

  id-equiv-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle l2 P) →
    equiv-dependent-descent-data-circle P Q Q
  id-equiv-dependent-descent-data-circle =
    id-equiv-Dependent-Type-With-Automorphism P

  equiv-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle l2 P) →
    Q ＝ T → equiv-dependent-descent-data-circle P Q T
  equiv-eq-dependent-descent-data-circle =
    equiv-eq-Dependent-Type-With-Automorphism P

  is-contr-total-equiv-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle l2 P) →
    is-contr
      ( Σ ( dependent-descent-data-circle l2 P)
          ( equiv-dependent-descent-data-circle P Q))
  is-contr-total-equiv-dependent-descent-data-circle =
    is-contr-total-equiv-Dependent-Type-With-Automorphism P

  is-equiv-equiv-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle l2 P) →
    is-equiv (equiv-eq-dependent-descent-data-circle Q T)
  is-equiv-equiv-eq-dependent-descent-data-circle =
    is-equiv-equiv-eq-Dependent-Type-With-Automorphism P

  extensionality-dependent-descent-data-circle :
    (Q T : dependent-descent-data-circle l2 P) →
    (Q ＝ T) ≃ equiv-dependent-descent-data-circle P Q T
  extensionality-dependent-descent-data-circle =
    extensionality-Dependent-Type-With-Automorphism P

  eq-equiv-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle l2 P) →
    equiv-dependent-descent-data-circle P Q T → Q ＝ T
  eq-equiv-dependent-descent-data-circle =
    eq-equiv-Dependent-Type-With-Automorphism P
```

### Uniqueness of dependent descent data characterizing a type family over a family over the circle

Given a type family `A : 𝕊¹ → U` with corresponding descent data `(X, e)`, and a
type family `R : X → U` over `X` invariant under `e` as witnessed by `k`, there
is a unique family `B : (t : 𝕊¹) → A t → U` for which `(R, k)` is dependent
descent data over `A`.

This is so far a conjecture which remains to be shown.

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  unique-dependent-family-property-circle : UU (l1 ⊔ l2 ⊔ lsuc l3)
  unique-dependent-family-property-circle =
    ( Q :
      dependent-descent-data-circle l3
        ( descent-data-family-with-descent-data-circle A)) →
    is-contr (family-for-dependent-descent-data-circle l A Q)
```
