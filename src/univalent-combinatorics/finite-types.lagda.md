# Finite types

```agda
module univalent-combinatorics.finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.0-connected-types
open import foundation.1-types
open import foundation.action-on-identifications-functions
open import foundation.connected-components-universes
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.torsorial-type-families

open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type is
{{#concept "finite" Disambiguation="type" Agda=is-finite WD="finite set" WDID=Q272404}}
if it is [merely equivalent](foundation.mere-equivalences.md) to a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

**Terminology.** This finiteness condition is also referred to as _Bishop
finiteness_. (Cf. the external links at the bottom of this page)

## Definition

### Finite types

```agda
is-finite-Prop :
  {l : Level} → UU l → Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

abstract
  is-prop-is-finite :
    {l : Level} (X : UU l) → is-prop (is-finite X)
  is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

abstract
  is-finite-count :
    {l : Level} {X : UU l} → count X → is-finite X
  is-finite-count = unit-trunc-Prop
```

### The type of all finite types of a universe level

```agda
Finite-Type : (l : Level) → UU (lsuc l)
Finite-Type l = Σ (UU l) is-finite

type-Finite-Type : {l : Level} → Finite-Type l → UU l
type-Finite-Type = pr1

is-finite-type-Finite-Type :
  {l : Level} (X : Finite-Type l) → is-finite (type-Finite-Type X)
is-finite-type-Finite-Type = pr2
```

### Types with finite cardinality `k`

```agda
has-cardinality-ℕ-Prop :
  {l : Level} → ℕ → UU l → Prop l
has-cardinality-ℕ-Prop k = mere-equiv-Prop (Fin k)

has-cardinality-ℕ :
  {l : Level} → ℕ → UU l → UU l
has-cardinality-ℕ k = mere-equiv (Fin k)
```

### The type of all types of cardinality `k` of a given universe level

```agda
Type-With-Cardinality-ℕ : (l : Level) → ℕ → UU (lsuc l)
Type-With-Cardinality-ℕ l k = Σ (UU l) (has-cardinality-ℕ k)

type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → Type-With-Cardinality-ℕ l k → UU l
type-Type-With-Cardinality-ℕ k = pr1

abstract
  has-cardinality-type-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
    mere-equiv (Fin k) (type-Type-With-Cardinality-ℕ k X)
  has-cardinality-type-Type-With-Cardinality-ℕ k = pr2
```

### Types of finite cardinality

```agda
has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (λ k → has-cardinality-ℕ k X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

abstract
  mere-equiv-has-finite-cardinality :
    {l : Level} {X : UU l} (c : has-finite-cardinality X) →
    type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
  mere-equiv-has-finite-cardinality = pr2
```

## Properties

### Finite types are closed under equivalences

```agda
abstract
  is-finite-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite A → is-finite B
  is-finite-equiv e =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv e))

abstract
  is-finite-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-finite A → is-finite B
  is-finite-is-equiv is-equiv-f =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

abstract
  is-finite-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite B → is-finite A
  is-finite-equiv' e = is-finite-equiv (inv-equiv e)
```

### Finite types are closed under mere equivalences

```agda
abstract
  is-finite-mere-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-finite A → is-finite B
  is-finite-mere-equiv e H =
    apply-universal-property-trunc-Prop e
      ( is-finite-Prop _)
      ( λ e' → is-finite-equiv e' H)
```

### The empty type is finite

```agda
abstract
  is-finite-empty : is-finite empty
  is-finite-empty = is-finite-count count-empty

empty-Finite-Type : Finite-Type lzero
pr1 empty-Finite-Type = empty
pr2 empty-Finite-Type = is-finite-empty

empty-Type-With-Cardinality-ℕ : Type-With-Cardinality-ℕ lzero zero-ℕ
pr1 empty-Type-With-Cardinality-ℕ = empty
pr2 empty-Type-With-Cardinality-ℕ = unit-trunc-Prop id-equiv
```

### The empty type has finite cardinality

```agda
has-finite-cardinality-empty : has-finite-cardinality empty
pr1 has-finite-cardinality-empty = zero-ℕ
pr2 has-finite-cardinality-empty = unit-trunc-Prop id-equiv
```

### Empty types are finite

```agda
abstract
  is-finite-is-empty :
    {l1 : Level} {X : UU l1} → is-empty X → is-finite X
  is-finite-is-empty H = is-finite-count (count-is-empty H)
```

### Empty types have finite cardinality

```agda
has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
pr1 (has-finite-cardinality-is-empty f) = zero-ℕ
pr2 (has-finite-cardinality-is-empty f) =
  unit-trunc-Prop (equiv-count (count-is-empty f))
```

### The unit type is finite

```agda
abstract
  is-finite-unit : is-finite unit
  is-finite-unit = is-finite-count count-unit

abstract
  is-finite-raise-unit :
    {l1 : Level} → is-finite (raise-unit l1)
  is-finite-raise-unit {l1} =
    is-finite-equiv (compute-raise-unit l1) is-finite-unit

unit-Finite-Type : Finite-Type lzero
pr1 unit-Finite-Type = unit
pr2 unit-Finite-Type = is-finite-unit

unit-Type-With-Cardinality-ℕ : Type-With-Cardinality-ℕ lzero 1
pr1 unit-Type-With-Cardinality-ℕ = unit
pr2 unit-Type-With-Cardinality-ℕ =
  unit-trunc-Prop (left-unit-law-coproduct unit)
```

### Contractible types are finite

```agda
abstract
  is-finite-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → is-finite X
  is-finite-is-contr H = is-finite-count (count-is-contr H)

abstract
  has-cardinality-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → has-cardinality-ℕ 1 X
  has-cardinality-is-contr H =
    unit-trunc-Prop (equiv-is-contr is-contr-Fin-1 H)
```

### The standard finite types are finite

```agda
abstract
  is-finite-Fin : (k : ℕ) → is-finite (Fin k)
  is-finite-Fin k = is-finite-count (count-Fin k)

Fin-Finite-Type : ℕ → Finite-Type lzero
pr1 (Fin-Finite-Type k) = Fin k
pr2 (Fin-Finite-Type k) = is-finite-Fin k

has-cardinality-raise-Fin :
  {l : Level} (k : ℕ) → has-cardinality-ℕ k (raise-Fin l k)
has-cardinality-raise-Fin {l} k = unit-trunc-Prop (compute-raise-Fin l k)

raise-Fin-Type-With-Cardinality-ℕ :
  (l : Level) (k : ℕ) → Type-With-Cardinality-ℕ l k
pr1 (raise-Fin-Type-With-Cardinality-ℕ l k) = raise-Fin l k
pr2 (raise-Fin-Type-With-Cardinality-ℕ l k) = has-cardinality-raise-Fin k

Fin-Type-With-Cardinality-ℕ :
  (k : ℕ) → Type-With-Cardinality-ℕ lzero k
pr1 (Fin-Type-With-Cardinality-ℕ k) = Fin k
pr2 (Fin-Type-With-Cardinality-ℕ k) = unit-trunc-Prop id-equiv
```

### Every type of cardinality `k` is finite

```agda
abstract
  is-finite-type-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
    is-finite (type-Type-With-Cardinality-ℕ k X)
  is-finite-type-Type-With-Cardinality-ℕ k X =
    is-finite-mere-equiv
      ( has-cardinality-type-Type-With-Cardinality-ℕ k X)
      ( is-finite-Fin k)

finite-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → Type-With-Cardinality-ℕ l k → Finite-Type l
pr1 (finite-type-Type-With-Cardinality-ℕ k X) =
  type-Type-With-Cardinality-ℕ k X
pr2 (finite-type-Type-With-Cardinality-ℕ k X) =
  is-finite-type-Type-With-Cardinality-ℕ k X
```

### Having a finite cardinality is a proposition

```agda
abstract
  all-elements-equal-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
  all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
    eq-type-subtype
      ( λ k → mere-equiv-Prop (Fin k) X)
      ( apply-universal-property-trunc-Prop K
        ( Id-Prop ℕ-Set k l)
        ( λ (e : Fin k ≃ X) →
          apply-universal-property-trunc-Prop L
            ( Id-Prop ℕ-Set k l)
            ( λ (f : Fin l ≃ X) →
              is-equivalence-injective-Fin (inv-equiv f ∘e e))))

abstract
  is-prop-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
  is-prop-has-finite-cardinality =
    is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → Prop l1
pr1 (has-finite-cardinality-Prop X) = has-finite-cardinality X
pr2 (has-finite-cardinality-Prop X) = is-prop-has-finite-cardinality
```

### A type has a finite cardinality if and only if it is finite

```agda
module _
  {l : Level} {X : UU l}
  where

  abstract
    is-finite-has-finite-cardinality : has-finite-cardinality X → is-finite X
    is-finite-has-finite-cardinality (pair k K) =
      apply-universal-property-trunc-Prop K
        ( is-finite-Prop X)
        ( is-finite-count ∘ pair k)

  abstract
    is-finite-has-cardinality-ℕ : (k : ℕ) → has-cardinality-ℕ k X → is-finite X
    is-finite-has-cardinality-ℕ k H =
      is-finite-has-finite-cardinality (pair k H)

  has-finite-cardinality-count : count X → has-finite-cardinality X
  pr1 (has-finite-cardinality-count e) = number-of-elements-count e
  pr2 (has-finite-cardinality-count e) = unit-trunc-Prop (equiv-count e)

  abstract
    has-finite-cardinality-is-finite : is-finite X → has-finite-cardinality X
    has-finite-cardinality-is-finite =
      map-universal-property-trunc-Prop
        ( has-finite-cardinality-Prop X)
        ( has-finite-cardinality-count)

  number-of-elements-is-finite : is-finite X → ℕ
  number-of-elements-is-finite =
    number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

  abstract
    mere-equiv-is-finite :
      (f : is-finite X) → mere-equiv (Fin (number-of-elements-is-finite f)) X
    mere-equiv-is-finite f =
      mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

  abstract
    compute-number-of-elements-is-finite :
      (e : count X) (f : is-finite X) →
      Id (number-of-elements-count e) (number-of-elements-is-finite f)
    compute-number-of-elements-is-finite e f =
      ind-trunc-Prop
        ( λ g →
          Id-Prop ℕ-Set
            ( number-of-elements-count e)
            ( number-of-elements-is-finite g))
        ( λ g →
          ( is-equivalence-injective-Fin
            ( inv-equiv (equiv-count g) ∘e equiv-count e)) ∙
          ( ap pr1
            ( eq-is-prop' is-prop-has-finite-cardinality
              ( has-finite-cardinality-count g)
              ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
        ( f)

  has-cardinality-is-finite :
    (H : is-finite X) → has-cardinality-ℕ (number-of-elements-is-finite H) X
  has-cardinality-is-finite H =
    pr2 (has-finite-cardinality-is-finite H)

number-of-elements-Finite-Type : {l : Level} → Finite-Type l → ℕ
number-of-elements-Finite-Type X =
  number-of-elements-is-finite (is-finite-type-Finite-Type X)
```

### If a type has cardinality `k` and cardinality `l`, then `k = l`

```agda
eq-cardinality :
  {l1 : Level} {k l : ℕ} {A : UU l1} →
  has-cardinality-ℕ k A → has-cardinality-ℕ l A → Id k l
eq-cardinality H K =
  apply-universal-property-trunc-Prop H
    ( Id-Prop ℕ-Set _ _)
    ( λ e →
      apply-universal-property-trunc-Prop K
        ( Id-Prop ℕ-Set _ _)
        ( λ f → is-equivalence-injective-Fin (inv-equiv f ∘e e)))
```

### Equivalent finite types have the same cardinality

```agda
eq-cardinality-equiv-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  (H : is-finite A) (K : is-finite B) →
  number-of-elements-is-finite H ＝ number-of-elements-is-finite K
eq-cardinality-equiv-is-finite e H K =
  map-universal-property-trunc-Prop
    ( Id-Prop ℕ-Set _ _)
    ( λ c@(n , f) →
      eq-cardinality
        ( has-cardinality-is-finite H)
        ( unit-trunc-Prop (inv-equiv e ∘e f)) ∙
      compute-number-of-elements-is-finite c K)
    ( K)
```

### Any finite type is a set

```agda
abstract
  is-set-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-set X
  is-set-is-finite {l} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-set-Prop X)
      ( λ e → is-set-count e)

is-set-type-Finite-Type :
  {l : Level} (X : Finite-Type l) → is-set (type-Finite-Type X)
is-set-type-Finite-Type X = is-set-is-finite (is-finite-type-Finite-Type X)

set-Finite-Type : {l : Level} → Finite-Type l → Set l
pr1 (set-Finite-Type X) = type-Finite-Type X
pr2 (set-Finite-Type X) = is-set-is-finite (is-finite-type-Finite-Type X)
```

### Any type of cardinality `k` is a set

```agda
is-set-has-cardinality-ℕ :
  {l1 : Level} {X : UU l1} (k : ℕ) → has-cardinality-ℕ k X → is-set X
is-set-has-cardinality-ℕ k H = is-set-mere-equiv' H (is-set-Fin k)

is-set-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X : Type-With-Cardinality-ℕ l k) →
  is-set (type-Type-With-Cardinality-ℕ k X)
is-set-type-Type-With-Cardinality-ℕ k X =
  is-set-has-cardinality-ℕ k
    ( has-cardinality-type-Type-With-Cardinality-ℕ k X)

set-Type-With-Cardinality-ℕ :
  {l1 : Level} (k : ℕ) → Type-With-Cardinality-ℕ l1 k → Set l1
pr1 (set-Type-With-Cardinality-ℕ k X) =
  type-Type-With-Cardinality-ℕ k X
pr2 (set-Type-With-Cardinality-ℕ k X) =
  is-set-type-Type-With-Cardinality-ℕ k X
```

### A finite type is empty if and only if it has 0 elements

```agda
abstract
  is-empty-is-zero-number-of-elements-is-finite :
    {l1 : Level} {X : UU l1} (f : is-finite X) →
    is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
  is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p =
    apply-universal-property-trunc-Prop f
      ( is-empty-Prop X)
      ( λ e →
        is-empty-is-zero-number-of-elements-count e
          ( compute-number-of-elements-is-finite e f ∙ p))
```

### A finite type is contractible if and only if it has one element

```agda
is-one-number-of-elements-is-finite-is-contr :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-contr X → is-one-ℕ (number-of-elements-is-finite H)
is-one-number-of-elements-is-finite-is-contr H K =
  eq-cardinality
    ( has-cardinality-is-finite H)
    ( has-cardinality-is-contr K)

is-contr-is-one-number-of-elements-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) →
  is-one-ℕ (number-of-elements-is-finite H) → is-contr X
is-contr-is-one-number-of-elements-is-finite H p =
  apply-universal-property-trunc-Prop H
    ( is-contr-Prop _)
    ( λ e →
      is-contr-equiv'
        ( Fin 1)
        ( ( equiv-count e) ∘e
          ( equiv-tr Fin
            ( inv p ∙ inv (compute-number-of-elements-is-finite e H))))
        ( is-contr-Fin-1))

is-decidable-is-contr-is-finite :
  {l : Level} {X : UU l} (H : is-finite X) → is-decidable (is-contr X)
is-decidable-is-contr-is-finite H =
  is-decidable-iff
    ( is-contr-is-one-number-of-elements-is-finite H)
    ( is-one-number-of-elements-is-finite-is-contr H)
    ( has-decidable-equality-ℕ (number-of-elements-is-finite H) 1)
```

### The type of all pairs consisting of a natural number `k` and a type of cardinality `k` is equivalent to the type of all finite types

```agda
map-compute-total-Type-With-Cardinality-ℕ :
  {l : Level} → Σ ℕ (Type-With-Cardinality-ℕ l) → Finite-Type l
pr1 (map-compute-total-Type-With-Cardinality-ℕ (pair k (pair X e))) = X
pr2 (map-compute-total-Type-With-Cardinality-ℕ (pair k (pair X e))) =
  is-finite-has-finite-cardinality (pair k e)

compute-total-Type-With-Cardinality-ℕ :
  {l : Level} → Σ ℕ (Type-With-Cardinality-ℕ l) ≃ Finite-Type l
compute-total-Type-With-Cardinality-ℕ =
  ( equiv-tot
    ( λ X →
      equiv-iff-is-prop
        ( is-prop-has-finite-cardinality)
        ( is-prop-is-finite X)
        ( is-finite-has-finite-cardinality)
        ( has-finite-cardinality-is-finite))) ∘e
  ( equiv-left-swap-Σ)
```

### Finite types are either inhabited or empty

```agda
is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)
```

### Finite types of cardinality greater than one are inhabited

```agda
is-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ :
  {l1 : Level} (n : ℕ) (A : Type-With-Cardinality-ℕ l1 (succ-ℕ n)) →
  is-inhabited (type-Type-With-Cardinality-ℕ (succ-ℕ n) A)
is-inhabited-type-Type-With-Cardinality-ℕ-succ-ℕ n A =
  apply-universal-property-trunc-Prop
    ( pr2 A)
    ( is-inhabited-Prop (type-Type-With-Cardinality-ℕ (succ-ℕ n) A))
    ( λ e → unit-trunc-Prop (map-equiv e (zero-Fin n)))
```

### If `X` is finite, then its propositional truncation is decidable

```agda
is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H =
  map-coproduct
    ( id)
    ( map-universal-property-trunc-Prop empty-Prop)
      ( is-inhabited-or-empty-is-finite H)
```

### If a type is finite, then its propositional truncation is finite

```agda
abstract
  is-finite-type-trunc-Prop :
    {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
  is-finite-type-trunc-Prop = map-trunc-Prop count-type-trunc-Prop

trunc-prop-Finite-Type : {l : Level} → Finite-Type l → Finite-Type l
pr1 (trunc-prop-Finite-Type A) = type-trunc-Prop (type-Finite-Type A)
pr2 (trunc-prop-Finite-Type A) =
  is-finite-type-trunc-Prop (is-finite-type-Finite-Type A)
```

### We characterize the identity type of Finite-Type

```agda
equiv-Finite-Type :
  {l1 l2 : Level} → Finite-Type l1 → Finite-Type l2 → UU (l1 ⊔ l2)
equiv-Finite-Type X Y = type-Finite-Type X ≃ type-Finite-Type Y

id-equiv-Finite-Type : {l : Level} (X : Finite-Type l) → equiv-Finite-Type X X
id-equiv-Finite-Type X = id-equiv

extensionality-Finite-Type :
  {l : Level} (X Y : Finite-Type l) → Id X Y ≃ equiv-Finite-Type X Y
extensionality-Finite-Type = extensionality-subuniverse is-finite-Prop

is-torsorial-equiv-Finite-Type :
  {l : Level} (X : Finite-Type l) →
  is-torsorial (λ (Y : Finite-Type l) → equiv-Finite-Type X Y)
is-torsorial-equiv-Finite-Type {l} X =
  is-contr-equiv'
    ( Σ (Finite-Type l) (Id X))
    ( equiv-tot (extensionality-Finite-Type X))
    ( is-torsorial-Id X)

equiv-eq-Finite-Type :
  {l : Level} → (X Y : Finite-Type l) → Id X Y → equiv-Finite-Type X Y
equiv-eq-Finite-Type X Y = map-equiv (extensionality-Finite-Type X Y)

eq-equiv-Finite-Type :
  {l : Level} → (X Y : Finite-Type l) → equiv-Finite-Type X Y → Id X Y
eq-equiv-Finite-Type X Y = map-inv-equiv (extensionality-Finite-Type X Y)
```

### We characterize the identity type of families of finite types

```agda
equiv-fam-Finite-Type :
  {l1 l2 : Level} {X : UU l1} (Y Z : X → Finite-Type l2) → UU (l1 ⊔ l2)
equiv-fam-Finite-Type Y Z =
  equiv-fam (type-Finite-Type ∘ Y) (type-Finite-Type ∘ Z)

id-equiv-fam-Finite-Type :
  {l1 l2 : Level} {X : UU l1} (Y : X → Finite-Type l2) →
  equiv-fam-Finite-Type Y Y
id-equiv-fam-Finite-Type Y x = id-equiv

extensionality-fam-Finite-Type :
  {l1 l2 : Level} {X : UU l1} (Y Z : X → Finite-Type l2) →
  Id Y Z ≃ equiv-fam-Finite-Type Y Z
extensionality-fam-Finite-Type = extensionality-fam-subuniverse is-finite-Prop
```

### We characterize the identity type of `Type-With-Cardinality-ℕ`

```agda
equiv-Type-With-Cardinality-ℕ :
  {l1 l2 : Level} (k : ℕ) →
  Type-With-Cardinality-ℕ l1 k →
  Type-With-Cardinality-ℕ l2 k →
  UU (l1 ⊔ l2)
equiv-Type-With-Cardinality-ℕ k X Y =
  type-Type-With-Cardinality-ℕ k X ≃ type-Type-With-Cardinality-ℕ k Y

id-equiv-Type-With-Cardinality-ℕ :
  {l : Level} {k : ℕ} (X : Type-With-Cardinality-ℕ l k) →
  equiv-Type-With-Cardinality-ℕ k X X
id-equiv-Type-With-Cardinality-ℕ X = id-equiv-component-UU-Level X

equiv-eq-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) {X Y : Type-With-Cardinality-ℕ l k} →
  Id X Y → equiv-Type-With-Cardinality-ℕ k X Y
equiv-eq-Type-With-Cardinality-ℕ k p = equiv-eq-component-UU-Level p

abstract
  is-torsorial-equiv-Type-With-Cardinality-ℕ :
    {l : Level} {k : ℕ} (X : Type-With-Cardinality-ℕ l k) →
    is-torsorial
      ( λ (Y : Type-With-Cardinality-ℕ l k) →
        equiv-Type-With-Cardinality-ℕ k X Y)
  is-torsorial-equiv-Type-With-Cardinality-ℕ {l} {k} X =
    is-torsorial-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ :
    {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
    is-equiv (equiv-eq-Type-With-Cardinality-ℕ k {X = X} {Y})
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ k X =
    is-equiv-equiv-eq-component-UU-Level X

eq-equiv-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
  equiv-Type-With-Cardinality-ℕ k X Y → Id X Y
eq-equiv-Type-With-Cardinality-ℕ k X Y =
  eq-equiv-component-UU-Level X Y

equiv-equiv-eq-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) (X Y : Type-With-Cardinality-ℕ l k) →
  Id X Y ≃ equiv-Type-With-Cardinality-ℕ k X Y
pr1 (equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y) =
  equiv-eq-Type-With-Cardinality-ℕ k
pr2 (equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y) =
  is-equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y
```

### The type `Type-With-Cardinality-ℕ l k` is a 1-type

```agda
is-1-type-Type-With-Cardinality-ℕ :
  {l : Level} (k : ℕ) → is-1-type (Type-With-Cardinality-ℕ l k)
is-1-type-Type-With-Cardinality-ℕ k X Y =
  is-set-equiv
    ( equiv-Type-With-Cardinality-ℕ k X Y)
    ( equiv-equiv-eq-Type-With-Cardinality-ℕ k X Y)
    ( is-set-equiv-is-set
      ( is-set-type-Type-With-Cardinality-ℕ k X)
      ( is-set-type-Type-With-Cardinality-ℕ k Y))

Type-With-Cardinality-ℕ-1-Type : (l : Level) (k : ℕ) → 1-Type (lsuc l)
pr1 (Type-With-Cardinality-ℕ-1-Type l k) = Type-With-Cardinality-ℕ l k
pr2 (Type-With-Cardinality-ℕ-1-Type l k) =
  is-1-type-Type-With-Cardinality-ℕ k
```

### The type `Type-With-Cardinality-ℕ` is connected

```agda
abstract
  is-0-connected-Type-With-Cardinality-ℕ :
    {l : Level} (n : ℕ) → is-0-connected (Type-With-Cardinality-ℕ l n)
  is-0-connected-Type-With-Cardinality-ℕ {l} n =
    is-0-connected-mere-eq
      ( raise-Fin-Type-With-Cardinality-ℕ l n)
      ( λ A →
        map-trunc-Prop
          ( ( eq-equiv-Type-With-Cardinality-ℕ n
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( A)) ∘
            ( map-equiv
              ( equiv-precomp-equiv
                ( inv-equiv (compute-raise l (Fin n)))
                ( type-Type-With-Cardinality-ℕ n A))))
          ( pr2 A))
```

```agda
  equiv-has-cardinality-id-number-of-elements-is-finite :
    {l : Level} (X : UU l) ( H : is-finite X) (n : ℕ) →
    ( has-cardinality-ℕ n X ≃ Id (number-of-elements-is-finite H) n)
  pr1 (equiv-has-cardinality-id-number-of-elements-is-finite X H n) Q =
    ap
      ( number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( has-finite-cardinality-is-finite H)
        ( pair n Q))
  pr2 (equiv-has-cardinality-id-number-of-elements-is-finite X H n) =
    is-equiv-has-converse-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-set-ℕ (number-of-elements-is-finite H) n)
      ( λ p →
        tr
          ( λ m → has-cardinality-ℕ m X)
          ( p)
          ( pr2 (has-finite-cardinality-is-finite H)))
```

## External links

- [Finiteness in Sheaf Topoi](https://grossack.site/2024/08/19/finiteness-in-sheaf-topoi),
  blog post by Chris Grossack
- [`Fin.Bishop`](https://www.cs.bham.ac.uk/~mhe/TypeTopology/Fin.Bishop.html) at
  TypeTopology
- [finite set](https://ncatlab.org/nlab/show/finite+set) at $n$Lab
- [finite object](https://ncatlab.org/nlab/show/finite+object) at $n$Lab
- [Finite set](https://en.wikipedia.org/wiki/Finite_set) at Wikipedia
- [Finite set](https://www.wikidata.org/wiki/Q272404) at Wikidata
