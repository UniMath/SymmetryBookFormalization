# π-finite types

```agda
module univalent-combinatorics.pi-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-function-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.maybe
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.set-truncations
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-many-connected-components
open import univalent-combinatorics.retracts-of-finite-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.untruncated-pi-finite-types
```

</details>

## Idea

A type is
{{#concept "πₙ-finite" Disambiguation="type" Agda=is-π-finite Agda=π-Finite-Type}}
if it has [finitely](univalent-combinatorics.finite-types.md) many
[connected components](foundation.connected-components.md), all of its homotopy
groups up to level `n` at all base points are finite, and all higher homotopy
groups are [trivial](group-theory.trivial-groups.md). A type is
{{#concept "π-finite"}} if it is πₙ-finite for some `n`.

## Definitions

### The πₙ-finiteness predicate

```agda
is-π-finite-Prop : {l : Level} (k : ℕ) → UU l → Prop l
is-π-finite-Prop zero-ℕ X = is-finite-Prop X
is-π-finite-Prop (succ-ℕ k) X =
  product-Prop
    ( has-finitely-many-connected-components-Prop X)
    ( Π-Prop X (λ x → Π-Prop X (λ y → is-π-finite-Prop k (x ＝ y))))

is-π-finite : {l : Level} (k : ℕ) → UU l → UU l
is-π-finite k A =
  type-Prop (is-π-finite-Prop k A)

is-prop-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-prop (is-π-finite k A)
is-prop-is-π-finite k {A} =
  is-prop-type-Prop (is-π-finite-Prop k A)

has-finitely-many-connected-components-is-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-π-finite k X → has-finitely-many-connected-components X
has-finitely-many-connected-components-is-π-finite zero-ℕ =
  has-finitely-many-connected-components-is-finite
has-finitely-many-connected-components-is-π-finite (succ-ℕ k) = pr1
```

### πₙ-finite types are n-truncated

```agda
is-trunc-is-π-finite :
  {l : Level} (k : ℕ) {X : UU l} →
  is-π-finite k X → is-trunc (truncation-level-ℕ k) X
is-trunc-is-π-finite zero-ℕ = is-set-is-finite
is-trunc-is-π-finite (succ-ℕ k) H x y =
  is-trunc-is-π-finite k (pr2 H x y)
```

### πₙ-finite types are untruncated πₙ-finite

```agda
is-untruncated-π-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} →
  is-π-finite k A → is-untruncated-π-finite k A
is-untruncated-π-finite-is-π-finite zero-ℕ H =
  is-finite-equiv
    ( equiv-unit-trunc-Set (_ , (is-set-is-finite H)))
    ( H)
pr1 (is-untruncated-π-finite-is-π-finite (succ-ℕ k) H) = pr1 H
pr2 (is-untruncated-π-finite-is-π-finite (succ-ℕ k) H) x y =
  is-untruncated-π-finite-is-π-finite k (pr2 H x y)
```

### The subuniverse πₙ-finite types

```agda
π-Finite-Type : (l : Level) (k : ℕ) → UU (lsuc l)
π-Finite-Type l k = Σ (UU l) (is-π-finite k)

module _
  {l : Level} (k : ℕ) (A : π-Finite-Type l k)
  where

  type-π-Finite-Type : UU l
  type-π-Finite-Type = pr1 A

  is-π-finite-type-π-Finite-Type : is-π-finite k type-π-Finite-Type
  is-π-finite-type-π-Finite-Type = pr2 A

  is-trunc-type-π-Finite-Type :
    is-trunc (truncation-level-ℕ k) type-π-Finite-Type
  is-trunc-type-π-Finite-Type =
    is-trunc-is-π-finite k is-π-finite-type-π-Finite-Type

  is-untruncated-π-finite-type-π-Finite-Type :
    is-untruncated-π-finite k type-π-Finite-Type
  is-untruncated-π-finite-type-π-Finite-Type =
    is-untruncated-π-finite-is-π-finite k is-π-finite-type-π-Finite-Type
```

## Properties

### Untruncated πₙ-finite n-truncated types are πₙ-finite

```agda
is-π-finite-is-untruncated-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-trunc (truncation-level-ℕ k) A →
  is-untruncated-π-finite k A → is-π-finite k A
is-π-finite-is-untruncated-π-finite zero-ℕ H K =
  is-finite-is-untruncated-π-finite zero-ℕ H K
pr1 (is-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) = pr1 K
pr2 (is-π-finite-is-untruncated-π-finite (succ-ℕ k) H K) x y =
  is-π-finite-is-untruncated-π-finite k (H x y) (pr2 K x y)
```

### πₙ-finite types are closed under retracts

```agda
is-π-finite-retract :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A retract-of B → is-π-finite k B → is-π-finite k A
is-π-finite-retract zero-ℕ = is-finite-retract
pr1 (is-π-finite-retract (succ-ℕ k) r H) =
  has-finitely-many-connected-components-retract
    ( r)
    ( has-finitely-many-connected-components-is-π-finite (succ-ℕ k) H)
pr2 (is-π-finite-retract (succ-ℕ k) r H) x y =
  is-π-finite-retract k
    ( retract-eq r x y)
    ( pr2 H (inclusion-retract r x) (inclusion-retract r y))
```

### π-finite types are closed under equivalences

```agda
is-π-finite-equiv :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-π-finite k B → is-π-finite k A
is-π-finite-equiv k e =
  is-π-finite-retract k (retract-equiv e)

is-π-finite-equiv' :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  A ≃ B → is-π-finite k A → is-π-finite k B
is-π-finite-equiv' k e =
  is-π-finite-retract k (retract-inv-equiv e)
```

### Empty types are π-finite

```agda
is-π-finite-empty : (k : ℕ) → is-π-finite k empty
is-π-finite-empty zero-ℕ = is-finite-empty
is-π-finite-empty (succ-ℕ k) =
  ( has-finitely-many-connected-components-empty , ind-empty)

empty-π-Finite-Type : (k : ℕ) → π-Finite-Type lzero k
empty-π-Finite-Type k = (empty , is-π-finite-empty k)

is-π-finite-is-empty :
  {l : Level} (k : ℕ) {A : UU l} → is-empty A → is-π-finite k A
is-π-finite-is-empty zero-ℕ = is-finite-is-empty
is-π-finite-is-empty (succ-ℕ k) f =
  ( has-finitely-many-connected-components-is-empty f , ex-falso ∘ f)
```

### Contractible types are π-finite

```agda
is-π-finite-is-contr :
  {l : Level} (k : ℕ) {A : UU l} → is-contr A → is-π-finite k A
is-π-finite-is-contr zero-ℕ =
  is-finite-is-contr
pr1 (is-π-finite-is-contr (succ-ℕ k) H) =
  has-finitely-many-connected-components-is-contr H
pr2 (is-π-finite-is-contr (succ-ℕ k) H) x y =
  is-π-finite-is-contr k (is-prop-is-contr H x y)

is-π-finite-unit : (k : ℕ) → is-π-finite k unit
is-π-finite-unit k =
  is-π-finite-is-contr k is-contr-unit

unit-π-Finite-Type : (k : ℕ) → π-Finite-Type lzero k
unit-π-Finite-Type k =
  ( unit , is-π-finite-unit k)
```

### Coproducts of π-finite types are π-finite

```agda
is-π-finite-coproduct :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : UU l2} →
  is-π-finite k A → is-π-finite k B →
  is-π-finite k (A + B)
is-π-finite-coproduct k hA hB =
  is-π-finite-is-untruncated-π-finite k
    ( is-trunc-coproduct
      ( truncation-level-minus-two-ℕ k)
      ( is-trunc-is-π-finite k hA)
      ( is-trunc-is-π-finite k hB))
    ( is-untruncated-π-finite-coproduct k
      ( is-untruncated-π-finite-is-π-finite k hA)
      ( is-untruncated-π-finite-is-π-finite k hB))

coproduct-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) →
  π-Finite-Type l1 k →
  π-Finite-Type l2 k →
  π-Finite-Type (l1 ⊔ l2) k
pr1 (coproduct-π-Finite-Type k A B) =
  (type-π-Finite-Type k A + type-π-Finite-Type k B)
pr2 (coproduct-π-Finite-Type k A B) =
  is-π-finite-coproduct k
    ( is-π-finite-type-π-Finite-Type k A)
    ( is-π-finite-type-π-Finite-Type k B)
```

### `Maybe A` of any π-finite type `A` is π-finite

```agda
is-π-finite-Maybe :
  {l : Level} (k : ℕ) {A : UU l} → is-π-finite k A → is-π-finite k (Maybe A)
is-π-finite-Maybe k H = is-π-finite-coproduct k H (is-π-finite-unit k)

Maybe-π-Finite-Type :
  {l : Level} (k : ℕ) → π-Finite-Type l k → π-Finite-Type l k
Maybe-π-Finite-Type k A = coproduct-π-Finite-Type k A (unit-π-Finite-Type k)
```

### Any standard finite type is π-finite

```agda
is-π-finite-Fin : (k n : ℕ) → is-π-finite k (Fin n)
is-π-finite-Fin k zero-ℕ = is-π-finite-empty k
is-π-finite-Fin k (succ-ℕ n) = is-π-finite-Maybe k (is-π-finite-Fin k n)

Fin-π-Finite-Type : (k : ℕ) (n : ℕ) → π-Finite-Type lzero k
Fin-π-Finite-Type k n = (Fin n , is-π-finite-Fin k n)
```

### Any type equipped with a counting is π-finite

```agda
is-π-finite-count : {l : Level} (k : ℕ) {A : UU l} → count A → is-π-finite k A
is-π-finite-count k (n , e) = is-π-finite-equiv' k e (is-π-finite-Fin k n)
```

### Any finite type is π-finite

```agda
is-π-finite-is-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-finite A → is-π-finite k A
is-π-finite-is-finite k {A} H =
  apply-universal-property-trunc-Prop H
    ( is-π-finite-Prop k A)
    ( is-π-finite-count k)

π-finite-Finite-Type : {l : Level} (k : ℕ) → Finite-Type l → π-Finite-Type l k
π-finite-Finite-Type k A =
  ( type-Finite-Type A , is-π-finite-is-finite k (is-finite-type-Finite-Type A))
```

### π-finite sets are finite

```agda
is-finite-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-set A → is-π-finite k A → is-finite A
is-finite-is-π-finite k H K =
  is-finite-equiv'
    ( equiv-unit-trunc-Set (_ , H))
    ( has-finitely-many-connected-components-is-π-finite k K)
```

### πₙ-finite types are πₙ₊₁-finite

```agda
is-π-finite-succ-is-π-finite :
  {l : Level} (k : ℕ) {A : UU l} → is-π-finite k A → is-π-finite (succ-ℕ k) A
is-π-finite-succ-is-π-finite zero-ℕ =
  is-π-finite-is-finite 1
is-π-finite-succ-is-π-finite (succ-ℕ k) (H , K) =
  ( H , (λ x y → is-π-finite-succ-is-π-finite k (K x y)))
```

### The type of all `n`-element types in `UU l` is π₁-finite

```agda
is-π-finite-Type-With-Cardinality-ℕ :
  {l : Level} (n : ℕ) → is-π-finite 1 (Type-With-Cardinality-ℕ l n)
is-π-finite-Type-With-Cardinality-ℕ n =
  is-π-finite-is-untruncated-π-finite 1
    ( is-1-type-Type-With-Cardinality-ℕ n)
    ( is-untruncated-π-finite-Type-With-Cardinality-ℕ 1 n)

Type-With-Cardinality-ℕ-π-Finite-Type :
  (l : Level) (n : ℕ) → π-Finite-Type (lsuc l) 1
Type-With-Cardinality-ℕ-π-Finite-Type l n =
  (Type-With-Cardinality-ℕ l n , is-π-finite-Type-With-Cardinality-ℕ n)
```

### Finite products of π-finite types are π-finite

```agda
is-π-finite-Π :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-finite A → ((a : A) → is-π-finite k (B a)) →
  is-π-finite k ((a : A) → B a)
is-π-finite-Π k hA hB =
  is-π-finite-is-untruncated-π-finite k
    ( is-trunc-Π (truncation-level-ℕ k) (is-trunc-is-π-finite k ∘ hB))
    ( is-untruncated-π-finite-Π k hA
      ( is-untruncated-π-finite-is-π-finite k ∘ hB))

finite-Π-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) (A : Finite-Type l1)
  (B : type-Finite-Type A → π-Finite-Type l2 k) →
  π-Finite-Type (l1 ⊔ l2) k
pr1 (finite-Π-π-Finite-Type k A B) =
  (x : type-Finite-Type A) → (type-π-Finite-Type k (B x))
pr2 (finite-Π-π-Finite-Type k A B) =
  is-π-finite-Π k
    ( is-finite-type-Finite-Type A)
      ( λ x → is-π-finite-type-π-Finite-Type k (B x))
```

### Dependent sums of π-finite types are π-finite

```agda
is-π-finite-Σ :
  {l1 l2 : Level} (k : ℕ) {A : UU l1} {B : A → UU l2} →
  is-π-finite k A → ((a : A) → is-π-finite k (B a)) →
  is-π-finite k (Σ A B)
is-π-finite-Σ k hA hB =
  is-π-finite-is-untruncated-π-finite k
    ( is-trunc-Σ
      ( is-trunc-is-π-finite k hA)
      ( is-trunc-is-π-finite k ∘ hB))
    ( is-untruncated-π-finite-Σ k
      ( is-untruncated-π-finite-is-π-finite (succ-ℕ k)
        ( is-π-finite-succ-is-π-finite k hA))
      ( is-untruncated-π-finite-is-π-finite k ∘ hB))

Σ-π-Finite-Type :
  {l1 l2 : Level} (k : ℕ) (A : π-Finite-Type l1 k)
  (B : type-π-Finite-Type k A → π-Finite-Type l2 k) →
  π-Finite-Type (l1 ⊔ l2) k
pr1 (Σ-π-Finite-Type k A B) =
  Σ (type-π-Finite-Type k A) (type-π-Finite-Type k ∘ B)
pr2 (Σ-π-Finite-Type k A B) =
  is-π-finite-Σ k
    ( is-π-finite-type-π-Finite-Type k A)
    ( is-π-finite-type-π-Finite-Type k ∘ B)
```

## See also

- [Unbounded π-finite types](univalent-combinatorics.unbounded-pi-finite-types.md)

## External links

- [pi-finite type](https://ncatlab.org/nlab/show/pi-finite+type) at $n$Lab
