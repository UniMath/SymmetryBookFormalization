# Type arithmetic for cartesian product types

```agda
module foundation.type-arithmetic-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

We prove laws for the manipulation of cartesian products with respect to
themselves and dependent pair types.

## Laws

### Commutativity of cartesian products

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-product : A × B → B × A
  pr1 (map-commutative-product (pair a b)) = b
  pr2 (map-commutative-product (pair a b)) = a

  map-inv-commutative-product : B × A → A × B
  pr1 (map-inv-commutative-product (pair b a)) = a
  pr2 (map-inv-commutative-product (pair b a)) = b

  is-section-map-inv-commutative-product :
    (map-commutative-product ∘ map-inv-commutative-product) ~ id
  is-section-map-inv-commutative-product (pair b a) = refl

  is-retraction-map-inv-commutative-product :
    (map-inv-commutative-product ∘ map-commutative-product) ~ id
  is-retraction-map-inv-commutative-product (pair a b) = refl

  is-equiv-map-commutative-product : is-equiv map-commutative-product
  is-equiv-map-commutative-product =
    is-equiv-is-invertible
      map-inv-commutative-product
      is-section-map-inv-commutative-product
      is-retraction-map-inv-commutative-product

  commutative-product : (A × B) ≃ (B × A)
  pr1 commutative-product = map-commutative-product
  pr2 commutative-product = is-equiv-map-commutative-product
```

### Associativity of cartesian products

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-associative-product : (A × B) × C → A × (B × C)
  map-associative-product = map-associative-Σ A (λ _ → B) (λ _ → C)

  map-inv-associative-product : A × (B × C) → (A × B) × C
  map-inv-associative-product = map-inv-associative-Σ A (λ _ → B) (λ _ → C)

  is-section-map-inv-associative-product :
    (map-associative-product ∘ map-inv-associative-product) ~ id
  is-section-map-inv-associative-product =
    is-section-map-inv-associative-Σ A (λ _ → B) (λ _ → C)

  is-retraction-map-inv-associative-product :
    (map-inv-associative-product ∘ map-associative-product) ~ id
  is-retraction-map-inv-associative-product =
    is-retraction-map-inv-associative-Σ A (λ _ → B) (λ _ → C)

  is-equiv-map-associative-product : is-equiv map-associative-product
  is-equiv-map-associative-product =
    is-equiv-map-associative-Σ A (λ _ → B) (λ _ → C)

  associative-product : ((A × B) × C) ≃ (A × (B × C))
  associative-product = associative-Σ A (λ _ → B) (λ _ → C)
```

### The unit laws of cartesian product types with respect to contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-B : is-contr B)
  where

  right-unit-law-product-is-contr : A × B ≃ A
  right-unit-law-product-is-contr = right-unit-law-Σ-is-contr (λ _ → is-contr-B)

  inv-right-unit-law-product-is-contr : A ≃ A × B
  inv-right-unit-law-product-is-contr =
    inv-equiv right-unit-law-product-is-contr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : A → is-contr B)
  where

  right-unit-law-product-is-contr' : A × B ≃ A
  right-unit-law-product-is-contr' = right-unit-law-Σ-is-contr H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (is-contr-A : is-contr A)
  where

  left-unit-law-product-is-contr : A × B ≃ B
  left-unit-law-product-is-contr =
    left-unit-law-Σ-is-contr is-contr-A (center is-contr-A)

  inv-left-unit-law-product-is-contr : B ≃ A × B
  inv-left-unit-law-product-is-contr = inv-equiv left-unit-law-product-is-contr

  is-equiv-pr2-product-is-contr : is-equiv (pr2 {B = λ _ → B})
  is-equiv-pr2-product-is-contr =
    is-equiv-comp
      ( pr1)
      ( map-commutative-product)
      ( is-equiv-map-commutative-product)
      ( is-equiv-pr1-is-contr (λ _ → is-contr-A))

  equiv-pr2-product-is-contr : (A × B) ≃ B
  pr1 equiv-pr2-product-is-contr = pr2
  pr2 equiv-pr2-product-is-contr = is-equiv-pr2-product-is-contr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : B → is-contr A)
  where

  left-unit-law-product-is-contr' : A × B ≃ B
  left-unit-law-product-is-contr' =
    right-unit-law-product-is-contr' H ∘e commutative-product
```

### Adding redundant properties

```agda
equiv-add-redundant-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-prop B → (f : A → B) → A ≃ A × B
pr1 (equiv-add-redundant-prop is-prop-B f) a = a , f a
pr2 (equiv-add-redundant-prop is-prop-B f) =
  is-equiv-is-invertible
    ( pr1)
    ( λ p → eq-pair refl (eq-is-prop is-prop-B))
    ( refl-htpy)
```

## See also

- Functorial properties of cartesian products are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- The universal property of cartesian product types is treated in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).
- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
  - Arithmetical laws involving dependent product types are recorded in
    [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Arithmetical laws involving coproduct types are recorded in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).
- Arithmetical laws involving the unit type are recorded in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).
- Arithmetical laws involving the empty type are recorded in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).
