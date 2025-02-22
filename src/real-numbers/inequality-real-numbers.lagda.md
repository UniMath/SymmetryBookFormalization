# Inequality on the real numbers

```agda
module real-numbers.inequality-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets
open import order-theory.preorders

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "standard ordering" Disambiguation="real numbers" Agda=leq-ℝ}} on
the [real numbers](real-numbers.dedekind-real-numbers.md) is defined as the
lower cut of one being a subset of the lower cut of the other. This is the
definition used in {{#cite UF13}}, section 11.2.1.

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-ℝ-Prop = leq-lower-ℝ-Prop (lower-real-ℝ x) (lower-real-ℝ y)

  leq-ℝ : UU (l1 ⊔ l2)
  leq-ℝ = type-Prop leq-ℝ-Prop
```

## Properties

### Equivalence with inequality on upper cuts

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  leq-ℝ-Prop' : Prop (l1 ⊔ l2)
  leq-ℝ-Prop' = leq-upper-ℝ-Prop (upper-real-ℝ x) (upper-real-ℝ y)

  leq-ℝ' : UU (l1 ⊔ l2)
  leq-ℝ' = type-Prop leq-ℝ-Prop'

  leq-iff-ℝ' : leq-ℝ x y ↔ leq-ℝ'
  pr1 leq-iff-ℝ' x≤y q y<q =
    elim-exists
      ( upper-cut-ℝ x q)
      ( λ p (p<q , p≮y) →
        subset-upper-cut-upper-complement-lower-cut-ℝ
          ( x)
          ( q)
          ( intro-exists
            ( p)
            ( p<q ,
              reverses-order-complement-subtype
                ( lower-cut-ℝ x)
                ( lower-cut-ℝ y)
                ( x≤y)
                ( p)
                ( p≮y))))
      ( subset-upper-complement-lower-cut-upper-cut-ℝ y q y<q)
  pr2 leq-iff-ℝ' uy⊆ux p p<x =
    elim-exists
      ( lower-cut-ℝ y p)
      ( λ q (p<q , x≮q) →
        subset-lower-cut-lower-complement-upper-cut-ℝ
          ( y)
          ( p)
          ( intro-exists
            ( q)
            ( p<q ,
              reverses-order-complement-subtype
                ( upper-cut-ℝ y)
                ( upper-cut-ℝ x)
                ( uy⊆ux)
                ( q)
                ( x≮q))))
      ( subset-lower-complement-upper-cut-lower-cut-ℝ x p p<x)
```

### Inequality on the real numbers is reflexive

```agda
refl-leq-ℝ : {l : Level} → (x : ℝ l) → leq-ℝ x x
refl-leq-ℝ x = refl-leq-Large-Preorder lower-ℝ-Large-Preorder (lower-real-ℝ x)
```

### Inequality on the real numbers is antisymmetric

```agda
antisymmetric-leq-ℝ : {l : Level} → (x y : ℝ l) → leq-ℝ x y → leq-ℝ y x → x ＝ y
antisymmetric-leq-ℝ x y x≤y y≤x =
  eq-eq-lower-cut-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) x≤y y≤x)
```

### Inequality on the real numbers is transitive

```agda
module _
  {l1 l2 l3 : Level}
  (x : ℝ l1)
  (y : ℝ l2)
  (z : ℝ l3)
  where

  transitive-leq-ℝ : leq-ℝ y z → leq-ℝ x y → leq-ℝ x z
  transitive-leq-ℝ =
    transitive-leq-subtype (lower-cut-ℝ x) (lower-cut-ℝ y) (lower-cut-ℝ z)
```

### The large preorder of real numbers

```agda
ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder ℝ-Large-Preorder = ℝ
leq-prop-Large-Preorder ℝ-Large-Preorder = leq-ℝ-Prop
refl-leq-Large-Preorder ℝ-Large-Preorder = refl-leq-ℝ
transitive-leq-Large-Preorder ℝ-Large-Preorder = transitive-leq-ℝ
```

### The large poset of real numbers

```agda
ℝ-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset ℝ-Large-Poset = ℝ-Large-Preorder
antisymmetric-leq-Large-Poset ℝ-Large-Poset = antisymmetric-leq-ℝ
```

### The partially ordered set of reals at a specific level

```agda
ℝ-Preorder : (l : Level) → Preorder (lsuc l) l
ℝ-Preorder = preorder-Large-Preorder ℝ-Large-Preorder

ℝ-Poset : (l : Level) → Poset (lsuc l) l
ℝ-Poset = poset-Large-Poset ℝ-Large-Poset
```

### The canonical map from rational numbers to the reals preserves and reflects inequality

```agda
preserves-leq-real-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℝ (real-ℚ x) (real-ℚ y)
preserves-leq-real-ℚ = preserves-leq-lower-real-ℚ

reflects-leq-real-ℚ : (x y : ℚ) → leq-ℝ (real-ℚ x) (real-ℚ y) → leq-ℚ x y
reflects-leq-real-ℚ = reflects-leq-lower-real-ℚ

iff-leq-real-ℚ : (x y : ℚ) → leq-ℚ x y ↔ leq-ℝ (real-ℚ x) (real-ℚ y)
iff-leq-real-ℚ = iff-leq-lower-real-ℚ
```

### Inequality on the real numbers is invariant under similarity

```agda
module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3) (x~y : sim-ℝ x y)
  where

  opaque
    unfolding sim-ℝ

    preserves-leq-left-sim-ℝ : leq-ℝ x z → leq-ℝ y z
    preserves-leq-left-sim-ℝ lx⊆lz q q<y = lx⊆lz q (pr2 x~y q q<y)

    preserves-leq-right-sim-ℝ : leq-ℝ z x → leq-ℝ z y
    preserves-leq-right-sim-ℝ lz⊆lx q q<z = pr1 x~y q (lz⊆lx q q<z)

module _
  {l1 l2 l3 l4 : Level}
  (x1 : ℝ l1) (x2 : ℝ l2) (y1 : ℝ l3) (y2 : ℝ l4)
  (x1~x2 : sim-ℝ x1 x2) (y1~y2 : sim-ℝ y1 y2)
  where

  preserves-leq-sim-ℝ : leq-ℝ x1 y1 → leq-ℝ x2 y2
  preserves-leq-sim-ℝ x1≤y1 =
    preserves-leq-left-sim-ℝ
      ( y2)
      ( x1)
      ( x2)
      ( x1~x2)
      ( preserves-leq-right-sim-ℝ x1 y1 y2 y1~y2 x1≤y1)
```

### Inequality on the real numbers is invariant by translation

```agda
module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  preserves-leq-right-add-ℝ :
    leq-ℝ x y → leq-ℝ (x +ℝ z) (y +ℝ z)
  preserves-leq-right-add-ℝ lx⊆ly q =
    map-tot-exists (λ (qx , _) → map-product (lx⊆ly qx) id)

  preserves-leq-left-add-ℝ :
    leq-ℝ x y → leq-ℝ (z +ℝ x) (z +ℝ y)
  preserves-leq-left-add-ℝ lx⊆ly q =
    map-tot-exists (λ (_ , qx) → map-product id (map-product (lx⊆ly qx) id))

module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  reflects-leq-right-add-ℝ : leq-ℝ (x +ℝ z) (y +ℝ z) → leq-ℝ x y
  reflects-leq-right-add-ℝ x+z≤y+z =
    preserves-leq-sim-ℝ
      ( (x +ℝ z) +ℝ neg-ℝ z)
      ( x)
      ( (y +ℝ z) +ℝ neg-ℝ z)
      ( y)
      ( cancel-right-add-diff-ℝ x z)
      ( cancel-right-add-diff-ℝ y z)
      ( preserves-leq-right-add-ℝ (neg-ℝ z) (x +ℝ z) (y +ℝ z) x+z≤y+z)

  reflects-leq-left-add-ℝ : leq-ℝ (z +ℝ x) (z +ℝ y) → leq-ℝ x y
  reflects-leq-left-add-ℝ z+x≤z+y =
    reflects-leq-right-add-ℝ
      ( binary-tr leq-ℝ (commutative-add-ℝ z x) (commutative-add-ℝ z y) z+x≤z+y)

module _
  {l1 l2 l3 : Level}
  (z : ℝ l1) (x : ℝ l2) (y : ℝ l3)
  where

  iff-leq-right-add-ℝ : leq-ℝ x y ↔ leq-ℝ (x +ℝ z) (y +ℝ z)
  pr1 iff-leq-right-add-ℝ = preserves-leq-right-add-ℝ z x y
  pr2 iff-leq-right-add-ℝ = reflects-leq-right-add-ℝ z x y

  iff-leq-left-add-ℝ : leq-ℝ x y ↔ leq-ℝ (z +ℝ x) (z +ℝ y)
  pr1 iff-leq-left-add-ℝ = preserves-leq-left-add-ℝ z x y
  pr2 iff-leq-left-add-ℝ = reflects-leq-left-add-ℝ z x y
```

### Negation reverses the ordering of inequality on real numbers

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  neg-leq-ℝ : leq-ℝ x y → leq-ℝ (neg-ℝ y) (neg-ℝ x)
  neg-leq-ℝ x≤y p = forward-implication (leq-iff-ℝ' x y) x≤y (neg-ℚ p)
```

### `x + y ≤ z` if and only if `x ≤ y - z`

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  iff-diff-right-leq-ℝ : leq-ℝ (x +ℝ y) z ↔ leq-ℝ x (z -ℝ y)
  pr1 iff-diff-right-leq-ℝ x+y<z =
    preserves-leq-left-sim-ℝ
      ( z -ℝ y)
      ( (x +ℝ y) -ℝ y)
      ( x)
      ( cancel-right-add-diff-ℝ x y)
      ( preserves-leq-right-add-ℝ (neg-ℝ y) (x +ℝ y) z x+y<z)
  pr2 iff-diff-right-leq-ℝ x<z-y =
    preserves-leq-right-sim-ℝ
      ( x +ℝ y)
      ( (z -ℝ y) +ℝ y)
      ( z)
      ( cancel-right-diff-add-ℝ z y)
      ( preserves-leq-right-add-ℝ y x (z -ℝ y) x<z-y)

module _
  {l1 l2 l3 : Level} (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  iff-add-right-leq-ℝ : leq-ℝ (x -ℝ y) z ↔ leq-ℝ x (z +ℝ y)
  iff-add-right-leq-ℝ =
    tr
      ( λ w → leq-ℝ (x -ℝ y) z ↔ leq-ℝ x (z +ℝ w))
      ( neg-neg-ℝ y)
      ( iff-diff-right-leq-ℝ x (neg-ℝ y) z)
```

## References

{{#bibliography}}
