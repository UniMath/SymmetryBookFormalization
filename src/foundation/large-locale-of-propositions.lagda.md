# The large locale of propositions

```agda
module foundation.large-locale-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.functions
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.largest-elements-large-posets
open import order-theory.least-upper-bounds-large-posets
```

</details>

## Idea

The types of propositions `Prop l` combined form a
[large locale](order-theory.large-locales.md).

## Definitions

### The large preorder of propositions

```agda
Prop-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder Prop-Large-Preorder = Prop
leq-Large-Preorder-Prop Prop-Large-Preorder = hom-Prop
refl-leq-Large-Preorder Prop-Large-Preorder P = id
transitive-leq-Large-Preorder Prop-Large-Preorder P Q R g f = g ∘ f
```

### The large poset of propositions

```agda
Prop-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset Prop-Large-Poset = Prop-Large-Preorder
antisymmetric-leq-Large-Poset Prop-Large-Poset P Q = eq-iff
```

### Meets in the large poset of propositions

```agda
has-meets-Prop-Large-Locale :
  has-meets-Large-Poset Prop-Large-Poset
meet-has-meets-Large-Poset has-meets-Prop-Large-Locale = conj-Prop
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-Prop-Large-Locale =
  iff-universal-property-conj-Prop
```

### The largest element in the large poset of propositions

```agda
has-largest-element-Prop-Large-Locale :
  has-largest-element-Large-Poset Prop-Large-Poset
top-has-largest-element-Large-Poset
  has-largest-element-Prop-Large-Locale = unit-Prop
is-largest-element-top-has-largest-element-Large-Poset
  has-largest-element-Prop-Large-Locale P p =
  star
```

### The large poset of propositions is a large meet-semilattice

```agda
is-large-meet-semilattice-Prop-Large-Locale :
  is-large-meet-semilattice-Large-Poset Prop-Large-Poset
has-meets-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale =
  has-meets-Prop-Large-Locale
has-largest-element-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-Prop-Large-Locale =
  has-largest-element-Prop-Large-Locale
```

### Suprema in the large poset of propositions

```agda
is-large-suplattice-Prop-Large-Locale :
  is-large-suplattice-Large-Poset Prop-Large-Poset
sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) =
  exists-Prop I P
is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
  ( is-large-suplattice-Prop-Large-Locale {I = I} P) =
  is-least-upper-bound-exists-Prop P
```

### The large locale of propositions

```agda
Prop-Large-Locale : Large-Locale lsuc _⊔_
large-poset-Large-Locale Prop-Large-Locale =
  Prop-Large-Poset
is-large-meet-semilattice-Large-Locale Prop-Large-Locale =
  is-large-meet-semilattice-Prop-Large-Locale
is-large-suplattice-Large-Locale Prop-Large-Locale =
  is-large-suplattice-Prop-Large-Locale
distributive-meet-sup-Large-Locale Prop-Large-Locale =
  distributive-conj-exists-Prop
```
