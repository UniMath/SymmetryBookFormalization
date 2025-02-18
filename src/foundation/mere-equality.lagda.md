# Mere equality

```agda
module foundation.mere-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

Two elements in a type are said to be merely equal if there is an element of the
propositionally truncated identity type between them.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  mere-eq-Prop : A → A → Prop l
  mere-eq-Prop x y = trunc-Prop (x ＝ y)

  mere-eq : A → A → UU l
  mere-eq x y = type-Prop (mere-eq-Prop x y)

  is-prop-mere-eq : (x y : A) → is-prop (mere-eq x y)
  is-prop-mere-eq x y = is-prop-type-trunc-Prop
```

## Properties

### Reflexivity

```agda
refl-mere-eq : {l : Level} {A : UU l} → is-reflexive (mere-eq {l} {A})
refl-mere-eq a = unit-trunc-Prop refl

mere-eq-eq : {l : Level} {A : UU l} {x y : A} → x ＝ y → mere-eq x y
mere-eq-eq {x = x} refl = refl-mere-eq x
```

### Symmetry

```agda
abstract
  symmetric-mere-eq :
    {l : Level} {A : UU l} → is-symmetric (mere-eq {l} {A})
  symmetric-mere-eq _ _ = map-trunc-Prop inv
```

### Transitivity

```agda
abstract
  transitive-mere-eq :
    {l : Level} {A : UU l} → is-transitive (mere-eq {l} {A})
  transitive-mere-eq x y z p q =
    apply-universal-property-trunc-Prop q
      ( mere-eq-Prop x z)
      ( λ p' → map-trunc-Prop (p' ∙_) p)
```

### Mere equality is an equivalence relation

```agda
mere-eq-equivalence-relation :
  {l1 : Level} (A : UU l1) → equivalence-relation l1 A
pr1 (mere-eq-equivalence-relation A) = mere-eq-Prop
pr1 (pr2 (mere-eq-equivalence-relation A)) = refl-mere-eq
pr1 (pr2 (pr2 (mere-eq-equivalence-relation A))) = symmetric-mere-eq
pr2 (pr2 (pr2 (mere-eq-equivalence-relation A))) = transitive-mere-eq
```

### Any map into a set reflects mere equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  reflects-mere-eq :
    reflects-equivalence-relation (mere-eq-equivalence-relation A) f
  reflects-mere-eq {x} {y} r =
    apply-universal-property-trunc-Prop r
      ( Id-Prop X (f x) (f y))
      ( ap f)

  reflecting-map-mere-eq :
    reflecting-map-equivalence-relation
      ( mere-eq-equivalence-relation A)
      ( type-Set X)
  pr1 reflecting-map-mere-eq = f
  pr2 reflecting-map-mere-eq = reflects-mere-eq
```

### If mere equality maps into the identity type of `A`, then `A` is a set

```agda
is-set-mere-eq-in-id :
  {l : Level} {A : UU l} → ((x y : A) → mere-eq x y → x ＝ y) → is-set A
is-set-mere-eq-in-id =
  is-set-prop-in-id
    ( mere-eq)
    ( is-prop-mere-eq)
    ( refl-mere-eq)
```
