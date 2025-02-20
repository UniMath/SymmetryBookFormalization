# Dependent products of large inflattices

```agda
module order-theory.dependent-products-large-inflattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-inflattices
open import order-theory.large-posets
```

</details>

## Idea

Families of greatest lower bounds of families of elements in dependent products
of large posets are again greatest lower bounds. Therefore it follows that
dependent products of large inflattices are again large inflattices.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {l1 : Level} {I : UU l1} (L : I → Large-Inflattice α β γ)
  where

  large-poset-Π-Large-Inflattice :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Π-Large-Inflattice =
    Π-Large-Poset (λ i → large-poset-Large-Inflattice (L i))

  is-large-inflattice-Π-Large-Inflattice :
    is-large-inflattice-Large-Poset γ large-poset-Π-Large-Inflattice
  inf-has-greatest-lower-bound-family-of-elements-Large-Poset
    ( is-large-inflattice-Π-Large-Inflattice {l2} {l3} {J} a) i =
    inf-Large-Inflattice (L i) (λ j → a j i)
  is-greatest-lower-bound-inf-has-greatest-lower-bound-family-of-elements-Large-Poset
    ( is-large-inflattice-Π-Large-Inflattice {l2} {l3} {J} a) =
    is-greatest-lower-bound-Π-Large-Poset
      ( λ i → large-poset-Large-Inflattice (L i))
      ( a)
      ( λ i → inf-Large-Inflattice (L i) (λ j → a j i))
      ( λ i →
        is-greatest-lower-bound-inf-Large-Inflattice (L i) (λ j → a j i))

  Π-Large-Inflattice :
    Large-Inflattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-poset-Large-Inflattice Π-Large-Inflattice =
    large-poset-Π-Large-Inflattice
  is-large-inflattice-Large-Inflattice Π-Large-Inflattice =
    is-large-inflattice-Π-Large-Inflattice

  set-Π-Large-Inflattice : (l : Level) → Set (α l ⊔ l1)
  set-Π-Large-Inflattice =
    set-Large-Inflattice Π-Large-Inflattice

  type-Π-Large-Inflattice : (l : Level) → UU (α l ⊔ l1)
  type-Π-Large-Inflattice =
    type-Large-Inflattice Π-Large-Inflattice

  is-set-type-Π-Large-Inflattice :
    {l : Level} → is-set (type-Π-Large-Inflattice l)
  is-set-type-Π-Large-Inflattice =
    is-set-type-Large-Inflattice Π-Large-Inflattice

  leq-prop-Π-Large-Inflattice :
    Large-Relation-Prop
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Inflattice)
  leq-prop-Π-Large-Inflattice =
    leq-prop-Large-Inflattice Π-Large-Inflattice

  leq-Π-Large-Inflattice :
    {l2 l3 : Level}
    (x : type-Π-Large-Inflattice l2) (y : type-Π-Large-Inflattice l3) →
    UU (β l2 l3 ⊔ l1)
  leq-Π-Large-Inflattice =
    leq-Large-Inflattice Π-Large-Inflattice

  is-prop-leq-Π-Large-Inflattice :
    is-prop-Large-Relation type-Π-Large-Inflattice leq-Π-Large-Inflattice
  is-prop-leq-Π-Large-Inflattice =
    is-prop-leq-Large-Inflattice Π-Large-Inflattice

  refl-leq-Π-Large-Inflattice :
    is-reflexive-Large-Relation type-Π-Large-Inflattice leq-Π-Large-Inflattice
  refl-leq-Π-Large-Inflattice =
    refl-leq-Large-Inflattice Π-Large-Inflattice

  antisymmetric-leq-Π-Large-Inflattice :
    is-antisymmetric-Large-Relation
      ( type-Π-Large-Inflattice)
      ( leq-Π-Large-Inflattice)
  antisymmetric-leq-Π-Large-Inflattice =
    antisymmetric-leq-Large-Inflattice Π-Large-Inflattice

  transitive-leq-Π-Large-Inflattice :
    is-transitive-Large-Relation
      ( type-Π-Large-Inflattice)
      ( leq-Π-Large-Inflattice)
  transitive-leq-Π-Large-Inflattice =
    transitive-leq-Large-Inflattice Π-Large-Inflattice

  inf-Π-Large-Inflattice :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Inflattice l3) →
    type-Π-Large-Inflattice (γ ⊔ l2 ⊔ l3)
  inf-Π-Large-Inflattice =
    inf-Large-Inflattice Π-Large-Inflattice

  is-lower-bound-family-of-elements-Π-Large-Inflattice :
    {l2 l3 l4 : Level} {J : UU l2} (x : J → type-Π-Large-Inflattice l3)
    (y : type-Π-Large-Inflattice l4) → UU (β l4 l3 ⊔ l1 ⊔ l2)
  is-lower-bound-family-of-elements-Π-Large-Inflattice =
    is-lower-bound-family-of-elements-Large-Inflattice Π-Large-Inflattice

  is-greatest-lower-bound-family-of-elements-Π-Large-Inflattice :
    {l2 l3 l4 : Level} {J : UU l2} (x : J → type-Π-Large-Inflattice l3) →
    type-Π-Large-Inflattice l4 → UUω
  is-greatest-lower-bound-family-of-elements-Π-Large-Inflattice =
    is-greatest-lower-bound-family-of-elements-Large-Inflattice
      ( Π-Large-Inflattice)

  is-greatest-lower-bound-inf-Π-Large-Inflattice :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Inflattice l3) →
    is-greatest-lower-bound-family-of-elements-Π-Large-Inflattice x
      ( inf-Π-Large-Inflattice x)
  is-greatest-lower-bound-inf-Π-Large-Inflattice =
    is-greatest-lower-bound-inf-Large-Inflattice Π-Large-Inflattice
```
