# Minkowski multiplication on subsets of a semigroup

```agda
module group-theory.minkowski-multiplication-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.powersets
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups
open import group-theory.subsets-semigroups

open import logic.functoriality-existential-quantification
```

</details>

## Idea

Given two [subsets](group-theory.subsets-semigroups.md) `A` and `B` of a
[semigroup](group-theory.semigroups.md) `S`, the
{{#concept "Minkowski multiplication" Disambiguation="on subsets of a semigroup" WD="Minkowski addition" WDID=Q1322294 Agda=minkowski-mul-Semigroup}}
of `A` and `B` is the [set](foundation-core.sets.md) of elements that can be
formed by multiplying an element of `A` and an element of `B`. This binary
operation defines a semigroup structure on the
[powerset](foundation.powersets.md) of `S`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (G : Semigroup l1)
  (A : subset-Semigroup l2 G)
  (B : subset-Semigroup l3 G)
  where

  minkowski-mul-Semigroup : subset-Semigroup (l1 ⊔ l2 ⊔ l3) G
  minkowski-mul-Semigroup c = ∃
    ( type-Semigroup G × type-Semigroup G)
    ( λ (a , b) →
      A a ∧ B b ∧ Id-Prop (set-Semigroup G) c (mul-Semigroup G a b))
```

## Properties

### Minkowski multiplication on subsets of a semigroup is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1)
  (A : subset-Semigroup l2 G)
  (B : subset-Semigroup l3 G)
  (C : subset-Semigroup l4 G)
  where

  sim-associative-minkowski-mul-Semigroup :
    sim-subtype
      ( minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C)
      ( minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C))
  pr1 sim-associative-minkowski-mul-Semigroup x =
    elim-exists
      ( claim)
      ( λ (ab , c) (ab∈AB , c∈C , x=ab*c) →
        elim-exists
          ( claim)
          ( λ (a , b) (a∈A , b∈B , ab=a*b) →
            intro-exists
              ( a , mul-Semigroup G b c)
              ( a∈A ,
                intro-exists (b , c) (b∈B , c∈C , refl) ,
                ( equational-reasoning
                  x
                  ＝ mul-Semigroup G ab c by x=ab*c
                  ＝ mul-Semigroup G (mul-Semigroup G a b) c
                    by ap (mul-Semigroup' G c) ab=a*b
                  ＝ mul-Semigroup G a (mul-Semigroup G b c)
                    by associative-mul-Semigroup G a b c)))
          ( ab∈AB))
    where
      claim =
        minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C) x
  pr2 sim-associative-minkowski-mul-Semigroup x =
    elim-exists
      ( claim)
      ( λ (a , bc) (a∈A , bc∈BC , x=a*bc) →
        elim-exists
          ( claim)
          ( λ (b , c) (b∈B , c∈C , bc=b*c) →
            intro-exists
              ( mul-Semigroup G a b , c)
              ( intro-exists (a , b) (a∈A , b∈B , refl) ,
                c∈C ,
                ( equational-reasoning
                  x
                  ＝ mul-Semigroup G a bc by x=a*bc
                  ＝ mul-Semigroup G a (mul-Semigroup G b c)
                    by ap (mul-Semigroup G a) bc=b*c
                  ＝ mul-Semigroup G (mul-Semigroup G a b) c
                    by inv (associative-mul-Semigroup G a b c))))
          ( bc∈BC))
    where
      claim =
        minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C x

  associative-minkowski-mul-Semigroup :
    minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C ＝
    minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C)
  associative-minkowski-mul-Semigroup =
    eq-sim-subtype
      ( minkowski-mul-Semigroup G (minkowski-mul-Semigroup G A B) C)
      ( minkowski-mul-Semigroup G A (minkowski-mul-Semigroup G B C))
      ( sim-associative-minkowski-mul-Semigroup)
```

### Minkowski multiplication on subsets of a semigroup forms a semigroup

```agda
module _
  {l : Level}
  (G : Semigroup l)
  where

  semigroup-minkowski-mul-Semigroup : Semigroup (lsuc l)
  pr1 semigroup-minkowski-mul-Semigroup = subtype-Set l (type-Semigroup G)
  pr1 (pr2 semigroup-minkowski-mul-Semigroup) = minkowski-mul-Semigroup G
  pr2 (pr2 semigroup-minkowski-mul-Semigroup) =
    associative-minkowski-mul-Semigroup G
```

### The Minkowski multiplication of two inhabited subsets of a semigroup is inhabited

```agda
module _
  {l1 l2 l3 : Level}
  (G : Semigroup l1)
  (A : subset-Semigroup l2 G)
  (B : subset-Semigroup l3 G)
  where

  minkowski-mul-inhabited-is-inhabited-Semigroup :
    is-inhabited-subtype A →
    is-inhabited-subtype B →
    is-inhabited-subtype (minkowski-mul-Semigroup G A B)
  minkowski-mul-inhabited-is-inhabited-Semigroup =
    map-binary-exists
      ( is-in-subtype (minkowski-mul-Semigroup G A B))
      ( mul-Semigroup G)
      ( λ a b a∈A b∈B → intro-exists (a , b) (a∈A , b∈B , refl))
```

### Containment of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1)
  (B : subset-Semigroup l2 G)
  (A : subset-Semigroup l3 G)
  (A' : subset-Semigroup l4 G)
  where

  preserves-leq-left-minkowski-mul-Semigroup :
    A ⊆ A' → minkowski-mul-Semigroup G A B ⊆ minkowski-mul-Semigroup G A' B
  preserves-leq-left-minkowski-mul-Semigroup A⊆A' x =
    map-tot-exists (λ (a , b) → map-product (A⊆A' a) id)

  preserves-leq-right-minkowski-mul-Semigroup :
    A ⊆ A' → minkowski-mul-Semigroup G B A ⊆ minkowski-mul-Semigroup G B A'
  preserves-leq-right-minkowski-mul-Semigroup A⊆A' x =
    map-tot-exists (λ (b , a) → map-product id (map-product (A⊆A' a) id))
```

### Similarity of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Semigroup l1)
  (B : subset-Semigroup l2 G)
  (A : subset-Semigroup l3 G)
  (A' : subset-Semigroup l4 G)
  where

  preserves-sim-left-minkowski-mul-Semigroup :
    sim-subtype A A' →
    sim-subtype (minkowski-mul-Semigroup G A B) (minkowski-mul-Semigroup G A' B)
  pr1 (preserves-sim-left-minkowski-mul-Semigroup (A⊆A' , _)) =
    preserves-leq-left-minkowski-mul-Semigroup G B A A' A⊆A'
  pr2 (preserves-sim-left-minkowski-mul-Semigroup (_ , A'⊆A)) =
    preserves-leq-left-minkowski-mul-Semigroup G B A' A A'⊆A

  preserves-sim-right-minkowski-mul-Semigroup :
    sim-subtype A A' →
    sim-subtype (minkowski-mul-Semigroup G B A) (minkowski-mul-Semigroup G B A')
  pr1 (preserves-sim-right-minkowski-mul-Semigroup (A⊆A' , _)) =
    preserves-leq-right-minkowski-mul-Semigroup G B A A' A⊆A'
  pr2 (preserves-sim-right-minkowski-mul-Semigroup (_ , A'⊆A)) =
    preserves-leq-right-minkowski-mul-Semigroup G B A' A A'⊆A

module _
  {l1 l2 l3 l4 l5 : Level}
  (G : Semigroup l1)
  (A : subset-Semigroup l2 G)
  (A' : subset-Semigroup l3 G)
  (B : subset-Semigroup l4 G)
  (B' : subset-Semigroup l5 G)
  where

  preserves-sim-minkowski-mul-Semigroup :
    sim-subtype A A' →
    sim-subtype B B' →
    sim-subtype
      ( minkowski-mul-Semigroup G A B)
      ( minkowski-mul-Semigroup G A' B')
  preserves-sim-minkowski-mul-Semigroup A≈A' B≈B' =
    transitive-sim-subtype
      ( minkowski-mul-Semigroup G A B)
      ( minkowski-mul-Semigroup G A B')
      ( minkowski-mul-Semigroup G A' B')
      ( preserves-sim-left-minkowski-mul-Semigroup G B' A A' A≈A')
      ( preserves-sim-right-minkowski-mul-Semigroup G A B B' B≈B')
```

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
