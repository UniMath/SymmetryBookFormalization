# Counting in type theory

```agda
module univalent-combinatorics.counting where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import logic.propositionally-decidable-types

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The elements of a type `X` can be counted by establishing an equivalence
`Fin n ≃ X`.

## Definition

```agda
count : {l : Level} → UU l → UU l
count X = Σ ℕ (λ k → Fin k ≃ X)

module _
  {l : Level} {X : UU l} (e : count X)
  where

  number-of-elements-count : ℕ
  number-of-elements-count = pr1 e

  equiv-count : Fin number-of-elements-count ≃ X
  equiv-count = pr2 e

  map-equiv-count : Fin number-of-elements-count → X
  map-equiv-count = map-equiv equiv-count

  map-inv-equiv-count : X → Fin number-of-elements-count
  map-inv-equiv-count = map-inv-equiv equiv-count

  is-section-map-inv-equiv-count : (map-equiv-count ∘ map-inv-equiv-count) ~ id
  is-section-map-inv-equiv-count = is-section-map-inv-equiv equiv-count

  is-retraction-map-inv-equiv-count :
    (map-inv-equiv-count ∘ map-equiv-count) ~ id
  is-retraction-map-inv-equiv-count = is-retraction-map-inv-equiv equiv-count

  inv-equiv-count : X ≃ Fin number-of-elements-count
  inv-equiv-count = inv-equiv equiv-count

  is-set-count : is-set X
  is-set-count =
    is-set-equiv'
      ( Fin number-of-elements-count)
      ( equiv-count)
      ( is-set-Fin number-of-elements-count)
```

## Properties

### The elements of the standard finite types can be counted

```agda
count-Fin : (k : ℕ) → count (Fin k)
pr1 (count-Fin k) = k
pr2 (count-Fin k) = id-equiv
```

### Types equipped with countings are closed under equivalences

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  abstract
    equiv-count-equiv :
      (e : X ≃ Y) (f : count X) → Fin (number-of-elements-count f) ≃ Y
    equiv-count-equiv e f = e ∘e (equiv-count f)

  count-equiv : X ≃ Y → count X → count Y
  pr1 (count-equiv e f) = number-of-elements-count f
  pr2 (count-equiv e f) = equiv-count-equiv e f

  abstract
    equiv-count-equiv' :
      (e : X ≃ Y) (f : count Y) → Fin (number-of-elements-count f) ≃ X
    equiv-count-equiv' e f = inv-equiv e ∘e (equiv-count f)

  count-equiv' : X ≃ Y → count Y → count X
  pr1 (count-equiv' e f) = number-of-elements-count f
  pr2 (count-equiv' e f) = equiv-count-equiv' e f

  count-is-equiv : {f : X → Y} → is-equiv f → count X → count Y
  count-is-equiv H = count-equiv (pair _ H)

  count-is-equiv' :
    {f : X → Y} → is-equiv f → count Y → count X
  count-is-equiv' H = count-equiv' (pair _ H)
```

### A type as 0 elements if and only if it is empty

```agda
abstract
  is-empty-is-zero-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-zero-ℕ (number-of-elements-count e) → is-empty X
  is-empty-is-zero-number-of-elements-count (pair .zero-ℕ e) refl x =
    map-inv-equiv e x

abstract
  is-zero-number-of-elements-count-is-empty :
    {l : Level} {X : UU l} (e : count X) →
    is-empty X → is-zero-ℕ (number-of-elements-count e)
  is-zero-number-of-elements-count-is-empty (pair zero-ℕ e) H = refl
  is-zero-number-of-elements-count-is-empty (pair (succ-ℕ k) e) H =
    ex-falso (H (map-equiv e (zero-Fin k)))

count-is-empty :
  {l : Level} {X : UU l} → is-empty X → count X
pr1 (count-is-empty H) = zero-ℕ
pr2 (count-is-empty H) = inv-equiv (pair H (is-equiv-is-empty' H))

count-empty : count empty
count-empty = count-Fin zero-ℕ
```

### A type has 1 element if and only if it is contractible

```agda
count-is-contr :
  {l : Level} {X : UU l} → is-contr X → count X
pr1 (count-is-contr H) = 1
pr2 (count-is-contr H) = equiv-is-contr is-contr-Fin-1 H

abstract
  is-contr-is-one-number-of-elements-count :
    {l : Level} {X : UU l} (e : count X) →
    is-one-ℕ (number-of-elements-count e) → is-contr X
  is-contr-is-one-number-of-elements-count (pair .(succ-ℕ zero-ℕ) e) refl =
    is-contr-equiv' (Fin 1) e is-contr-Fin-1

abstract
  is-one-number-of-elements-count-is-contr :
    {l : Level} {X : UU l} (e : count X) →
    is-contr X → is-one-ℕ (number-of-elements-count e)
  is-one-number-of-elements-count-is-contr (pair zero-ℕ e) H =
    ex-falso (map-inv-equiv e (center H))
  is-one-number-of-elements-count-is-contr (pair (succ-ℕ zero-ℕ) e) H =
    refl
  is-one-number-of-elements-count-is-contr (pair (succ-ℕ (succ-ℕ k)) e) H =
    ex-falso
      ( Eq-Fin-eq (succ-ℕ (succ-ℕ k))
        ( is-injective-equiv e
          ( eq-is-contr' H
            ( map-equiv e (zero-Fin (succ-ℕ k)))
            ( map-equiv e (neg-one-Fin (succ-ℕ k))))))

count-unit : count unit
count-unit = count-is-contr is-contr-unit
```

### Types with a count have decidable equality

```agda
has-decidable-equality-count :
  {l : Level} {X : UU l} → count X → has-decidable-equality X
has-decidable-equality-count (pair k e) =
  has-decidable-equality-equiv' e (has-decidable-equality-Fin k)
```

### This with a count are either inhabited or empty

```agda
is-inhabited-or-empty-count :
  {l1 : Level} {A : UU l1} → count A → is-inhabited-or-empty A
is-inhabited-or-empty-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-inhabited-or-empty-count (pair (succ-ℕ k) e) =
  inl (unit-trunc-Prop (map-equiv e (zero-Fin k)))
```

### If the elements of a type can be counted, then the elements of its propositional truncation can be counted

```agda
count-type-trunc-Prop :
  {l1 : Level} {A : UU l1} → count A → count (type-trunc-Prop A)
count-type-trunc-Prop (pair zero-ℕ e) =
  count-is-empty
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl))
count-type-trunc-Prop (pair (succ-ℕ k) e) =
  count-is-contr
    ( is-proof-irrelevant-is-prop
      ( is-prop-type-trunc-Prop)
      ( unit-trunc-Prop (map-equiv e (zero-Fin k))))
```
