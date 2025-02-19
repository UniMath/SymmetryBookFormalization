# Inequality on types equipped with a counting

```agda
module univalent-combinatorics.inequality-types-with-counting where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

If a type comes equipped with a counting of its elements, then it inherits the
inequality relations from the standard finite types.

## Definition

```agda
leq-count : {l : Level} {X : UU l} → count X → X → X → UU lzero
leq-count e x y =
  leq-Fin
    ( number-of-elements-count e)
    ( map-inv-equiv-count e x)
    ( map-inv-equiv-count e y)
```

## Properties

```agda
refl-leq-count :
  {l : Level} {X : UU l} (e : count X) (x : X) → leq-count e x x
refl-leq-count e x =
  refl-leq-Fin (number-of-elements-count e) (map-inv-equiv-count e x)

antisymmetric-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y : X} →
  leq-count e x y → leq-count e y x → Id x y
antisymmetric-leq-count e H K =
  is-injective-map-inv-equiv
    ( equiv-count e)
    ( antisymmetric-leq-Fin (number-of-elements-count e) _ _ H K)

transitive-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y z : X} →
  leq-count e y z → leq-count e x y → leq-count e x z
transitive-leq-count (pair k e) {x} {y} {z} =
  transitive-leq-Fin k
    ( map-inv-equiv e x)
    ( map-inv-equiv e y)
    ( map-inv-equiv-count (pair k e) z)

preserves-order-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-Fin (number-of-elements-count e) x y →
  leq-count e (map-equiv-count e x) (map-equiv-count e y)
preserves-order-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( is-retraction-map-inv-equiv (equiv-count e) x)
    ( H)
    ( inv (is-retraction-map-inv-equiv (equiv-count e) y))

reflects-order-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-count e (map-equiv-count e x) (map-equiv-count e y) →
  leq-Fin (number-of-elements-count e) x y
reflects-order-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( inv (is-retraction-map-inv-equiv (equiv-count e) x))
    ( H)
    ( is-retraction-map-inv-equiv (equiv-count e) y)

transpose-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X) →
  {x : Fin (number-of-elements-count e)} {y : X} →
  leq-Fin
    ( number-of-elements-count e) x (map-inv-equiv-count e y) →
  leq-count e (map-equiv-count e x) y
transpose-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( is-retraction-map-inv-equiv (equiv-count e) x)
    ( H)
    ( refl)

transpose-leq-equiv-count' :
  {l : Level} {X : UU l} (e : count X) →
  {x : X} {y : Fin (number-of-elements-count e)} →
  leq-Fin (number-of-elements-count e) (map-inv-equiv-count e x) y →
  leq-count e x (map-equiv-count e y)
transpose-leq-equiv-count' e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( number-of-elements-count e)
    ( refl)
    ( H)
    ( inv (is-retraction-map-inv-equiv (equiv-count e) y))
```
