# Transpositions of standard finite types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.transpositions-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import lists.functoriality-lists
open import lists.lists

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given `i` and `j` in `Fin n`, the transposition associated to `i` and `j` swap
these two elements.

## Definitions

### Transpositions on `Fin n`

This definition uses the `standard-transposition` in
[`finite-group-theory.transposition`](finite-group-theory.transpositions.md).

```agda
module _
  (n : ℕ) (i j : Fin n) (neq : i ≠ j)
  where

  transposition-Fin : permutation n
  transposition-Fin = standard-transposition (has-decidable-equality-Fin n) neq

  map-transposition-Fin : Fin n → Fin n
  map-transposition-Fin =
    map-standard-transposition (has-decidable-equality-Fin n) neq

  left-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq i ＝ j
  left-computation-transposition-Fin =
    left-computation-standard-transposition (has-decidable-equality-Fin n) neq

  right-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq j ＝ i
  right-computation-transposition-Fin =
    right-computation-standard-transposition (has-decidable-equality-Fin n) neq

  is-fixed-point-transposition-Fin :
    (z : Fin n) →
    i ≠ z →
    j ≠ z →
    map-standard-transposition (has-decidable-equality-Fin n) neq z ＝ z
  is-fixed-point-transposition-Fin =
    is-fixed-point-standard-transposition (has-decidable-equality-Fin n) neq
```

### The transposition that swaps the two last elements of `Fin (succ-ℕ (succ-ℕ n))`

We define directly the transposition of `Fin (succ-ℕ (succ-ℕ n))` that exchanges
the two elements associated to `n` and `succ-ℕ n`.

```agda
module _
  (n : ℕ)
  where

  map-swap-two-last-elements-transposition-Fin :
    Fin (succ-ℕ (succ-ℕ n)) → Fin (succ-ℕ (succ-ℕ n))
  map-swap-two-last-elements-transposition-Fin (inl (inl x)) = inl (inl x)
  map-swap-two-last-elements-transposition-Fin (inl (inr star)) = inr star
  map-swap-two-last-elements-transposition-Fin (inr star) = inl (inr star)

  is-involution-map-swap-two-last-elements-transposition-Fin :
    ( map-swap-two-last-elements-transposition-Fin ∘
      map-swap-two-last-elements-transposition-Fin) ~
    id
  is-involution-map-swap-two-last-elements-transposition-Fin (inl (inl x)) =
    refl
  is-involution-map-swap-two-last-elements-transposition-Fin (inl (inr star)) =
    refl
  is-involution-map-swap-two-last-elements-transposition-Fin (inr star) = refl

  swap-two-last-elements-transposition-Fin : permutation (succ-ℕ (succ-ℕ n))
  pr1 swap-two-last-elements-transposition-Fin =
    map-swap-two-last-elements-transposition-Fin
  pr2 swap-two-last-elements-transposition-Fin =
    is-equiv-is-invertible
      map-swap-two-last-elements-transposition-Fin
      is-involution-map-swap-two-last-elements-transposition-Fin
      is-involution-map-swap-two-last-elements-transposition-Fin
```

We show that this definiton is an instance of the previous one.

```agda
  cases-htpy-swap-two-last-elements-transposition-Fin :
    (x : Fin (succ-ℕ (succ-ℕ n))) →
    (x ＝ neg-one-Fin (succ-ℕ n)) + (x ≠ neg-one-Fin (succ-ℕ n)) →
    (x ＝ neg-two-Fin (succ-ℕ n)) + (x ≠ neg-two-Fin (succ-ℕ n)) →
    map-swap-two-last-elements-transposition-Fin x ＝
    map-transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-two-Fin (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( neq-inl-inr)
      ( x)
  cases-htpy-swap-two-last-elements-transposition-Fin _ (inl refl) _ =
    inv
      ( right-computation-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq-inl-inr))
  cases-htpy-swap-two-last-elements-transposition-Fin _ (inr p) (inl refl) =
    inv
      ( left-computation-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq-inl-inr))
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inl (inl x))
    ( inr p)
    ( inr q) =
    inv
      ( is-fixed-point-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq-inl-inr)
        ( inl (inl x))
        ( q ∘ inv)
        ( p ∘ inv))
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inl (inr star))
    ( inr p)
    ( inr q) = ex-falso (q refl)
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inr star)
    ( inr p)
    ( inr q) = ex-falso (p refl)

  htpy-swap-two-last-elements-transposition-Fin :
    htpy-equiv
      ( swap-two-last-elements-transposition-Fin)
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq-inl-inr))
  htpy-swap-two-last-elements-transposition-Fin x =
    cases-htpy-swap-two-last-elements-transposition-Fin
      ( x)
      ( has-decidable-equality-Fin
        ( succ-ℕ (succ-ℕ n))
        ( x)
        ( neg-one-Fin (succ-ℕ n)))
      ( has-decidable-equality-Fin
        ( succ-ℕ (succ-ℕ n))
        ( x)
        ( neg-two-Fin (succ-ℕ n)))
```

### Transpositions of a pair of adjacent elements in `Fin (succ-ℕ n)`

#### Definition using `swap-two-last-elements-transposition-Fin`

```agda
adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  permutation (succ-ℕ n)
adjacent-transposition-Fin (succ-ℕ n) (inl x) =
  equiv-coproduct (adjacent-transposition-Fin n x) id-equiv
adjacent-transposition-Fin (succ-ℕ n) (inr x) =
  swap-two-last-elements-transposition-Fin n

map-adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  (Fin (succ-ℕ n) → Fin (succ-ℕ n))
map-adjacent-transposition-Fin n k = map-equiv (adjacent-transposition-Fin n k)
```

#### `adjacent-transposition-Fin` is an instance of the definiton `transposition-Fin`

```agda
cases-htpy-map-coproduct-map-transposition-id-Fin :
  (n : ℕ) → (k l : Fin n) → (neq : k ≠ l) →
  (x : Fin (succ-ℕ n)) →
  (x ＝ inl-Fin n k) + (x ≠ inl-Fin n k) →
  (x ＝ inl-Fin n l) + (x ≠ inl-Fin n l) →
  map-coproduct (map-transposition-Fin n k l neq) id x ＝
  map-transposition-Fin
    ( succ-ℕ n)
    ( inl-Fin n k)
    ( inl-Fin n l)
    ( neq ∘ is-injective-inl-Fin n)
    ( x)
cases-htpy-map-coproduct-map-transposition-id-Fin n k l neq x (inl refl) _ =
  ( ( ap
      ( inl-Fin n)
      ( left-computation-transposition-Fin n k l neq)) ∙
    ( inv
      ( left-computation-transposition-Fin
        ( succ-ℕ n)
        ( inl-Fin n k)
        ( inl-Fin n l)
        ( neq ∘ is-injective-inl-Fin n))))
cases-htpy-map-coproduct-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( x)
  ( inr _)
  ( inl refl) =
  ( ( ap
      ( inl-Fin n)
      ( right-computation-transposition-Fin n k l neq)) ∙
    ( inv
      ( right-computation-transposition-Fin
        ( succ-ℕ n)
        ( inl-Fin n k)
        ( inl-Fin n l)
        ( neq ∘ is-injective-inl-Fin n))))
cases-htpy-map-coproduct-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( inl x)
  ( inr neqk)
  ( inr neql) =
  ( ( ap
      ( inl-Fin n)
      ( is-fixed-point-transposition-Fin
        ( n)
        ( k)
        ( l)
        ( neq)
        ( x)
        ( neqk ∘ (inv ∘ ap (inl-Fin n)))
        ( neql ∘ (inv ∘ ap (inl-Fin n))))) ∙
    ( inv
      ( is-fixed-point-transposition-Fin
        ( succ-ℕ n)
        ( inl-Fin n k)
        ( inl-Fin n l)
        ( neq ∘ is-injective-inl-Fin n)
        ( inl x)
        ( neqk ∘ inv)
        ( neql ∘ inv))))
cases-htpy-map-coproduct-map-transposition-id-Fin
  ( n)
  ( k)
  ( l)
  ( neq)
  ( inr star)
  ( inr neqk)
  ( inr neql) =
  inv
    ( is-fixed-point-transposition-Fin
      ( succ-ℕ n)
      ( inl-Fin n k)
      ( inl-Fin n l)
      ( neq ∘ is-injective-inl-Fin n)
      ( inr star)
      ( neqk ∘ inv)
      ( neql ∘ inv))

htpy-map-coproduct-map-transposition-id-Fin :
  (n : ℕ) → (k l : Fin n) → (neq : k ≠ l) →
  htpy-equiv
    ( equiv-coproduct (transposition-Fin n k l neq) id-equiv)
    ( transposition-Fin
      ( succ-ℕ n)
      ( inl-Fin n k)
      ( inl-Fin n l)
      ( neq ∘ is-injective-inl-Fin n))
htpy-map-coproduct-map-transposition-id-Fin n k l neq x =
  cases-htpy-map-coproduct-map-transposition-id-Fin
    ( n)
    ( k)
    ( l)
    ( neq)
    ( x)
    ( has-decidable-equality-Fin (succ-ℕ n) x (inl-Fin n k))
    ( has-decidable-equality-Fin (succ-ℕ n) x (inl-Fin n l))

helper-htpy-same-transposition-Fin :
  (n : ℕ) (k l : Fin n) (neq1 : k ≠ l) (neq2 : k ≠ l) →
  (neq1 ＝ neq2) →
  htpy-equiv
    ( transposition-Fin n k l neq1)
    ( transposition-Fin n k l neq2)
helper-htpy-same-transposition-Fin n k l neq1 .neq1 refl = refl-htpy

htpy-same-transposition-Fin :
  {n : ℕ} {k l : Fin n} {neq1 : k ≠ l} {neq2 : k ≠ l} →
  htpy-equiv
    ( transposition-Fin n k l neq1)
    ( transposition-Fin n k l neq2)
htpy-same-transposition-Fin {n} {k} {l} {neq1} {neq2} =
  helper-htpy-same-transposition-Fin n k l neq1 neq2 (eq-is-prop is-prop-neg)

htpy-adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) →
  htpy-equiv
    ( adjacent-transposition-Fin n k)
    ( transposition-Fin
      ( succ-ℕ n)
      ( inl-Fin n k)
      ( inr-Fin n k)
      ( neq-inl-Fin-inr-Fin n k))
htpy-adjacent-transposition-Fin (succ-ℕ n) (inl x) =
  ( ( htpy-map-coproduct (htpy-adjacent-transposition-Fin n x) refl-htpy) ∙h
    ( ( htpy-map-coproduct-map-transposition-id-Fin
        ( succ-ℕ n)
        ( inl-Fin n x)
        ( inr-Fin n x)
        ( neq-inl-Fin-inr-Fin n x)) ∙h
      ( htpy-same-transposition-Fin)))
htpy-adjacent-transposition-Fin (succ-ℕ n) (inr star) =
  htpy-swap-two-last-elements-transposition-Fin n
```

## Properties

### The transposition associated to `i` and `j` is homotopic to the one associated with `j` and `i`

```agda
cases-htpy-transposition-Fin-transposition-swap-Fin :
  (n : ℕ) → (i j : Fin n) → (neq : i ≠ j) → (x : Fin n) →
  (x ＝ i) + (x ≠ i) →
  (x ＝ j) + (x ≠ j) →
  map-transposition-Fin n i j neq x ＝
  map-transposition-Fin n j i (neq ∘ inv) x
cases-htpy-transposition-Fin-transposition-swap-Fin
  ( n)
  ( i)
  ( j)
  ( neq)
  ( .i)
  ( inl refl) _ =
  left-computation-transposition-Fin n i j neq ∙
  inv (right-computation-transposition-Fin n j i (neq ∘ inv))
cases-htpy-transposition-Fin-transposition-swap-Fin
  ( n)
  ( i)
  ( j)
  ( neq)
  ( .j)
  ( inr _)
  ( inl refl) =
  right-computation-transposition-Fin n i j neq ∙
  inv (left-computation-transposition-Fin n j i (neq ∘ inv))
cases-htpy-transposition-Fin-transposition-swap-Fin
  ( n)
  ( i)
  ( j)
  ( neq)
  ( x)
  ( inr neqi)
  ( inr neqj) =
  is-fixed-point-transposition-Fin
    ( n)
    ( i)
    ( j)
    ( neq)
    ( x)
    ( neqi ∘ inv)
    ( neqj ∘ inv) ∙
  inv
    (is-fixed-point-transposition-Fin
      ( n)
      ( j)
      ( i)
      ( neq ∘ inv)
      ( x)
      ( neqj ∘ inv)
      ( neqi ∘ inv))

htpy-transposition-Fin-transposition-swap-Fin :
  (n : ℕ) → (i j : Fin n) → (neq : i ≠ j) →
  htpy-equiv
    ( transposition-Fin n i j neq)
    ( transposition-Fin n j i (neq ∘ inv))
htpy-transposition-Fin-transposition-swap-Fin n i j neq x =
  cases-htpy-transposition-Fin-transposition-swap-Fin
    ( n)
    ( i)
    ( j)
    ( neq)
    ( x)
    ( has-decidable-equality-Fin n x i)
    ( has-decidable-equality-Fin n x j)
```

### The conjugate of a transposition is also a transposition

```agda
htpy-conjugate-transposition-Fin :
  (n : ℕ) (x y z : Fin n)
  (neqxy : x ≠ y)
  (neqyz : y ≠ z)
  (neqxz : x ≠ z) →
  htpy-equiv
    ( transposition-Fin n y z neqyz ∘e
      ( transposition-Fin n x y neqxy ∘e
        transposition-Fin n y z neqyz))
    ( transposition-Fin n x z neqxz)
htpy-conjugate-transposition-Fin n x y z neqxy neqyz neqxz =
  htpy-conjugate-transposition
    ( has-decidable-equality-Fin n)
    ( neqxy)
    ( neqyz)
    ( neqxz)

private
  htpy-whisker-conjugate :
    {l1 : Level} {A : UU l1} {f f' : A → A} (g : A → A) →
    (f ~ f') → (f ∘ (g ∘ f)) ~ (f' ∘ (g ∘ f'))
  htpy-whisker-conjugate {f = f} {f' = f'} g H x =
    H (g ( f x)) ∙ ap (f' ∘ g) (H x)

htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin :
  (n : ℕ) (x : Fin (succ-ℕ n)) (neq : x ≠ neg-one-Fin n) →
  htpy-equiv
    ( swap-two-last-elements-transposition-Fin n ∘e
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( inl-Fin (succ-ℕ n) x)
        ( neg-two-Fin (succ-ℕ n))
        ( neq ∘ is-injective-inl-Fin (succ-ℕ n)) ∘e
        swap-two-last-elements-transposition-Fin n))
    ( transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( inl-Fin (succ-ℕ n) x)
      ( neg-one-Fin (succ-ℕ n))
      ( neq-inl-inr))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin n x neq =
  ( ( htpy-whisker-conjugate
        ( map-transposition-Fin
          ( succ-ℕ (succ-ℕ n))
          ( inl-Fin (succ-ℕ n) x)
          ( neg-two-Fin (succ-ℕ n))
          ( neq ∘ is-injective-inl-Fin (succ-ℕ n)))
        ( htpy-swap-two-last-elements-transposition-Fin n)) ∙h
    ( ( htpy-conjugate-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( inl-Fin (succ-ℕ n) x)
        ( neg-two-Fin (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neq ∘ is-injective-inl-Fin (succ-ℕ n))
        ( neq-inl-inr)
        ( neq-inl-inr))))

htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin' :
  (n : ℕ) (x : Fin (succ-ℕ n)) (neq : x ≠ neg-one-Fin n) →
  htpy-equiv
    ( swap-two-last-elements-transposition-Fin n ∘e
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( inl-Fin (succ-ℕ n) x)
        ( neq ∘ (is-injective-inl-Fin (succ-ℕ n) ∘ inv)) ∘e
        swap-two-last-elements-transposition-Fin n))
    ( transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( inl-Fin (succ-ℕ n) x)
      ( neq-inr-inl))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin' n x neq =
  ( ( double-whisker-comp
      ( map-swap-two-last-elements-transposition-Fin n)
      ( ( htpy-transposition-Fin-transposition-swap-Fin
          ( succ-ℕ (succ-ℕ n))
          ( neg-two-Fin (succ-ℕ n))
          ( inl-Fin (succ-ℕ n) x)
          ( neq ∘ (is-injective-inl-Fin (succ-ℕ n) ∘ inv))) ∙h
        htpy-same-transposition-Fin)
      ( map-swap-two-last-elements-transposition-Fin n)) ∙h
      ( ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin
          ( n)
          ( x)
          ( neq) ∙h
        ( ( htpy-transposition-Fin-transposition-swap-Fin
            ( succ-ℕ (succ-ℕ n))
            ( inl-Fin (succ-ℕ n) x)
            ( neg-one-Fin (succ-ℕ n))
            ( neq-inl-inr)) ∙h
          htpy-same-transposition-Fin))))
```

### Every transposition is the composition of a list of adjacent transpositions

```agda
list-adjacent-transpositions-transposition-Fin :
  (n : ℕ) → (i j : Fin (succ-ℕ n)) →
  list (Fin n)
list-adjacent-transpositions-transposition-Fin n (inr _) (inr _) = nil
list-adjacent-transpositions-transposition-Fin 0 (inl _) (inr _) = nil
list-adjacent-transpositions-transposition-Fin 0 (inl _) (inl _) = nil
list-adjacent-transpositions-transposition-Fin 0 (inr _) (inl _) = nil
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl i)
  ( inl j) =
  map-list (inl-Fin n) (list-adjacent-transpositions-transposition-Fin n i j)
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inr star))
  ( inr star) = cons (inr star) nil
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inl i))
  ( inr star) =
  snoc
    ( cons
      ( inr star)
      ( map-list
        ( inl-Fin n)
        ( list-adjacent-transpositions-transposition-Fin n (inl i) (inr star))))
    ( inr star)
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inl j)) =
  snoc
    ( cons
      ( inr star)
      ( map-list
        ( inl-Fin n)
        ( list-adjacent-transpositions-transposition-Fin n (inr star) (inl j))))
    ( inr star)
list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inr star)) = cons (inr star) nil

permutation-list-adjacent-transpositions :
  (n : ℕ) → list (Fin n) → permutation (succ-ℕ n)
permutation-list-adjacent-transpositions n nil = id-equiv
permutation-list-adjacent-transpositions n (cons x l) =
  adjacent-transposition-Fin n x ∘e
  permutation-list-adjacent-transpositions n l

map-permutation-list-adjacent-transpositions :
  (n : ℕ) → list (Fin n) → Fin (succ-ℕ n) → Fin (succ-ℕ n)
map-permutation-list-adjacent-transpositions n l =
  map-equiv (permutation-list-adjacent-transpositions n l)

htpy-permutation-inl-list-adjacent-transpositions :
  (n : ℕ) → (l : list (Fin n)) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions
      ( succ-ℕ n)
      ( map-list (inl-Fin n) l))
    ( equiv-coproduct
      ( permutation-list-adjacent-transpositions n l)
      ( id-equiv))
htpy-permutation-inl-list-adjacent-transpositions n nil =
  inv-htpy (id-map-coproduct (Fin (succ-ℕ n)) unit)
htpy-permutation-inl-list-adjacent-transpositions n (cons x l) =
  ( map-coproduct (map-adjacent-transposition-Fin n x) id ·l
    htpy-permutation-inl-list-adjacent-transpositions n l) ∙h
  ( inv-htpy
      ( preserves-comp-map-coproduct
        ( map-permutation-list-adjacent-transpositions n l)
        ( map-adjacent-transposition-Fin n x)
        ( id)
        ( id)))

htpy-permutation-snoc-list-adjacent-transpositions :
  (n : ℕ) (l : list (Fin n)) (x : Fin n) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions n (snoc l x))
    ( permutation-list-adjacent-transpositions n l ∘e
      adjacent-transposition-Fin n x)
htpy-permutation-snoc-list-adjacent-transpositions n nil x = refl-htpy
htpy-permutation-snoc-list-adjacent-transpositions n (cons y l) x =
  map-adjacent-transposition-Fin n y ·l
  htpy-permutation-snoc-list-adjacent-transpositions n l x

htpy-permutation-list-adjacent-transpositions-transposition-Fin :
  (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
  htpy-equiv
    ( permutation-list-adjacent-transpositions
      ( n)
      ( list-adjacent-transpositions-transposition-Fin n i j))
    ( transposition-Fin (succ-ℕ n) i j neq)
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( 0)
  ( inr star)
  ( inr star)
  ( neq) = ex-falso (neq refl)
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl i)
  ( inl j)
  ( neq) =
  ( ( htpy-permutation-inl-list-adjacent-transpositions
      ( n)
      ( list-adjacent-transpositions-transposition-Fin n i j)) ∙h
    ( ( htpy-map-coproduct
        ( htpy-permutation-list-adjacent-transpositions-transposition-Fin
          ( n)
          ( i)
          ( j)
          ( neq ∘ (ap (inl-Fin (succ-ℕ n)))))
        ( refl-htpy)) ∙h
      ( ( htpy-map-coproduct-map-transposition-id-Fin
          ( succ-ℕ n)
          ( i)
          ( j)
          ( neq ∘ ap (inl-Fin (succ-ℕ n)))) ∙h
        ( htpy-same-transposition-Fin))))
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inl i))
  ( inr star)
  ( neq) =
  ( ( map-swap-two-last-elements-transposition-Fin n ·l
      htpy-permutation-snoc-list-adjacent-transpositions
        ( succ-ℕ n)
        ( map-list
          ( inl-Fin n)
          ( list-adjacent-transpositions-transposition-Fin
            ( n)
            ( inl i)
            ( inr star)))
        ( inr star)) ∙h
    ( ( double-whisker-comp
        ( map-swap-two-last-elements-transposition-Fin n)
        ( ( htpy-permutation-inl-list-adjacent-transpositions
            ( n)
            ( list-adjacent-transpositions-transposition-Fin
              ( n)
              ( inl i)
              ( inr star))) ∙h
          ( htpy-map-coproduct
            ( htpy-permutation-list-adjacent-transpositions-transposition-Fin
              ( n)
              ( inl i)
              ( inr star)
              ( neq-inl-inr))
            ( refl-htpy) ∙h
            htpy-map-coproduct-map-transposition-id-Fin
              ( succ-ℕ n)
              ( inl i)
              ( inr star)
              ( neq-inl-inr)))
        ( map-swap-two-last-elements-transposition-Fin n)) ∙h
        ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin
          ( n)
          ( inl i)
          ( neq-inl-inr) ∙h
          htpy-same-transposition-Fin)))
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inl (inr star))
  ( inr star)
  ( neq) =
  htpy-swap-two-last-elements-transposition-Fin n ∙h
  htpy-same-transposition-Fin
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inl j))
  ( neq) =
  ( ( map-swap-two-last-elements-transposition-Fin n ·l
      htpy-permutation-snoc-list-adjacent-transpositions
        ( succ-ℕ n)
        ( map-list
          ( inl-Fin n)
          ( list-adjacent-transpositions-transposition-Fin
            ( n)
            ( inr star)
            ( inl j)))
        ( inr star)) ∙h
    ( ( double-whisker-comp
        ( map-swap-two-last-elements-transposition-Fin n)
        ( ( htpy-permutation-inl-list-adjacent-transpositions
            ( n)
            ( list-adjacent-transpositions-transposition-Fin
              ( n)
              ( inr star)
              ( inl j))) ∙h
          ( ( htpy-map-coproduct
              ( htpy-permutation-list-adjacent-transpositions-transposition-Fin
                ( n)
                ( inr star)
                ( inl j)
                ( neq-inr-inl))
              ( refl-htpy)) ∙h
            ( ( htpy-map-coproduct-map-transposition-id-Fin
                ( succ-ℕ n)
                ( inr star)
                ( inl j)
                ( neq-inr-inl)) ∙h
              ( htpy-same-transposition-Fin))))
        ( map-swap-two-last-elements-transposition-Fin n)) ∙h
      ( ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin'
          ( n)
          ( inl j)
          ( neq-inl-inr)) ∙h
        htpy-same-transposition-Fin)))
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inl (inr star))
  ( neq) =
  htpy-swap-two-last-elements-transposition-Fin n ∙h
  ( ( htpy-transposition-Fin-transposition-swap-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-two-Fin (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( neq-inl-inr)) ∙h
    htpy-same-transposition-Fin)
htpy-permutation-list-adjacent-transpositions-transposition-Fin
  ( succ-ℕ n)
  ( inr star)
  ( inr star)
  ( neq) = ex-falso (neq refl)
```
