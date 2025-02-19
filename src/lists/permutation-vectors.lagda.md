# Permutations of vectors

```agda
module lists.permutation-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import lists.arrays
open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an functional vector `t` of length `n` and a automorphism `σ` of `Fin n`,
the permutation of `t` according to `σ` is the functional vector where the index
are permuted by `σ`. Then, we can define what is a permutation of a vector of
length `n` via the equivalence between functional vectors and vectors.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-vec : (n : ℕ) → vec A n → permutation n → vec A n
  permute-vec n v s =
    listed-vec-functional-vec n (functional-vec-vec n v ∘ (map-equiv s))
```

### The predicate that a function from `vec` to `vec` is just permuting vectors

```agda
  is-permutation-vec : (n : ℕ) → (vec A n → vec A n) → UU l
  is-permutation-vec n f =
    (v : vec A n) →
    Σ ( permutation n)
      ( λ t → f v ＝ permute-vec n v t)

  permutation-is-permutation-vec :
    (n : ℕ) (f : vec A n → vec A n) → is-permutation-vec n f →
    (v : vec A n) → permutation n
  permutation-is-permutation-vec n f P v = pr1 (P v)

  eq-permute-vec-permutation-is-permutation-vec :
    (n : ℕ) (f : vec A n → vec A n) → (P : is-permutation-vec n f) →
    (v : vec A n) →
    (f v ＝ permute-vec n v (permutation-is-permutation-vec n f P v))
  eq-permute-vec-permutation-is-permutation-vec n f P v = pr2 (P v)
```

## Properties

### Computational rules

```agda
  compute-permute-vec-id-equiv :
    (n : ℕ)
    (v : vec A n) →
    permute-vec n v id-equiv ＝ v
  compute-permute-vec-id-equiv n v =
    ap (λ f → map-equiv f v) (right-inverse-law-equiv (compute-vec n))

  compute-composition-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (a b : permutation n) →
    permute-vec n v (a ∘e b) ＝ permute-vec n (permute-vec n v a) b
  compute-composition-permute-vec n v a b =
    ap
      ( λ f → listed-vec-functional-vec n (f ∘ (map-equiv b)))
      ( inv
        ( is-retraction-functional-vec-vec n
          ( functional-vec-vec n v ∘ map-equiv a)))

  compute-swap-two-last-elements-transposition-Fin-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (x y : A) →
    permute-vec
      (succ-ℕ (succ-ℕ n))
      (x ∷ y ∷ v)
      (swap-two-last-elements-transposition-Fin n) ＝
    (y ∷ x ∷ v)
  compute-swap-two-last-elements-transposition-Fin-permute-vec n v x y =
    eq-Eq-vec
      ( succ-ℕ (succ-ℕ n))
      ( permute-vec
          ( succ-ℕ (succ-ℕ n))
          ( x ∷ y ∷ v)
          ( swap-two-last-elements-transposition-Fin n))
      ( y ∷ x ∷ v)
      ( refl ,
        refl ,
        Eq-eq-vec
          ( n)
          ( permute-vec n v id-equiv)
          ( v)
          ( compute-permute-vec-id-equiv n v))

  compute-equiv-coproduct-permutation-id-equiv-permute-vec :
    (n : ℕ)
    (v : vec A n)
    (x : A)
    (t : permutation n) →
    permute-vec (succ-ℕ n) (x ∷ v) (equiv-coproduct t id-equiv) ＝
    (x ∷ permute-vec n v t)
  compute-equiv-coproduct-permutation-id-equiv-permute-vec n v x t =
    eq-Eq-vec
      ( succ-ℕ n)
      ( permute-vec (succ-ℕ n) (x ∷ v) (equiv-coproduct t id-equiv))
      ( x ∷ permute-vec n v t)
      ( refl ,
        ( Eq-eq-vec
          ( n)
          ( _)
          ( permute-vec n v t)
          ( refl)))

  ap-permute-vec :
    {n : ℕ}
    (a : permutation n)
    {v w : vec A n} →
    v ＝ w →
    permute-vec n v a ＝ permute-vec n w a
  ap-permute-vec a refl = refl
```

### `x` is in a vector `v` iff it is in `permute v t`

```agda
  is-in-functional-vec-is-in-permute-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : permutation n) (x : A) →
    in-functional-vec n x (v ∘ map-equiv t) → in-functional-vec n x v
  is-in-functional-vec-is-in-permute-functional-vec n v t x (k , refl) =
    map-equiv t k , refl

  is-in-vec-is-in-permute-vec :
    (n : ℕ) (v : vec A n) (t : permutation n) (x : A) →
    x ∈-vec (permute-vec n v t) → x ∈-vec v
  is-in-vec-is-in-permute-vec n v t x I =
    is-in-vec-is-in-functional-vec
      ( n)
      ( v)
      ( x)
      ( is-in-functional-vec-is-in-permute-functional-vec
        ( n)
        ( functional-vec-vec n v)
        ( t)
        ( x)
        ( tr
          ( λ p → in-functional-vec n x p)
          ( is-retraction-functional-vec-vec n
            ( functional-vec-vec n v ∘ map-equiv t))
          ( is-in-functional-vec-is-in-vec n (permute-vec n v t) x I)))

  is-in-permute-functional-vec-is-in-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : permutation n) (x : A) →
    in-functional-vec n x v → in-functional-vec n x (v ∘ map-equiv t)
  is-in-permute-functional-vec-is-in-functional-vec n v t x (k , refl) =
    map-inv-equiv t k , ap v (inv (is-section-map-inv-equiv t k))

  is-in-permute-vec-is-in-vec :
    (n : ℕ) (v : vec A n) (t : permutation n) (x : A) →
    x ∈-vec v → x ∈-vec (permute-vec n v t)
  is-in-permute-vec-is-in-vec n v t x I =
    is-in-vec-is-in-functional-vec
      ( n)
      ( permute-vec n v t)
      ( x)
      ( tr
        ( λ p → in-functional-vec n x p)
        ( inv
          ( is-retraction-functional-vec-vec n
            ( functional-vec-vec n v ∘ map-equiv t)))
        ( is-in-permute-functional-vec-is-in-functional-vec
          ( n)
          ( functional-vec-vec n v)
          ( t)
          ( x)
          ( is-in-functional-vec-is-in-vec n v x I)))
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-vec b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μ : A → (B → B))
  where

  commutative-fold-vec : UU (l1 ⊔ l2)
  commutative-fold-vec = (a1 a2 : A) (b : B) → μ a1 (μ a2 b) ＝ μ a2 (μ a1 b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  (C : commutative-fold-vec μ)
  where

  invariant-swap-two-last-elements-transposition-fold-vec :
    {n : ℕ} → (v : vec A (succ-ℕ (succ-ℕ n))) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec (succ-ℕ (succ-ℕ n))
      ( v)
      ( swap-two-last-elements-transposition-Fin n))
  invariant-swap-two-last-elements-transposition-fold-vec {n} (y ∷ z ∷ v) =
    C y z (fold-vec b μ v) ∙
    inv
      ( ap
        ( fold-vec b μ)
        ( compute-swap-two-last-elements-transposition-Fin-permute-vec
          ( n)
          ( v)
          ( y)
          ( z)))

  invariant-adjacent-transposition-fold-vec :
    {n : ℕ} → (v : vec A (succ-ℕ n)) → (k : Fin n) →
    fold-vec b μ v ＝
    fold-vec b μ (permute-vec (succ-ℕ n) v (adjacent-transposition-Fin n k))
  invariant-adjacent-transposition-fold-vec {succ-ℕ n} (x ∷ v) (inl k) =
    ap
      ( μ x)
      ( invariant-adjacent-transposition-fold-vec v k) ∙
    inv
      ( ap
        ( fold-vec b μ)
        ( compute-equiv-coproduct-permutation-id-equiv-permute-vec
          ( succ-ℕ n)
          ( v)
          ( x)
          ( adjacent-transposition-Fin n k)))
  invariant-adjacent-transposition-fold-vec {succ-ℕ n} (x ∷ v) (inr _) =
    invariant-swap-two-last-elements-transposition-fold-vec (x ∷ v)

  invariant-list-adjacent-transpositions-fold-vec :
    {n : ℕ} (v : vec A (succ-ℕ n)) (l : list (Fin n)) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec
        ( succ-ℕ n)
        ( v)
        ( permutation-list-adjacent-transpositions n l))
  invariant-list-adjacent-transpositions-fold-vec {n} v nil =
    ap (fold-vec b μ) (inv (compute-permute-vec-id-equiv (succ-ℕ n) v))
  invariant-list-adjacent-transpositions-fold-vec {n} v (cons x l) =
    ( invariant-adjacent-transposition-fold-vec v x ∙
      ( ( invariant-list-adjacent-transpositions-fold-vec
          ( permute-vec (succ-ℕ n) v (adjacent-transposition-Fin n x))
          ( l)) ∙
        ( ap
          ( fold-vec b μ)
          ( inv
            ( compute-composition-permute-vec
              ( succ-ℕ n)
              ( v)
              ( adjacent-transposition-Fin n x)
              ( permutation-list-adjacent-transpositions n l))))))

  invariant-transposition-fold-vec :
    {n : ℕ} (v : vec A (succ-ℕ n)) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec (succ-ℕ n) v (transposition-Fin (succ-ℕ n) i j neq))
  invariant-transposition-fold-vec {n} v i j neq =
    ( ( invariant-list-adjacent-transpositions-fold-vec
        ( v)
        ( list-adjacent-transpositions-transposition-Fin n i j)) ∙
      ( ap
        ( λ t → fold-vec b μ (permute-vec (succ-ℕ n) v t))
        ( eq-htpy-equiv
          { e =
            permutation-list-adjacent-transpositions
              ( n)
              ( list-adjacent-transpositions-transposition-Fin n i j)}
          { e' = transposition-Fin (succ-ℕ n) i j neq}
          ( htpy-permutation-list-adjacent-transpositions-transposition-Fin
            ( n)
            ( i)
            ( j)
            ( neq)))))

  invariant-list-transpositions-fold-vec :
    {n : ℕ}
    (v : vec A n)
    (l : list (Σ (Fin n × Fin n) (λ (i , j) → i ≠ j))) →
    fold-vec b μ v ＝
    fold-vec
      ( b)
      ( μ)
      ( permute-vec
        ( n)
        ( v)
        ( permutation-list-standard-transpositions-Fin n l))
  invariant-list-transpositions-fold-vec {n} v nil =
    ap
      ( fold-vec b μ)
      ( inv ( compute-permute-vec-id-equiv n v))
  invariant-list-transpositions-fold-vec {0} v (cons _ _) = refl
  invariant-list-transpositions-fold-vec {succ-ℕ n} v (cons ((i , j) , neq) l) =
    ( invariant-transposition-fold-vec v i j neq ∙
      ( ( invariant-list-transpositions-fold-vec
          ( permute-vec (succ-ℕ n) v (transposition-Fin (succ-ℕ n) i j neq))
          ( l)) ∙
        ( ap
          ( fold-vec b μ)
          ( inv
            ( compute-composition-permute-vec
              ( succ-ℕ n)
              ( v)
              ( transposition-Fin (succ-ℕ n) i j neq)
              ( permutation-list-standard-transpositions-Fin (succ-ℕ n) l))))))

  permutation-invariant-fold-vec :
    {n : ℕ} → (v : vec A n) → (f : permutation n) →
    fold-vec b μ v ＝ fold-vec b μ (permute-vec n v f)
  permutation-invariant-fold-vec {n} v f =
    ( ( invariant-list-transpositions-fold-vec
        ( v)
        ( list-standard-transpositions-permutation-Fin n f)) ∙
      ( ap
        ( λ f → fold-vec b μ (permute-vec n v f))
        ( eq-htpy-equiv
          {e =
            permutation-list-standard-transpositions-Fin
              ( n)
              ( list-standard-transpositions-permutation-Fin n f)}
          {e' = f}
          ( retraction-permutation-list-standard-transpositions-Fin n f))))
```

### `map-vec` of the permutation of a vector

```agda
eq-map-vec-permute-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {n : ℕ} (v : vec A n) (t : permutation n) →
  permute-vec n (map-vec f v) t ＝
  map-vec f (permute-vec n v t)
eq-map-vec-permute-vec f {n} v t =
  ( ( ap
      ( λ w →
        ( listed-vec-functional-vec
          ( n)
          ( functional-vec-vec n w ∘ (map-equiv t)))))
      ( inv (map-vec-map-functional-vec f n v)) ∙
    ( ( ap
        ( λ p →
          listed-vec-functional-vec
            ( n)
            ( p ∘ map-equiv t))
        ( is-retraction-functional-vec-vec
          ( n)
          ( map-functional-vec n f (functional-vec-vec n v)))) ∙
      ( ( ap
          ( listed-vec-functional-vec n ∘ map-functional-vec n f)
          ( inv
            ( is-retraction-functional-vec-vec
              ( n)
              ( λ z → functional-vec-vec n v (map-equiv t z))))) ∙
        ( map-vec-map-functional-vec f n (permute-vec n v t)))))
```
