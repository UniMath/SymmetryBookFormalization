# Iterated cartesian product types

```agda
module foundation.iterated-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-empty-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
open import lists.permutation-lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

In this file, we give three definitions of the iterated cartesian product
`A₁ × ... × Aₙ` of `n` types `A₁ , ... , Aₙ`. Two use a family of types over
`Fin n`: the first uses recursion over `Fin n` and the second is just
`Π (Fin n) A`. The last one uses lists.

We show that :

- all of these definitions are equivalent
- iterated cartesian product of types is closed under permutations

## Definitions

### Via a family of types over `Fin n`

#### Using recursion

```agda
iterated-product-Fin-recursive :
  {l : Level} (n : ℕ) →
  ((Fin n) → UU l) → UU l
iterated-product-Fin-recursive {l} zero-ℕ A = raise-unit l
iterated-product-Fin-recursive (succ-ℕ n) A =
  A (inr star) × iterated-product-Fin-recursive n (A ∘ inl)
```

#### Using `Π`-types

```agda
iterated-product-Fin-Π :
  {l : Level} (n : ℕ) →
  ((Fin n) → UU l) → UU l
iterated-product-Fin-Π n A = (i : Fin n) → A i
```

### Via lists

```agda
iterated-product-lists :
  {l : Level} → list (UU l) → UU l
iterated-product-lists {l} nil = raise-unit l
iterated-product-lists (cons A p) = A × iterated-product-lists p
```

## Properties

### The definitions using recursion and `Π`-types are equivalent

```agda
equiv-iterated-product-Fin-recursive-Π :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) →
  iterated-product-Fin-recursive n A ≃
  iterated-product-Fin-Π n A
equiv-iterated-product-Fin-recursive-Π zero-ℕ A =
  equiv-is-contr is-contr-raise-unit (dependent-universal-property-empty' A)
equiv-iterated-product-Fin-recursive-Π (succ-ℕ n) A =
  ( ( inv-equiv (equiv-dependent-universal-property-coproduct A)) ∘e
    ( ( commutative-product) ∘e
      ( ( equiv-product
            ( inv-equiv (left-unit-law-Π-is-contr is-contr-unit star))
            ( id-equiv)) ∘e
        ( ( equiv-product
              ( id-equiv)
              ( equiv-iterated-product-Fin-recursive-Π n (A ∘ inl)))))))
```

### The definitions using recursion and lists are equivalent

```agda
equiv-iterated-product-Fin-recursive-lists :
  {l : Level} (l : list (UU l)) →
  iterated-product-Fin-recursive
    ( length-array (array-list l))
    ( functional-vec-array (array-list l)) ≃
  iterated-product-lists l
equiv-iterated-product-Fin-recursive-lists nil = id-equiv
equiv-iterated-product-Fin-recursive-lists (cons x l) =
  equiv-product id-equiv (equiv-iterated-product-Fin-recursive-lists l)
```

### The cartesian product of two iterated cartesian products (via list) is the iterated cartesian product of the concatenation of the corresponding lists

```agda
equiv-product-iterated-product-lists :
  {l : Level} (p q : list (UU l)) →
  (iterated-product-lists p × iterated-product-lists q) ≃
  iterated-product-lists (concat-list p q)
equiv-product-iterated-product-lists nil q =
  left-unit-law-product-is-contr (is-contr-raise-unit)
equiv-product-iterated-product-lists (cons x p) q =
  ( ( equiv-product
      ( id-equiv)
      ( equiv-product-iterated-product-lists p q)) ∘e
    ( associative-product
      ( x)
      ( iterated-product-lists p)
      ( iterated-product-lists q)))
```

### Iterated cartesian product is closed under permutations

```agda
permutation-iterated-product-Fin-Π :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) → UU l
permutation-iterated-product-Fin-Π n A t =
  iterated-product-Fin-Π n (A ∘ map-equiv t)

equiv-permutation-iterated-product-Fin-Π :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) →
  permutation-iterated-product-Fin-Π n A t ≃ iterated-product-Fin-Π n A
equiv-permutation-iterated-product-Fin-Π n A t =
  equiv-Π (λ z → A z) t (λ a → id-equiv)

eq-permutation-iterated-product-Fin-Π :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) →
  permutation-iterated-product-Fin-Π n A t ＝ iterated-product-Fin-Π n A
eq-permutation-iterated-product-Fin-Π n A t =
  eq-equiv (equiv-permutation-iterated-product-Fin-Π n A t)

permutation-iterated-product-Fin-recursive :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) → UU l
permutation-iterated-product-Fin-recursive n A t =
  iterated-product-Fin-recursive n (A ∘ map-equiv t)

equiv-permutation-iterated-product-Fin-recursive :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) →
  permutation-iterated-product-Fin-recursive n A t ≃
  iterated-product-Fin-recursive n A
equiv-permutation-iterated-product-Fin-recursive n A t =
  ( inv-equiv (equiv-iterated-product-Fin-recursive-Π n A)) ∘e
  ( equiv-permutation-iterated-product-Fin-Π n A t) ∘e
  ( equiv-iterated-product-Fin-recursive-Π n (A ∘ map-equiv t))

eq-permutation-iterated-product-Fin-recursive :
  {l : Level} (n : ℕ) (A : (Fin n → UU l)) (t : permutation n) →
  permutation-iterated-product-Fin-recursive n A t ＝
  iterated-product-Fin-recursive n A
eq-permutation-iterated-product-Fin-recursive n A t =
  eq-equiv (equiv-permutation-iterated-product-Fin-recursive n A t)

permutation-iterated-product-lists :
  {l : Level} (L : list (UU l)) (t : permutation (length-list L)) → UU l
permutation-iterated-product-lists L t =
  iterated-product-lists (permute-list L t)

equiv-permutation-iterated-product-lists :
  {l : Level} (L : list (UU l)) (t : permutation (length-list L)) →
  permutation-iterated-product-lists L t ≃
  iterated-product-lists L
equiv-permutation-iterated-product-lists L t =
  ( equiv-iterated-product-Fin-recursive-lists L ∘e
    ( ( equiv-permutation-iterated-product-Fin-recursive
        ( length-list L)
        ( functional-vec-array (array-list L))
        ( t)) ∘e
      ( equiv-eq
        ( ap
          ( λ p →
            iterated-product-Fin-recursive
              ( length-array p)
              ( functional-vec-array p))
          ( is-retraction-array-list
            ( length-list L ,
              ( functional-vec-array (array-list L) ∘ map-equiv t)))) ∘e
        ( inv-equiv
          ( equiv-iterated-product-Fin-recursive-lists (permute-list L t))))))

eq-permutation-iterated-product-lists :
  {l : Level} (L : list (UU l)) (t : permutation (length-list L)) →
  permutation-iterated-product-lists L t ＝
  iterated-product-lists L
eq-permutation-iterated-product-lists L t =
  eq-equiv (equiv-permutation-iterated-product-lists L t)
```
