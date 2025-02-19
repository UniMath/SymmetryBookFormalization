# Vectors

```agda
module linear-algebra.vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition

open import lists.lists

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

There are two equivalent definitions of vectors of length `n`. First, a **listed
vector** of length `n` is a list of `n` elements of type `A`. Secondly, a
**functional vector** of length `n` is a map `Fin n → A`. We define both types
of vectors and show that they are equivalent.

## Definitions

### The type of listed vectors

```agda
infixr 10 _∷_

data vec {l : Level} (A : UU l) : ℕ → UU l where
  empty-vec : vec A zero-ℕ
  _∷_ : {n : ℕ} → A → vec A n → vec A (succ-ℕ n)

module _
  {l : Level} {A : UU l}
  where

  head-vec : {n : ℕ} → vec A (succ-ℕ n) → A
  head-vec (x ∷ v) = x

  tail-vec : {n : ℕ} → vec A (succ-ℕ n) → vec A n
  tail-vec (x ∷ v) = v

  snoc-vec : {n : ℕ} → vec A n → A → vec A (succ-ℕ n)
  snoc-vec empty-vec a = a ∷ empty-vec
  snoc-vec (x ∷ v) a = x ∷ (snoc-vec v a)

  revert-vec : {n : ℕ} → vec A n → vec A n
  revert-vec empty-vec = empty-vec
  revert-vec (x ∷ v) = snoc-vec (revert-vec v) x

  for-all-vec : {l2 : Level} {n : ℕ} → (P : A → UU l2) → vec A n → UU l2
  for-all-vec P empty-vec = raise-unit _
  for-all-vec P (x ∷ v) = P x × for-all-vec P v

  component-vec :
    (n : ℕ) → vec A n → Fin n → A
  component-vec (succ-ℕ n) (a ∷ v) (inl k) = component-vec n v k
  component-vec (succ-ℕ n) (a ∷ v) (inr k) = a

  infix 6 _∈-vec_
  data _∈-vec_ : {n : ℕ} → A → vec A n → UU l where
    is-head : {n : ℕ} (a : A) (l : vec A n) → a ∈-vec (a ∷ l)
    is-in-tail : {n : ℕ} (a x : A) (l : vec A n) → a ∈-vec l → a ∈-vec (x ∷ l)

  index-in-vec : (n : ℕ) (a : A) (v : vec A n) → a ∈-vec v → Fin n
  index-in-vec (succ-ℕ n) a (.a ∷ v) (is-head .a .v) =
    inr star
  index-in-vec (succ-ℕ n) a (x ∷ v) (is-in-tail .a .x .v I) =
    inl (index-in-vec n a v I)

  eq-component-vec-index-in-vec :
    (n : ℕ) (a : A) (v : vec A n) (I : a ∈-vec v) →
    a ＝ component-vec n v (index-in-vec n a v I)
  eq-component-vec-index-in-vec (succ-ℕ n) a (.a ∷ v) (is-head .a .v) = refl
  eq-component-vec-index-in-vec (succ-ℕ n) a (x ∷ v) (is-in-tail .a .x .v I) =
    eq-component-vec-index-in-vec n a v I
```

### The functional type of vectors

```agda
functional-vec : {l : Level} → UU l → ℕ → UU l
functional-vec A n = Fin n → A

module _
  {l : Level} {A : UU l}
  where

  empty-functional-vec : functional-vec A 0
  empty-functional-vec ()

  head-functional-vec : (n : ℕ) → functional-vec A (succ-ℕ n) → A
  head-functional-vec n v = v (inr star)

  tail-functional-vec :
    (n : ℕ) → functional-vec A (succ-ℕ n) → functional-vec A n
  tail-functional-vec n v = v ∘ (inl-Fin n)

  cons-functional-vec :
    (n : ℕ) → A → functional-vec A n → functional-vec A (succ-ℕ n)
  cons-functional-vec n a v (inl x) = v x
  cons-functional-vec n a v (inr x) = a

  snoc-functional-vec :
    (n : ℕ) → functional-vec A n → A → functional-vec A (succ-ℕ n)
  snoc-functional-vec zero-ℕ v a i = a
  snoc-functional-vec (succ-ℕ n) v a (inl x) =
    snoc-functional-vec n (tail-functional-vec n v) a x
  snoc-functional-vec (succ-ℕ n) v a (inr x) = head-functional-vec n v

  revert-functional-vec :
    (n : ℕ) → functional-vec A n → functional-vec A n
  revert-functional-vec n v i = v (opposite-Fin n i)

  in-functional-vec : (n : ℕ) → A → functional-vec A n → UU l
  in-functional-vec n a v = Σ (Fin n) (λ k → a ＝ v k)

  index-in-functional-vec :
    (n : ℕ) (x : A) (v : functional-vec A n) →
    in-functional-vec n x v → Fin n
  index-in-functional-vec n x v I = pr1 I

  eq-component-functional-vec-index-in-functional-vec :
    (n : ℕ) (x : A) (v : functional-vec A n) (I : in-functional-vec n x v) →
    x ＝ v (index-in-functional-vec n x v I)
  eq-component-functional-vec-index-in-functional-vec n x v I = pr2 I
```

### The definition of `fold-vec`

```agda
fold-vec :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  {n : ℕ} → vec A n → B
fold-vec b μ {0} _ = b
fold-vec b μ (a ∷ l) = μ a (fold-vec b μ l)
```

## Properties

### Characterizing equality of listed vectors

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-vec : (n : ℕ) → vec A n → vec A n → UU l
  Eq-vec zero-ℕ empty-vec empty-vec = raise-unit l
  Eq-vec (succ-ℕ n) (x ∷ xs) (y ∷ ys) = (Id x y) × (Eq-vec n xs ys)

  refl-Eq-vec : (n : ℕ) → (u : vec A n) → Eq-vec n u u
  refl-Eq-vec zero-ℕ empty-vec = map-raise star
  pr1 (refl-Eq-vec (succ-ℕ n) (x ∷ xs)) = refl
  pr2 (refl-Eq-vec (succ-ℕ n) (x ∷ xs)) = refl-Eq-vec n xs

  Eq-eq-vec : (n : ℕ) → (u v : vec A n) → Id u v → Eq-vec n u v
  Eq-eq-vec n u .u refl = refl-Eq-vec n u

  eq-Eq-vec : (n : ℕ) → (u v : vec A n) → Eq-vec n u v → Id u v
  eq-Eq-vec zero-ℕ empty-vec empty-vec eq-vec = refl
  eq-Eq-vec (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , eqs) =
    ap (x ∷_) (eq-Eq-vec n xs ys eqs)

  is-retraction-eq-Eq-vec :
    (n : ℕ) → (u v : vec A n) →
    (p : u ＝ v) → eq-Eq-vec n u v (Eq-eq-vec n u v p) ＝ p
  is-retraction-eq-Eq-vec zero-ℕ empty-vec empty-vec refl = refl
  is-retraction-eq-Eq-vec (succ-ℕ n) (x ∷ xs) .(x ∷ xs) refl =
    left-whisker-comp² (x ∷_) (is-retraction-eq-Eq-vec n xs xs) refl

  square-Eq-eq-vec :
    (n : ℕ) (x : A) (u v : vec A n) (p : Id u v) →
    (Eq-eq-vec _ (x ∷ u) (x ∷ v) (ap (x ∷_) p)) ＝ (refl , (Eq-eq-vec n u v p))
  square-Eq-eq-vec zero-ℕ x empty-vec empty-vec refl = refl
  square-Eq-eq-vec (succ-ℕ n) a (x ∷ xs) (.x ∷ .xs) refl = refl

  is-section-eq-Eq-vec :
    (n : ℕ) (u v : vec A n) →
    (p : Eq-vec n u v) → Eq-eq-vec n u v (eq-Eq-vec n u v p) ＝ p
  is-section-eq-Eq-vec zero-ℕ empty-vec empty-vec (map-raise star) = refl
  is-section-eq-Eq-vec (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , ps) =
    ( square-Eq-eq-vec n x xs ys (eq-Eq-vec n xs ys ps)) ∙
    ( eq-pair-eq-fiber (is-section-eq-Eq-vec n xs ys ps))

  is-equiv-Eq-eq-vec :
    (n : ℕ) → (u v : vec A n) → is-equiv (Eq-eq-vec n u v)
  is-equiv-Eq-eq-vec n u v =
    is-equiv-is-invertible
      ( eq-Eq-vec n u v)
      ( is-section-eq-Eq-vec n u v)
      ( is-retraction-eq-Eq-vec n u v)

  extensionality-vec : (n : ℕ) → (u v : vec A n) → Id u v ≃ Eq-vec n u v
  extensionality-vec n u v = (Eq-eq-vec n u v , is-equiv-Eq-eq-vec n u v)
```

### The types of listed vectors and functional vectors are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  listed-vec-functional-vec : (n : ℕ) → functional-vec A n → vec A n
  listed-vec-functional-vec zero-ℕ v = empty-vec
  listed-vec-functional-vec (succ-ℕ n) v =
    head-functional-vec n v ∷
    listed-vec-functional-vec n (tail-functional-vec n v)

  functional-vec-vec : (n : ℕ) → vec A n → functional-vec A n
  functional-vec-vec zero-ℕ v = empty-functional-vec
  functional-vec-vec (succ-ℕ n) (a ∷ v) =
    cons-functional-vec n a (functional-vec-vec n v)

  is-section-functional-vec-vec :
    (n : ℕ) → (listed-vec-functional-vec n ∘ functional-vec-vec n) ~ id
  is-section-functional-vec-vec .zero-ℕ empty-vec = refl
  is-section-functional-vec-vec .(succ-ℕ _) (a ∷ v) =
    ap (λ u → a ∷ u) (is-section-functional-vec-vec _ v)

  abstract
    is-retraction-functional-vec-vec :
      (n : ℕ) → (functional-vec-vec n ∘ listed-vec-functional-vec n) ~ id
    is-retraction-functional-vec-vec zero-ℕ v = eq-htpy (λ ())
    is-retraction-functional-vec-vec (succ-ℕ n) v =
      eq-htpy
        ( λ where
          ( inl x) →
            htpy-eq
              ( is-retraction-functional-vec-vec n (tail-functional-vec n v))
              ( x)
          ( inr star) → refl)

  is-equiv-listed-vec-functional-vec :
    (n : ℕ) → is-equiv (listed-vec-functional-vec n)
  is-equiv-listed-vec-functional-vec n =
    is-equiv-is-invertible
      ( functional-vec-vec n)
      ( is-section-functional-vec-vec n)
      ( is-retraction-functional-vec-vec n)

  is-equiv-functional-vec-vec :
    (n : ℕ) → is-equiv (functional-vec-vec n)
  is-equiv-functional-vec-vec n =
    is-equiv-is-invertible
      ( listed-vec-functional-vec n)
      ( is-retraction-functional-vec-vec n)
      ( is-section-functional-vec-vec n)

  compute-vec : (n : ℕ) → functional-vec A n ≃ vec A n
  pr1 (compute-vec n) = listed-vec-functional-vec n
  pr2 (compute-vec n) = is-equiv-listed-vec-functional-vec n
```

### Characterizing the elementhood predicate

```agda
  is-in-functional-vec-is-in-vec :
    (n : ℕ) (v : vec A n) (x : A) →
    (x ∈-vec v) → (in-functional-vec n x (functional-vec-vec n v))
  is-in-functional-vec-is-in-vec (succ-ℕ n) (y ∷ l) x (is-head .x l) =
    (inr star) , refl
  is-in-functional-vec-is-in-vec (succ-ℕ n) (y ∷ l) x (is-in-tail .x x₁ l I) =
    inl (pr1 (is-in-functional-vec-is-in-vec n l x I)) ,
    pr2 (is-in-functional-vec-is-in-vec n l x I)

  is-in-vec-is-in-functional-vec :
    (n : ℕ) (v : vec A n) (x : A) →
    (in-functional-vec n x (functional-vec-vec n v)) → (x ∈-vec v)
  is-in-vec-is-in-functional-vec (succ-ℕ n) (y ∷ v) x (inl k , p) =
    is-in-tail x y v (is-in-vec-is-in-functional-vec n v x (k , p))
  is-in-vec-is-in-functional-vec (succ-ℕ n) (y ∷ v) _ (inr k , refl) =
    is-head (functional-vec-vec (succ-ℕ n) (y ∷ v) (inr k)) v
```

### The type of vectors of elements in a truncated type is truncated

#### The type of listed vectors of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-Eq-vec :
    (k : 𝕋) (n : ℕ) → is-trunc (succ-𝕋 k) A →
    (u v : vec A n) → is-trunc (k) (Eq-vec n u v)
  is-trunc-Eq-vec k zero-ℕ A-trunc empty-vec empty-vec =
    is-trunc-is-contr k is-contr-raise-unit
  is-trunc-Eq-vec k (succ-ℕ n) A-trunc (x ∷ xs) (y ∷ ys) =
    is-trunc-product k (A-trunc x y) (is-trunc-Eq-vec k n A-trunc xs ys)

  center-is-contr-vec :
    {n : ℕ} → is-contr A → vec A n
  center-is-contr-vec {zero-ℕ} H = empty-vec
  center-is-contr-vec {succ-ℕ n} H = center H ∷ center-is-contr-vec {n} H

  contraction-is-contr-vec' :
    {n : ℕ} (H : is-contr A) → (v : vec A n) →
    Eq-vec n (center-is-contr-vec H) v
  contraction-is-contr-vec' {zero-ℕ} H empty-vec =
    refl-Eq-vec {l} {A} 0 empty-vec
  pr1 (contraction-is-contr-vec' {succ-ℕ n} H (x ∷ v)) =
    eq-is-contr H
  pr2 (contraction-is-contr-vec' {succ-ℕ n} H (x ∷ v)) =
    contraction-is-contr-vec' {n} H v

  contraction-is-contr-vec :
    {n : ℕ} (H : is-contr A) → (v : vec A n) → (center-is-contr-vec H) ＝ v
  contraction-is-contr-vec {n} H v =
    eq-Eq-vec n (center-is-contr-vec H) v (contraction-is-contr-vec' H v)

  is-contr-vec :
    {n : ℕ} → is-contr A → is-contr (vec A n)
  pr1 (is-contr-vec H) = center-is-contr-vec H
  pr2 (is-contr-vec H) = contraction-is-contr-vec H

  is-trunc-vec :
    (k : 𝕋) → (n : ℕ) → is-trunc k A → is-trunc k (vec A n)
  is-trunc-vec neg-two-𝕋 n H = is-contr-vec H
  is-trunc-vec (succ-𝕋 k) n H x y =
    is-trunc-equiv k
      ( Eq-vec n x y)
      ( extensionality-vec n x y)
      ( is-trunc-Eq-vec k n H x y)
```

#### The type of functional vectors of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-functional-vec :
    (k : 𝕋) (n : ℕ) → is-trunc k A → is-trunc k (functional-vec A n)
  is-trunc-functional-vec k n H = is-trunc-function-type k H
```

### The type of vectors of elements in a set is a set

#### The type of listed vectors of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-vec : (n : ℕ) → is-set A -> is-set (vec A n)
  is-set-vec = is-trunc-vec zero-𝕋

vec-Set : {l : Level} → Set l → ℕ → Set l
pr1 (vec-Set A n) = vec (type-Set A) n
pr2 (vec-Set A n) = is-set-vec n (is-set-type-Set A)
```

#### The type of functional vectors of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-functional-vec : (n : ℕ) → is-set A → is-set (functional-vec A n)
  is-set-functional-vec = is-trunc-functional-vec zero-𝕋

functional-vec-Set : {l : Level} → Set l → ℕ → Set l
pr1 (functional-vec-Set A n) = functional-vec (type-Set A) n
pr2 (functional-vec-Set A n) = is-set-functional-vec n (is-set-type-Set A)
```

### Adding the tail to the head gives the same vector

#### Adding the tail to the head gives the same listed vector

```agda
module _
  {l : Level} {A : UU l}
  where

  cons-head-tail-vec :
    (n : ℕ) →
    (v : vec A (succ-ℕ n)) →
    ((head-vec v) ∷ (tail-vec v)) ＝ v
  cons-head-tail-vec n (x ∷ v) = refl
```

#### Adding the tail to the head gives the same functional vector

```agda
module _
  {l : Level} {A : UU l}
  where
  htpy-cons-head-tail-functional-vec :
    ( n : ℕ) →
    ( v : functional-vec A (succ-ℕ n)) →
    ( cons-functional-vec n
      ( head-functional-vec n v)
      ( tail-functional-vec n v)) ~
      ( v)
  htpy-cons-head-tail-functional-vec n v (inl x) = refl
  htpy-cons-head-tail-functional-vec n v (inr star) = refl

  cons-head-tail-functional-vec :
    ( n : ℕ) →
    ( v : functional-vec A (succ-ℕ n)) →
    ( cons-functional-vec n
      ( head-functional-vec n v)
      ( tail-functional-vec n v)) ＝
      ( v)
  cons-head-tail-functional-vec n v =
    eq-htpy (htpy-cons-head-tail-functional-vec n v)
```

### Computing the transport of a vector over its size

```agda
compute-tr-vec :
  {l : Level} {A : UU l}
  {n m : ℕ} (p : succ-ℕ n ＝ succ-ℕ m) (v : vec A n) (x : A) →
  tr (vec A) p (x ∷ v) ＝
  (x ∷ tr (vec A) (is-injective-succ-ℕ p) v)
compute-tr-vec refl v x = refl
```

### Back and forth between vectors and lists

```agda
module _
  {l : Level} {A : UU l}
  where

  list-vec : (n : ℕ) → vec A n → list A
  list-vec zero-ℕ _ = nil
  list-vec (succ-ℕ n) (x ∷ l) = cons x (list-vec n l)

  vec-list : (l : list A) → vec A (length-list l)
  vec-list nil = empty-vec
  vec-list (cons x l) = x ∷ vec-list l

  is-section-vec-list : (λ l → list-vec (length-list l) (vec-list l)) ~ id
  is-section-vec-list nil = refl
  is-section-vec-list (cons x l) = ap (cons x) (is-section-vec-list l)

  is-retraction-vec-list :
    ( λ (x : Σ ℕ (λ n → vec A n)) →
      ( length-list (list-vec (pr1 x) (pr2 x)) ,
        vec-list (list-vec (pr1 x) (pr2 x)))) ~
    id
  is-retraction-vec-list (zero-ℕ , empty-vec) = refl
  is-retraction-vec-list (succ-ℕ n , (x ∷ v)) =
    ap
      ( λ v → succ-ℕ (pr1 v) , (x ∷ (pr2 v)))
      ( is-retraction-vec-list (n , v))
```

### Back and forth between functional vectors and lists

```agda
module _
  {l : Level} {A : UU l}
  where

  list-functional-vec : (n : ℕ) → functional-vec A n → list A
  list-functional-vec zero-ℕ v =
    nil
  list-functional-vec (succ-ℕ n) v =
    cons (v (inr star)) (list-functional-vec n (v ∘ inl))

  functional-vec-list : (l : list A) → functional-vec A (length-list l)
  functional-vec-list nil =
    empty-functional-vec
  functional-vec-list (cons x l) =
    cons-functional-vec (length-list l) x (functional-vec-list l)
```
