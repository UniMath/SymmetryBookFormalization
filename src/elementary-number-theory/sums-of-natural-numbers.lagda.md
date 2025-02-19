# Sums of natural numbers

```agda
module elementary-number-theory.sums-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import lists.lists

open import univalent-combinatorics.counting
open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Consider a family of
[natural numbers](elementary-number-theory.natural-numbers.md)
$a : \mathsf{Fin}(n) → \mathbb{N}$ indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md)
$\mathsf{Fin}(n)$. The
{{#concept "sum" Disambiguation="natural numbers" Agda=sum-Fin-ℕ}}

$$
\sum_{0\leq i<n}a_i
$$

of the values of $a$ is defined by iteratively
[adding](elementary-number-theory.addition-natural-numbers.md) all the numbers
$a_0,\ldots,a_{n-1}$.

There are several variatiions of sums of natural numbers: We can add natural
numbers in [lists](lists.lists.md), families of natural numbers indexed by a
type equipped with a [counting](univalent-combinatorics.counting.md), and
families of natural numbers indexed by an arbitrary
[finite type](univalent-combinatorics.finite-types.md) (not yet implemented).
Furthermore, we can add families of natural numbers indexed by natural numbers
within a fixed [bound](elementary-number-theory.inequality-natural-numbers.md).

The sum of a family of natural numbers $a$ indexed by a type $I$ is the unique
natural number $\sum_{(i : I)}a_i$ such that for any $i_0 : I$ we have an
[identification](foundation-core.identity-types.md)

$$
\sum_{(i:I)} a_i = \left(\sum_{(i:I\setminus\{i₀\})} a_i\right)+a_{i_0}.
$$

## Definition

### Sums of lists of natural numbers

```agda
sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list 0 add-ℕ
```

### Sums of natural numbers indexed by a standard finite type

```agda
sum-Fin-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
sum-Fin-ℕ zero-ℕ f = zero-ℕ
sum-Fin-ℕ (succ-ℕ k) f = (sum-Fin-ℕ k (λ x → f (inl x))) +ℕ (f (inr star))
```

### Sums of natural numbers indexed by a type equipped with a counting

```agda
sum-count-ℕ : {l : Level} {A : UU l} (e : count A) → (f : A → ℕ) → ℕ
sum-count-ℕ (pair k e) f = sum-Fin-ℕ k (f ∘ (map-equiv e))
```

### Bounded sums of natural numbers

This function defines the sum of a family of natural numbers indexed by natural
numbers up to, and including, a given upper bound.

```agda
bounded-sum-ℕ :
  (N : ℕ) → ((i : ℕ) → leq-ℕ i N → ℕ) → ℕ
bounded-sum-ℕ zero-ℕ f =
  f 0 (refl-leq-ℕ 0)
bounded-sum-ℕ (succ-ℕ N) f =
  add-ℕ
    ( bounded-sum-ℕ N (λ x H → f x (leq-succ-leq-ℕ x N H)))
    ( f (succ-ℕ N) (refl-leq-ℕ N))
```

### Strictly bounded sums of natural numbers

This function defines the sum of a family of natural numbers indexed by natural
numbers up to, but not including, a given upper bound.

```agda
strictly-bounded-sum-ℕ :
  (u : ℕ) → ((x : ℕ) → le-ℕ x u → ℕ) → ℕ
strictly-bounded-sum-ℕ zero-ℕ f =
  zero-ℕ
strictly-bounded-sum-ℕ (succ-ℕ u) f =
  add-ℕ
    ( strictly-bounded-sum-ℕ u (λ x H → f x (preserves-le-succ-ℕ x u H)))
    ( f u (succ-le-ℕ u))
```

## Properties

### Sums are invariant under homotopy

```agda
abstract
  htpy-sum-Fin-ℕ :
    (k : ℕ) {f g : Fin k → ℕ} (H : f ~ g) → sum-Fin-ℕ k f ＝ sum-Fin-ℕ k g
  htpy-sum-Fin-ℕ zero-ℕ H = refl
  htpy-sum-Fin-ℕ (succ-ℕ k) H =
    ap-add-ℕ
      ( htpy-sum-Fin-ℕ k (λ x → H (inl x)))
      ( H (inr star))

abstract
  htpy-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) {f g : A → ℕ} (H : f ~ g) →
    sum-count-ℕ e f ＝ sum-count-ℕ e g
  htpy-sum-count-ℕ (pair k e) H = htpy-sum-Fin-ℕ k (H ·r (map-equiv e))
```

### Summing up the same value `m` times is multiplication by `m`

```agda
abstract
  constant-sum-Fin-ℕ :
    (m n : ℕ) → sum-Fin-ℕ m (const (Fin m) n) ＝ m *ℕ n
  constant-sum-Fin-ℕ zero-ℕ n = refl
  constant-sum-Fin-ℕ (succ-ℕ m) n = ap (_+ℕ n) (constant-sum-Fin-ℕ m n)

abstract
  constant-sum-count-ℕ :
    {l : Level} {A : UU l} (e : count A) (n : ℕ) →
    sum-count-ℕ e (const A n) ＝ (number-of-elements-count e) *ℕ n
  constant-sum-count-ℕ (pair m e) n = constant-sum-Fin-ℕ m n
```

### Each of the summands is less than or equal to the total sum

```agda
leq-sum-Fin-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (x : Fin k) → f x ≤-ℕ sum-Fin-ℕ k f
leq-sum-Fin-ℕ (succ-ℕ k) f (inl x) =
  transitive-leq-ℕ
    ( f (inl x))
    ( sum-Fin-ℕ k (f ∘ inl))
    ( sum-Fin-ℕ (succ-ℕ k) f)
    ( leq-add-ℕ (sum-Fin-ℕ k (f ∘ inl)) (f (inr _)))
    ( leq-sum-Fin-ℕ k (f ∘ inl) x)
leq-sum-Fin-ℕ (succ-ℕ k) f (inr x) =
  leq-add-ℕ' (f (inr x)) (sum-Fin-ℕ k (f ∘ inl))
```

### The difference between a summand and the sum of natural numbers

```agda
sum-skip-Fin-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) → ℕ
sum-skip-Fin-ℕ (succ-ℕ k) f i =
  sum-Fin-ℕ k (f ∘ skip-Fin k i)

eq-sum-skip-Fin-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) →
  sum-skip-Fin-ℕ k f i +ℕ f i ＝ sum-Fin-ℕ k f
eq-sum-skip-Fin-ℕ (succ-ℕ zero-ℕ) f (inr star) =
  refl
eq-sum-skip-Fin-ℕ (succ-ℕ (succ-ℕ k)) f (inl i) =
  ( right-swap-add-ℕ
    ( sum-Fin-ℕ k (f ∘ inl ∘ skip-Fin k i))
    ( f (inr star))
    ( f (inl i))) ∙
  ( ap (_+ℕ f (inr star)) (eq-sum-skip-Fin-ℕ (succ-ℕ k) (f ∘ inl) i))
eq-sum-skip-Fin-ℕ (succ-ℕ (succ-ℕ k)) f (inr star) =
  refl

compute-dist-summand-sum-Fin-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) →
  dist-ℕ (f i) (sum-Fin-ℕ k f) ＝ sum-skip-Fin-ℕ k f i
compute-dist-summand-sum-Fin-ℕ k f i =
  inv
    ( rewrite-left-add-dist-ℕ
      ( sum-skip-Fin-ℕ k f i)
      ( f i)
      ( sum-Fin-ℕ k f)
      ( eq-sum-skip-Fin-ℕ k f i))
```
