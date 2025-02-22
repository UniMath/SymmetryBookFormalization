# Well-ordering principles for the integers

```agda
module elementary-number-theory.well-ordering-principles-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The [poset of integers](elementary-number-theory.inequality-integers.md) does
not satisfy the
[well-ordering principle of the natural numbers](elementary-number-theory.well-ordering-principle-natural-numbers.md).
However, there are several useful approximations of the well-ordering principle
for the [integers](elementary-number-theory.integers.md) that are worth
recording:

- For every family `A` of [decidable types](foundation.decidable-types.md) over
  `ℤ` that is bounded from below and comes equipped with an integer `a` and an
  element of type `A a`, we can find a least integer `a₀` equipped with an
  element of type `A a₀`. Here, a type family `A` over the integers is bounded
  from below if it comes equipped with a
  [lower bound](order-theory.lower-bounds-posets.md) `b` such that `b ≤ x` for
  all `x : ℤ` equipped with an element of type `A x`.
- For every family `A` of [decidable types](foundation.decidable-types.md) over
  `ℤ` that is bounded from above and comes equipped with an integer `a` and an
  element of type `A a`, we can find a largest integer `a₀` equipped with an
  element of type `A a₀`. Here, a type family `A` over the integers is bounded
  from above if it comes equipped with an
  [upper bound](order-theory.lower-bounds-posets.md) `b` such that `x ≤ b` for
  all `x : ℤ` equipped with an element of type `A x`.

## Definitions

### Minimal elements

```agda
module _
  {l1 : Level} (A : ℤ → UU l1)
  where

  minimal-element-ℤ : UU l1
  minimal-element-ℤ = Σ ℤ (λ a → A a × ((b : ℤ) → A b → a ≤-ℤ b))
```

### Translations of minimal elements

```agda
module _
  {l1 : Level} (A : ℤ → UU l1) (a : ℤ)
  where

  translation-minimal-element-ℤ :
    minimal-element-ℤ (λ x → A (x +ℤ a)) → minimal-element-ℤ A
  translation-minimal-element-ℤ =
    map-Σ
      ( λ x → A x × ((y : ℤ) → A y → x ≤-ℤ y))
      ( λ x → x +ℤ a)
      ( λ x (b , H) →
        ( b ,
          λ y c →
          inv-transpose-right-summand-leq-ℤ' x y a
            ( H ( diff-ℤ y a)
                ( tr A (inv (is-section-right-add-neg-ℤ a y)) c))))
```

### Maximal elements

```agda
module _
  {l1 : Level} (A : ℤ → UU l1)
  where

  maximal-element-ℤ : UU l1
  maximal-element-ℤ = Σ ℤ (λ a → A a × ((b : ℤ) → A b → b ≤-ℤ a))
```

### Reflections of minimal and maximal elements

```agda
module _
  {l1 : Level} (A : ℤ → UU l1)
  where

  reflect-minimal-element-ℤ :
    minimal-element-ℤ (A ∘ neg-ℤ) → maximal-element-ℤ A
  reflect-minimal-element-ℤ =
    map-Σ
      ( λ x → A x × ((y : ℤ) → A y → y ≤-ℤ x))
      ( neg-ℤ)
      ( λ x (a , H) →
        ( a ,
          λ y b →
          transpose-right-neg-leq-ℤ y x
            ( H (neg-ℤ y) (tr A (inv (neg-neg-ℤ y)) b))))

  reflect-maximal-element-ℤ :
    maximal-element-ℤ (A ∘ neg-ℤ) → minimal-element-ℤ A
  reflect-maximal-element-ℤ =
    map-Σ
      ( λ x → A x × ((y : ℤ) → A y → x ≤-ℤ y))
      ( neg-ℤ)
       λ x (a , H) →
        ( a ,
          λ y b →
          transpose-left-neg-leq-ℤ x y
            ( H (neg-ℤ y) (tr A (inv (neg-neg-ℤ y)) b)))
```

### The well-ordering principle for the nonnegative integers

The
{{#concept "well-ordering principle for the nonnegative integers" Agda=well-ordering-principle-nonnegative-ℤ}}
states that for any family `A` of decidable types over `ℤ` such that the
implication `A x → is-nonnegative-ℤ x` holds for any `x : ℤ`, if we are given an
element `(a , a) : Σ ℤ A` then there is a minimal integer `a₀` equipped with an
element of type `A a₀`.

```agda
module _
  {l1 : Level} {A : ℤ → UU l1} (d : (x : ℤ) → is-decidable (A x))
  where

  well-ordering-principle-nonnegative-ℤ' :
    ((x : ℤ) → A x → is-nonnegative-ℤ x) →
    minimal-element-ℕ (A ∘ int-ℕ) → minimal-element-ℤ A
  pr1 (well-ordering-principle-nonnegative-ℤ' H (n , x , K)) =
    int-ℕ n
  pr1 (pr2 (well-ordering-principle-nonnegative-ℤ' H (n , x , K))) =
    x
  pr2 (pr2 (well-ordering-principle-nonnegative-ℤ' H (n , x , K))) b y =
    concatenate-leq-eq-ℤ (int-ℕ n) (leq-int-ℕ n m (K m (tr A (inv α) y))) α
    where

    m : ℕ
    m = nat-nonnegative-ℤ (b , H b y)

    α : int-ℕ m ＝ b
    α = ap pr1 (is-section-nat-nonnegative-ℤ (b , H b y))

  well-ordering-principle-nonnegative-ℤ :
    ((x : ℤ) → A x → is-nonnegative-ℤ x) → Σ ℤ A → minimal-element-ℤ A
  well-ordering-principle-nonnegative-ℤ H (a , x) =
    well-ordering-principle-nonnegative-ℤ' H
      ( well-ordering-principle-ℕ
        ( A ∘ int-ℕ)
        ( d ∘ int-ℕ)
        ( map-Σ
          ( A ∘ int-ℕ)
          ( nat-nonnegative-ℤ)
          ( λ x → id)
          ( ( a , H a x) ,
            ( tr A
              ( inv (ap pr1 (is-section-nat-nonnegative-ℤ (a , H a x))))
              ( x)))))
```

### The well-ordering principle for the positive integers

The
{{#concept "well-ordering principle for the positive integers" Agda=well-ordering-principle-positive-ℤ}}
states that for any family `A` of decidable types over `ℤ` such that the
implication `A x → is-positive-ℤ x` holds for any `x : ℤ`, if we are given an
element `(a , a) : Σ ℤ A` then there is a minimal integer `a₀` equipped with an
element of type `A a₀`.

```agda
module _
  {l1 : Level} {A : ℤ → UU l1} (d : (x : ℤ) → is-decidable (A x))
  where

  well-ordering-principle-positive-ℤ :
    ((x : ℤ) → A x → is-positive-ℤ x) → Σ ℤ A → minimal-element-ℤ A
  well-ordering-principle-positive-ℤ H (a , x) =
    well-ordering-principle-nonnegative-ℤ d
      ( λ b y → is-nonnegative-is-positive-ℤ (H b y))
      ( a , x)
```

### The lower bounded well-ordering principle for the integers

```agda
module _
  {l1 : Level} {A : ℤ → UU l1} (d : (x : ℤ) → is-decidable (A x))
  (b : ℤ) (H : (a : ℤ) → A a → b ≤-ℤ a) ((a , x) : Σ ℤ A)
  where

  lower-bounded-well-ordering-principle-ℤ :
    minimal-element-ℤ A
  lower-bounded-well-ordering-principle-ℤ =
    translation-minimal-element-ℤ A b
      ( well-ordering-principle-nonnegative-ℤ
        ( λ c → d (c +ℤ b))
        ( λ c z →
          tr
            ( is-nonnegative-ℤ)
            ( is-retraction-right-add-neg-ℤ b c)
            ( H (c +ℤ b) z) )
        ( diff-ℤ a b , tr A (inv (is-section-right-add-neg-ℤ b a)) x))

  integer-lower-bounded-well-ordering-principle-ℤ : ℤ
  integer-lower-bounded-well-ordering-principle-ℤ =
    pr1 lower-bounded-well-ordering-principle-ℤ

  structure-lower-bounded-well-ordering-principle-ℤ :
    A integer-lower-bounded-well-ordering-principle-ℤ
  structure-lower-bounded-well-ordering-principle-ℤ =
    pr1 (pr2 lower-bounded-well-ordering-principle-ℤ)

  is-least-element-integer-lower-bounded-well-ordering-principle-ℤ :
    (a : ℤ) → A a → integer-lower-bounded-well-ordering-principle-ℤ ≤-ℤ a
  is-least-element-integer-lower-bounded-well-ordering-principle-ℤ =
    pr2 (pr2 lower-bounded-well-ordering-principle-ℤ)
```

### The upper bounded well-ordering principle for the integers

```agda
module _
  {l1 : Level} {A : ℤ → UU l1} (d : (x : ℤ) → is-decidable (A x))
  (b : ℤ) (H : (a : ℤ) → A a → a ≤-ℤ b) ((a , x) : Σ ℤ A)
  where

  upper-bounded-well-ordering-principle-ℤ :
    maximal-element-ℤ A
  upper-bounded-well-ordering-principle-ℤ =
    reflect-minimal-element-ℤ A
      ( lower-bounded-well-ordering-principle-ℤ
        ( λ x → d (neg-ℤ x))
        ( neg-ℤ b)
        ( λ x y → transpose-left-neg-leq-ℤ b x (H (neg-ℤ x) y))
        ( neg-ℤ a , tr A (inv (neg-neg-ℤ a)) x))

  integer-upper-bounded-well-ordering-principle-ℤ : ℤ
  integer-upper-bounded-well-ordering-principle-ℤ =
    pr1 upper-bounded-well-ordering-principle-ℤ

  structure-upper-bounded-well-ordering-principle-ℤ :
    A integer-upper-bounded-well-ordering-principle-ℤ
  structure-upper-bounded-well-ordering-principle-ℤ =
    pr1 (pr2 upper-bounded-well-ordering-principle-ℤ)

  is-largest-element-integer-upper-bounded-well-ordering-principle-ℤ :
    (a : ℤ) → A a → a ≤-ℤ integer-upper-bounded-well-ordering-principle-ℤ
  is-largest-element-integer-upper-bounded-well-ordering-principle-ℤ =
    pr2 (pr2 upper-bounded-well-ordering-principle-ℤ)
```
