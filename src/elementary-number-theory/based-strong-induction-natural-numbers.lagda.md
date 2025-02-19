# Based strong induction for the natural numbers

```agda
module elementary-number-theory.based-strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universal-property-contractible-types
open import foundation.universe-levels
```

</details>

## Idea

The **based strong induction principle** for the natural numbers asserts that
for any natural number `k : ℕ` and any family `P` of types over the natural
numbers equipped with

1. an element `p0 : P k`, and
2. a function
   `pS : (x : ℕ) → k ≤-ℕ x → ((y : ℕ) → k ≤-ℕ y ≤-ℕ x → P y) → P (x + 1)` there
   is a function

```text
  f := based-strong-ind-ℕ k P p0 pS : (x : ℕ) → k ≤-ℕ x → P k
```

satisfying

1. `f k K ＝ p0` for any `K : k ≤-ℕ k`, and
2. `f (n + 1) N' ＝ pS n N (λ m M H → f m M)` for any `N : k ≤-ℕ n` and any
   `N' : k ≤-ℕ n + 1`.

## Definitions

### The based `□`-modality on families indexed by `ℕ`

```agda
based-□-≤-ℕ : {l : Level} (k : ℕ) → (ℕ → UU l) → ℕ → UU l
based-□-≤-ℕ k P n = (m : ℕ) → (k ≤-ℕ m) → (m ≤-ℕ n) → P m

η-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → P n) →
  (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
η-based-□-≤-ℕ k f n N m M p = f m M

ε-based-□-≤-ℕ :
  {l : Level} (k : ℕ) {P : ℕ → UU l} → ((n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n) →
  ((n : ℕ) → k ≤-ℕ n → P n)
ε-based-□-≤-ℕ k f n N = f n N n N (refl-leq-ℕ n)
```

## Theorem

### The base case of the based strong induction principle

```agda
base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) → P k → based-□-≤-ℕ k P k
base-based-strong-ind-ℕ zero-ℕ P p zero-ℕ M H = p
base-based-strong-ind-ℕ (succ-ℕ k) P p0 (succ-ℕ m) =
  base-based-strong-ind-ℕ k (P ∘ succ-ℕ) p0 m

eq-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p : P k)
  (s t : leq-ℕ k k) → base-based-strong-ind-ℕ k P p k s t ＝ p
eq-base-based-strong-ind-ℕ zero-ℕ P p0 M H = refl
eq-base-based-strong-ind-ℕ (succ-ℕ k) P =
  eq-base-based-strong-ind-ℕ k (P ∘ succ-ℕ)
```

### The successor case of the based strong induction principle

```agda
cases-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n → P (succ-ℕ n))
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-based-strong-ind-ℕ k P pS n N f m M (inl H') = f m M H'
cases-succ-based-strong-ind-ℕ k P pS n N f .(succ-ℕ n) M (inr refl) = pS n N f

succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  ((x : ℕ) → leq-ℕ k x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) → leq-ℕ k n → based-□-≤-ℕ k P n → based-□-≤-ℕ k P (succ-ℕ n)
succ-based-strong-ind-ℕ k P pS n N f m M H =
  cases-succ-based-strong-ind-ℕ k P pS n N f m M (decide-leq-succ-ℕ m n H)

cases-htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  (H : leq-ℕ m n) →
  cases-succ-based-strong-ind-ℕ k P pS n N f m M c ＝ f m M H
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inl p) H =
  ap (f m M) (eq-is-prop (is-prop-leq-ℕ m n))
cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (inr α) H =
  ex-falso (neg-succ-leq-ℕ n (concatenate-eq-leq-ℕ n (inv α) H))

htpy-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n)
  (m : ℕ) (M : k ≤-ℕ m) (H : leq-ℕ m (succ-ℕ n)) (K : leq-ℕ m n) →
  succ-based-strong-ind-ℕ k P pS n N f m M H ＝ f m M K
htpy-succ-based-strong-ind-ℕ k P pS n N f m M H =
  cases-htpy-succ-based-strong-ind-ℕ k P pS n N f m M (decide-leq-succ-ℕ m n H)

cases-eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (c : (leq-ℕ (succ-ℕ n) n) + (succ-ℕ n ＝ succ-ℕ n)) →
  cases-succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M c ＝ pS n N f
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inl H) =
  ex-falso (neg-succ-leq-ℕ n H)
cases-eq-succ-based-strong-ind-ℕ k P pS n N f M (inr α) =
  ap
    ( (cases-succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M) ∘ inr)
    ( eq-is-prop' (is-set-ℕ (succ-ℕ n) (succ-ℕ n)) α refl)

eq-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l)
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  (n : ℕ) (N : k ≤-ℕ n) (f : based-□-≤-ℕ k P n) (M : k ≤-ℕ succ-ℕ n)
  (H : leq-ℕ (succ-ℕ n) (succ-ℕ n)) →
  succ-based-strong-ind-ℕ k P pS n N f (succ-ℕ n) M H ＝ pS n N f
eq-succ-based-strong-ind-ℕ k P pS n N f M H =
  cases-eq-succ-based-strong-ind-ℕ k P pS n N f M
    ( decide-leq-succ-ℕ (succ-ℕ n) n H)
```

### The inductive step in the proof of based strong induction

```agda
module _
  {l : Level} (k : ℕ) (P : ℕ → UU l) (z : based-□-≤-ℕ k P k)
  (s : (m : ℕ) → k ≤-ℕ m → based-□-≤-ℕ k P m → based-□-≤-ℕ k P (succ-ℕ m))
  where

  inductive-step-based-strong-ind-ℕ : (n : ℕ) → k ≤-ℕ n → based-□-≤-ℕ k P n
  inductive-step-based-strong-ind-ℕ =
    based-ind-ℕ k (based-□-≤-ℕ k P) z s

  compute-base-inductive-step-based-strong-ind-ℕ :
    (K : k ≤-ℕ k) (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ k) →
    inductive-step-based-strong-ind-ℕ k K m M H ＝ z m M H
  compute-base-inductive-step-based-strong-ind-ℕ K m M =
    htpy-eq
      ( htpy-eq
        ( htpy-eq
          ( compute-base-based-ind-ℕ k (based-□-≤-ℕ k P) z s K)
          ( m))
        ( M))

  compute-succ-inductive-step-based-strong-ind-ℕ :
    (n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
    (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ succ-ℕ n) →
    inductive-step-based-strong-ind-ℕ (succ-ℕ n) N' m M H ＝
    s n N (inductive-step-based-strong-ind-ℕ n N) m M H
  compute-succ-inductive-step-based-strong-ind-ℕ n N N' m M =
    htpy-eq
      ( htpy-eq
        ( htpy-eq
          ( compute-succ-based-ind-ℕ k (based-□-≤-ℕ k P) z s n N N')
          ( m))
        ( M))

  ap-inductive-step-based-strong-ind-ℕ :
    {n n' : ℕ} (p : n ＝ n') (N : k ≤-ℕ n) (N' : k ≤-ℕ n')
    (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ n) (H' : m ≤-ℕ n') →
    inductive-step-based-strong-ind-ℕ n N m M H ＝
    inductive-step-based-strong-ind-ℕ n' N' m M H'
  ap-inductive-step-based-strong-ind-ℕ refl N N' m M H H' =
    ap-binary
      ( λ u v → inductive-step-based-strong-ind-ℕ _ u m M v)
      ( eq-is-prop (is-prop-leq-ℕ k _))
      ( eq-is-prop (is-prop-leq-ℕ m _))
```

### The based strong induction principle

```agda
based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  (n : ℕ) → k ≤-ℕ n → P n
based-strong-ind-ℕ k P p0 pS =
  ε-based-□-≤-ℕ k
    ( inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS))

compute-base-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  based-strong-ind-ℕ k P p0 pS k (refl-leq-ℕ k) ＝ p0
compute-base-based-strong-ind-ℕ k P p0 pS =
  ( compute-base-inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( refl-leq-ℕ k)
    ( k)
    ( refl-leq-ℕ k)
    ( refl-leq-ℕ k)) ∙
  ( eq-base-based-strong-ind-ℕ k P p0 (refl-leq-ℕ k) (refl-leq-ℕ k))

cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  ( n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n)
  ( m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ succ-ℕ n) →
  ( c : (m ≤-ℕ n) + (m ＝ succ-ℕ n)) →
  ( α :
    (I : k ≤-ℕ n) (J : m ≤-ℕ n) →
    inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( n)
      ( I)
      ( m)
      ( M)
      ( J) ＝
    inductive-step-based-strong-ind-ℕ k P
      ( base-based-strong-ind-ℕ k P p0)
      ( succ-based-strong-ind-ℕ k P pS)
      ( m)
      ( M)
      ( m)
      ( M)
      ( refl-leq-ℕ m)) →
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( succ-ℕ n)
    ( N')
    ( m)
    ( M)
    ( H) ＝
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( m)
    ( M)
    ( m)
    ( M)
    ( refl-leq-ℕ m)
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ
  k P p0 pS n N N' m M H (inl H') α =
  ( compute-succ-inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( n)
    ( N)
    ( N')
    ( m)
    ( M)
    ( H)) ∙
  ( ( htpy-succ-based-strong-ind-ℕ k P pS n N
      ( inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        ( n)
        ( N))
      ( m)
      ( M)
      ( H)
      ( H')) ∙
    ( α N H'))
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ
  k P p0 pS n N N' m M H (inr p) α =
  ap-inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( inv p)
    ( N')
    ( M)
    ( m)
    ( M)
    ( H)
    ( refl-leq-ℕ m)

eq-inductive-step-compute-succ-based-strong-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (x : ℕ) → k ≤-ℕ x → based-□-≤-ℕ k P x → P (succ-ℕ x))
  (n : ℕ) (N : k ≤-ℕ n)
  (m : ℕ) (M : k ≤-ℕ m) (H : m ≤-ℕ n) →
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( n)
    ( N)
    ( m)
    ( M)
    ( H) ＝
  inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( m)
    ( M)
    ( m)
    ( M)
    ( refl-leq-ℕ m)
eq-inductive-step-compute-succ-based-strong-ind-ℕ k P p0 pS n N m M =
  based-ind-ℕ k
    ( λ i →
      (I : k ≤-ℕ i) (J : m ≤-ℕ i) →
      inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        ( i)
        ( I)
        ( m)
        ( M)
        ( J) ＝
      inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        ( m)
        ( M)
        ( m)
        ( M)
        ( refl-leq-ℕ m))
    ( λ I J →
      ap-inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        ( antisymmetric-leq-ℕ k m M J)
        ( I)
        ( M)
        ( m)
        ( M)
        ( J)
        ( refl-leq-ℕ m))
    ( λ i I' α I J →
      cases-eq-inductive-step-compute-succ-based-strong-ind-ℕ
        k P p0 pS i I' I m M
        ( J)
        ( decide-leq-succ-ℕ m i J)
        ( α))
    ( n)
    ( N)
    ( N)

compute-succ-based-strong-ind-ℕ :
  { l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  ( pS : (x : ℕ) → k ≤-ℕ x → (based-□-≤-ℕ k P x) → P (succ-ℕ x)) →
  ( n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
  based-strong-ind-ℕ k P p0 pS (succ-ℕ n) N' ＝
  pS n N (λ m M H → based-strong-ind-ℕ k P p0 pS m M)
compute-succ-based-strong-ind-ℕ k P p0 pS n N N' =
  ( compute-succ-inductive-step-based-strong-ind-ℕ k P
    ( base-based-strong-ind-ℕ k P p0)
    ( succ-based-strong-ind-ℕ k P pS)
    ( n)
    ( N)
    ( N')
    ( succ-ℕ n)
    ( N')
    ( refl-leq-ℕ (succ-ℕ n))) ∙
  ( ( eq-succ-based-strong-ind-ℕ k P pS n N
      ( inductive-step-based-strong-ind-ℕ k P
        ( base-based-strong-ind-ℕ k P p0)
        ( succ-based-strong-ind-ℕ k P pS)
        ( n)
        ( N))
      ( N')
      ( refl-leq-ℕ n)) ∙
    ( ap
      ( pS n N)
      ( eq-htpy
        ( λ m →
          eq-htpy
          ( eq-htpy ∘
            eq-inductive-step-compute-succ-based-strong-ind-ℕ
              k P p0 pS n N m)))))
```

## Corollaries

### Based strong induction for a type family defined for `n ≥ k`

```agda
based-□-≤-ℕ' : {l : Level} (k : ℕ) → ((n : ℕ) → (k ≤-ℕ n) → UU l) → ℕ → UU l
based-□-≤-ℕ' k P x = (m : ℕ) → (H : k ≤-ℕ m) → (m ≤-ℕ x) → P m H

compute-base-□-≤-ℕ' :
  {l : Level} (k : ℕ) (P : (n : ℕ) → (k ≤-ℕ n) → UU l) (x : ℕ) →
  based-□-≤-ℕ k (λ n → (H : k ≤-ℕ n) → P n H) x →
  based-□-≤-ℕ' k P x
compute-base-□-≤-ℕ' k P x p m H I = p m H I H

based-strong-ind-ℕ' :
  {l : Level} (k : ℕ) (P : (n : ℕ) → (k ≤-ℕ n → UU l))
  (p0 : P k (refl-leq-ℕ k)) →
  (pS : (x : ℕ) → (H : k ≤-ℕ x) →
    based-□-≤-ℕ' k P x →
    P (succ-ℕ x) (leq-succ-leq-ℕ k x H))
  (n : ℕ) → (H : k ≤-ℕ n) → P n H
based-strong-ind-ℕ' {l} k P p0 pS n H =
  based-strong-ind-ℕ
    ( k)
    ( λ n → (H : k ≤-ℕ n) → P n H)
    ( apply-dependent-universal-property-contr
      ( refl-leq-ℕ k)
      ( is-proof-irrelevant-is-prop (is-prop-leq-ℕ k k) (refl-leq-ℕ k))
      ( P k)
      ( p0))
    ( λ x H p →
      apply-dependent-universal-property-contr
        ( leq-succ-leq-ℕ k x H)
        ( is-proof-irrelevant-is-prop
          ( is-prop-leq-ℕ k (succ-ℕ x))
          ( leq-succ-leq-ℕ k x H))
        ( P (succ-ℕ x))
        ( pS x H ( compute-base-□-≤-ℕ' k P x p)))
    ( n)
    ( H)
    ( H)
```
