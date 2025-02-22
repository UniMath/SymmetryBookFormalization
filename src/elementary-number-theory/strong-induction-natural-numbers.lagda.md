# The strong induction principle for the natural numbers

```agda
module elementary-number-theory.strong-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The strong induction principle allows one to assume in the inductive step that
the inductive hypothesis is satisfied at all smaller values.

## Definition

### The `□`-modality on families indexed by `ℕ`

```agda
□-≤-ℕ : {l : Level} → (ℕ → UU l) → ℕ → UU l
□-≤-ℕ P n = (m : ℕ) → (m ≤-ℕ n) → P m

η-□-≤-ℕ : {l : Level} {P : ℕ → UU l} → ((n : ℕ) → P n) → (n : ℕ) → □-≤-ℕ P n
η-□-≤-ℕ f n m p = f m

ε-□-≤-ℕ :
  {l : Level} {P : ℕ → UU l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ f n = f n n (refl-leq-ℕ n)
```

## Theorem

### The base case of the strong induction principle

```agda
zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  zero-strong-ind-ℕ P p0 zero-ℕ t ＝ p0
eq-zero-strong-ind-ℕ P p0 t = refl
```

### The successor case of the strong induction principle

```agda
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : (leq-ℕ m n) + (m ＝ succ-ℕ n)) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p)

cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : (leq-ℕ m k) + (m ＝ succ-ℕ k)) →
  (q : leq-ℕ m k) →
  ( cases-succ-strong-ind-ℕ P pS k H m c) ＝
  ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (eq-is-prop (is-prop-leq-ℕ m k))
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso (neg-succ-leq-ℕ k (concatenate-eq-leq-ℕ k (inv α) q))

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  ( succ-strong-ind-ℕ P pS k H m p) ＝
  ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p) q

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : (leq-ℕ (succ-ℕ k) k) + (succ-ℕ k ＝ succ-ℕ k)) →
  ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c)) ＝
  ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso (neg-succ-leq-ℕ k p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap
    ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
    ( eq-is-prop' (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p)) ＝
  ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (decide-leq-succ-ℕ (succ-ℕ k) k p)
```

### The inductive step

```agda
induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ P p0 pS zero-ℕ = p0
induction-strong-ind-ℕ P p0 pS (succ-ℕ n) =
  pS n (induction-strong-ind-ℕ P p0 pS n)

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : □-≤-ℕ P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  ( induction-strong-ind-ℕ P p0 pS (succ-ℕ n)) ＝
  ( pS n (induction-strong-ind-ℕ P p0 pS n))
computation-succ-strong-ind-ℕ P p0 pS n = refl
```

### The strong induction principle

```agda
strong-ind-ℕ :
  {l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ P p0 pS =
  ε-□-≤-ℕ
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

compute-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  strong-ind-ℕ P p0 pS zero-ℕ ＝ p0
compute-zero-strong-ind-ℕ P p0 pS = refl

cases-eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
      ( λ k z m₁ z₁ →
        cases-succ-strong-ind-ℕ P pS k z m₁ (decide-leq-succ-ℕ m₁ k z₁))
      n m p) ＝
    ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : (leq-ℕ m n) + (m ＝ succ-ℕ n)) →
  ( succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n) m p) ＝
  ( strong-ind-ℕ P p0 pS m)
cases-eq-compute-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-compute-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (decide-leq-succ-ℕ m k p₁))
          n)
        ( succ-ℕ n))
      ( decide-leq-refl-succ-ℕ)))

eq-compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
    ( λ k z m₁ z₁ →
      cases-succ-strong-ind-ℕ P pS k z m₁ (decide-leq-succ-ℕ m₁ k z₁))
    n m p) ＝
  ( strong-ind-ℕ P p0 pS m)
eq-compute-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ _ = refl
eq-compute-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-compute-succ-strong-ind-ℕ P p0 pS n
    ( eq-compute-succ-strong-ind-ℕ P p0 pS n) m p
    ( decide-leq-succ-ℕ m n p)

compute-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  strong-ind-ℕ P p0 pS (succ-ℕ n) ＝ pS n (λ m p → strong-ind-ℕ P p0 pS m)
compute-succ-strong-ind-ℕ P p0 pS n =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( refl-leq-ℕ n)) ∙
  ( ap
    ( pS n)
    ( eq-htpy (eq-htpy ∘ eq-compute-succ-strong-ind-ℕ P p0 pS n)))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( h zero-ℕ ＝ p0) ×
      ( (n : ℕ) → h (succ-ℕ n) ＝ pS n (λ m p → h m)))
pr1 (total-strong-ind-ℕ P p0 pS) = strong-ind-ℕ P p0 pS
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-zero-strong-ind-ℕ P p0 pS
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = compute-succ-strong-ind-ℕ P p0 pS
```

### Strong recursion

```agda
module _
  {l : Level} {A : UU l} (a0 : A) (aS : (k : ℕ) → (□-≤-ℕ (λ _ → A) k) → A)
  where

  strong-rec-ℕ : ℕ → A
  strong-rec-ℕ = strong-ind-ℕ (λ _ → A) a0 aS

  compute-zero-strong-rec-ℕ : strong-rec-ℕ 0 ＝ a0
  compute-zero-strong-rec-ℕ = compute-zero-strong-ind-ℕ (λ _ → A) a0 aS

  compute-succ-strong-rec-ℕ :
    (n : ℕ) → strong-rec-ℕ (succ-ℕ n) ＝ aS n (λ m _ → strong-rec-ℕ m)
  compute-succ-strong-rec-ℕ =
    compute-succ-strong-ind-ℕ (λ _ → A) a0 aS
```

## See also

- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).
