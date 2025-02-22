# The standard finite types

```agda
module univalent-combinatorics.standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalence-injective-type-families
open import foundation.equivalences
open import foundation.equivalences-maybe
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.noncontractible-types
open import foundation.preunivalent-type-families
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The standard finite types are defined inductively by `Fin 0 := empty` and
`Fin (n+1) := (Fin n) + 1`. **Note** that the outermost coproduct (i.e. the
`inr` injection) is the _top_ element, when `Fin n` is considered as an initial
segment of `ℕ`.

## Definition

### The standard finite types in universe level zero

```agda
Fin-Set : ℕ → Set lzero
Fin-Set zero-ℕ = empty-Set
Fin-Set (succ-ℕ n) = coproduct-Set (Fin-Set n) unit-Set

Fin : ℕ → UU lzero
Fin n = type-Set (Fin-Set n)

is-set-Fin : (n : ℕ) → is-set (Fin n)
is-set-Fin n = is-set-type-Set (Fin-Set n)

inl-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
inl-Fin k = inl

emb-inl-Fin : (k : ℕ) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-inl-Fin k) = inl-Fin k
pr2 (emb-inl-Fin k) = is-emb-inl

neg-one-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-one-Fin k = inr star

is-neg-one-Fin : (k : ℕ) → Fin k → UU lzero
is-neg-one-Fin (succ-ℕ k) x = x ＝ neg-one-Fin k

neg-two-Fin : (k : ℕ) → Fin (succ-ℕ k)
neg-two-Fin zero-ℕ = inr star
neg-two-Fin (succ-ℕ k) = inl (inr star)

is-inl-Fin : (k : ℕ) → Fin (succ-ℕ k) → UU lzero
is-inl-Fin k x = Σ (Fin k) (λ y → inl y ＝ x)

is-neg-one-is-not-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  ¬ (is-inl-Fin k x) → is-neg-one-Fin (succ-ℕ k) x
is-neg-one-is-not-inl-Fin k (inl x) H = ex-falso (H (x , refl))
is-neg-one-is-not-inl-Fin k (inr star) H = refl

inr-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
inr-Fin (succ-ℕ k) (inl x) = inl (inr-Fin k x)
inr-Fin (succ-ℕ k) (inr star) = inr star

neq-inl-Fin-inr-Fin :
  (n : ℕ) → (k : Fin n) → inl-Fin n k ≠ inr-Fin n k
neq-inl-Fin-inr-Fin (succ-ℕ n) (inl k) =
  neq-inl-Fin-inr-Fin n k ∘ is-injective-inl
neq-inl-Fin-inr-Fin (succ-ℕ n) (inr star) = neq-inl-inr

neq-inr-Fin-inl-Fin :
  (n : ℕ) → (k : Fin n) → inr-Fin n k ≠ inl-Fin n k
neq-inr-Fin-inl-Fin (succ-ℕ n) (inl k) =
  neq-inr-Fin-inl-Fin n k ∘ is-injective-inl
neq-inr-Fin-inl-Fin (succ-ℕ n) (inr k) = neq-inr-inl
```

### The standard finite types in an arbitrary universe

```agda
raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

compute-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
compute-raise-Fin l k = compute-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

raise-Fin-Set : (l : Level) (k : ℕ) → Set l
raise-Fin-Set l k = raise-Set l (Fin-Set k)
```

## Properties

### Being on the left is decidable

```agda
is-decidable-is-inl-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin k x)
is-decidable-is-inl-Fin k (inl x) = inl (x , refl)
is-decidable-is-inl-Fin k (inr star) = inr α
  where
  α : is-inl-Fin k (inr star) → empty
  α (y , ())
```

### `Fin 1` is contractible

```agda
map-equiv-Fin-1 : Fin 1 → unit
map-equiv-Fin-1 (inr x) = x

map-inv-equiv-Fin-1 : unit → Fin 1
map-inv-equiv-Fin-1 x = inr x

is-section-map-inv-equiv-Fin-1 :
  ( map-equiv-Fin-1 ∘ map-inv-equiv-Fin-1) ~ id
is-section-map-inv-equiv-Fin-1 _ = refl

is-retraction-map-inv-equiv-Fin-1 :
  ( map-inv-equiv-Fin-1 ∘ map-equiv-Fin-1) ~ id
is-retraction-map-inv-equiv-Fin-1 (inr _) = refl

is-equiv-map-equiv-Fin-1 : is-equiv map-equiv-Fin-1
is-equiv-map-equiv-Fin-1 =
  is-equiv-is-invertible
    map-inv-equiv-Fin-1
    is-section-map-inv-equiv-Fin-1
    is-retraction-map-inv-equiv-Fin-1

equiv-Fin-1 : Fin 1 ≃ unit
pr1 equiv-Fin-1 = map-equiv-Fin-1
pr2 equiv-Fin-1 = is-equiv-map-equiv-Fin-1

is-contr-Fin-1 : is-contr (Fin 1)
is-contr-Fin-1 = is-contr-equiv unit equiv-Fin-1 is-contr-unit

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  neq-inl-inr (eq-is-contr' C (neg-two-Fin (succ-ℕ k)) (neg-one-Fin (succ-ℕ k)))
```

### The zero elements in the standard finite types

```agda
zero-Fin : (k : ℕ) → Fin (succ-ℕ k)
zero-Fin zero-ℕ = inr star
zero-Fin (succ-ℕ k) = inl (zero-Fin k)

is-zero-Fin : (k : ℕ) → Fin k → UU lzero
is-zero-Fin (succ-ℕ k) x = x ＝ zero-Fin k

is-zero-Fin' : (k : ℕ) → Fin k → UU lzero
is-zero-Fin' (succ-ℕ k) x = zero-Fin k ＝ x

is-nonzero-Fin : (k : ℕ) → Fin k → UU lzero
is-nonzero-Fin (succ-ℕ k) x = ¬ (is-zero-Fin (succ-ℕ k) x)
```

### The successor function on the standard finite types

```agda
skip-zero-Fin : (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-zero-Fin (succ-ℕ k) (inl x) = inl (skip-zero-Fin k x)
skip-zero-Fin (succ-ℕ k) (inr star) = inr star

succ-Fin : (k : ℕ) → Fin k → Fin k
succ-Fin (succ-ℕ k) (inl x) = skip-zero-Fin k x
succ-Fin (succ-ℕ k) (inr star) = (zero-Fin k)

Fin-Type-With-Endomorphism : ℕ → Type-With-Endomorphism lzero
pr1 (Fin-Type-With-Endomorphism k) = Fin k
pr2 (Fin-Type-With-Endomorphism k) = succ-Fin k
```

### The bounded successor function on the standard finite types

```agda
bounded-succ-Fin : (k : ℕ) → Fin k → Fin k
bounded-succ-Fin (succ-ℕ k) (inl x) = skip-zero-Fin k x
bounded-succ-Fin (succ-ℕ k) (inr star) = inr star
```

### The inclusion of `Fin k` into `ℕ`

```agda
nat-Fin : (k : ℕ) → Fin k → ℕ
nat-Fin (succ-ℕ k) (inl x) = nat-Fin k x
nat-Fin (succ-ℕ k) (inr x) = k

nat-Fin-reverse : (k : ℕ) → Fin k → ℕ
nat-Fin-reverse (succ-ℕ k) (inl x) = succ-ℕ (nat-Fin k x)
nat-Fin-reverse (succ-ℕ k) (inr x) = 0

strict-upper-bound-nat-Fin : (k : ℕ) (x : Fin k) → le-ℕ (nat-Fin k x) k
strict-upper-bound-nat-Fin (succ-ℕ k) (inl x) =
  transitive-le-ℕ
    ( nat-Fin k x)
    ( k)
    ( succ-ℕ k)
    ( succ-le-ℕ k)
    ( strict-upper-bound-nat-Fin k x)
strict-upper-bound-nat-Fin (succ-ℕ k) (inr star) =
  succ-le-ℕ k

upper-bound-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → leq-ℕ (nat-Fin (succ-ℕ k) x) k
upper-bound-nat-Fin zero-ℕ (inr star) = star
upper-bound-nat-Fin (succ-ℕ k) (inl x) =
  leq-succ-leq-ℕ (nat-Fin (succ-ℕ k) x) k (upper-bound-nat-Fin k x)
upper-bound-nat-Fin (succ-ℕ k) (inr star) = refl-leq-ℕ (succ-ℕ k)

upper-bound-nat-Fin' :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k x) k
upper-bound-nat-Fin' k x =
  leq-le-ℕ (nat-Fin k x) k (strict-upper-bound-nat-Fin k x)

is-injective-nat-Fin : (k : ℕ) → is-injective (nat-Fin k)
is-injective-nat-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-nat-Fin k p)
is-injective-nat-Fin (succ-ℕ k) {inl x} {inr star} p =
  ex-falso
    ( neq-le-ℕ
      ( nat-Fin k x)
      ( nat-Fin (succ-ℕ k) (inr star))
      ( strict-upper-bound-nat-Fin k x)
      ( p))
is-injective-nat-Fin (succ-ℕ k) {inr star} {inl y} p =
  ex-falso
    ( neq-le-ℕ
      ( nat-Fin (succ-ℕ k) (inl y))
      ( nat-Fin (succ-ℕ k) (inr star))
      ( strict-upper-bound-nat-Fin k y)
      ( inv p))
is-injective-nat-Fin (succ-ℕ k) {inr star} {inr star} p =
  refl

is-emb-nat-Fin : (k : ℕ) → is-emb (nat-Fin k)
is-emb-nat-Fin k = is-emb-is-injective is-set-ℕ (is-injective-nat-Fin k)

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
pr1 (emb-nat-Fin k) = nat-Fin k
pr2 (emb-nat-Fin k) = is-emb-nat-Fin k
```

```agda
is-zero-nat-zero-Fin : {k : ℕ} → is-zero-ℕ (nat-Fin (succ-ℕ k) (zero-Fin k))
is-zero-nat-zero-Fin {zero-ℕ} = refl
is-zero-nat-zero-Fin {succ-ℕ k} = is-zero-nat-zero-Fin {k}

nat-skip-zero-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (skip-zero-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-skip-zero-Fin (succ-ℕ k) (inl x) = nat-skip-zero-Fin k x
nat-skip-zero-Fin (succ-ℕ k) (inr star) = refl

nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x)) ＝ succ-ℕ (nat-Fin k x)
nat-succ-Fin k x = nat-skip-zero-Fin k x

nat-inr-Fin :
  (k : ℕ) (x : Fin k) → nat-Fin (succ-ℕ k) (inr-Fin k x) ＝ succ-ℕ (nat-Fin k x)
nat-inr-Fin (succ-ℕ k) (inl x) = nat-inr-Fin k x
nat-inr-Fin (succ-ℕ k) (inr star) = refl
```

```agda
one-Fin : (k : ℕ) → Fin (succ-ℕ k)
one-Fin k = succ-Fin (succ-ℕ k) (zero-Fin k)

is-one-Fin : (k : ℕ) → Fin k → UU lzero
is-one-Fin (succ-ℕ k) x = x ＝ one-Fin k

is-zero-or-one-Fin-2 :
  (x : Fin 2) → (is-zero-Fin 2 x) + (is-one-Fin 2 x)
is-zero-or-one-Fin-2 (inl (inr star)) = inl refl
is-zero-or-one-Fin-2 (inr star) = inr refl

is-one-nat-one-Fin :
  (k : ℕ) → is-one-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k)))
is-one-nat-one-Fin zero-ℕ = refl
is-one-nat-one-Fin (succ-ℕ k) = is-one-nat-one-Fin k
```

```agda
is-injective-inl-Fin : (k : ℕ) → is-injective (inl-Fin k)
is-injective-inl-Fin k refl = refl
```

### Exercise 7.5 (c)

```agda
neq-zero-skip-zero-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (skip-zero-Fin k x)
neq-zero-skip-zero-Fin {succ-ℕ k} {inl x} p =
  neq-zero-skip-zero-Fin {k = k} {x = x} (is-injective-inl-Fin (succ-ℕ k) p)

neq-zero-succ-Fin :
  {k : ℕ} {x : Fin k} →
  is-nonzero-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl-Fin k x))
neq-zero-succ-Fin {succ-ℕ k} {inl x} p =
  neq-zero-succ-Fin (is-injective-inl-Fin (succ-ℕ k) p)
neq-zero-succ-Fin {succ-ℕ k} {inr star} ()
```

### Exercise 7.5 (d)

```agda
is-injective-skip-zero-Fin : (k : ℕ) → is-injective (skip-zero-Fin k)
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k (is-injective-inl-Fin (succ-ℕ k) p))
is-injective-skip-zero-Fin (succ-ℕ k) {inl x} {inr star} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inl y} ()
is-injective-skip-zero-Fin (succ-ℕ k) {inr star} {inr star} p = refl

is-injective-succ-Fin : (k : ℕ) → is-injective (succ-Fin k)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inl y} p =
  ap inl (is-injective-skip-zero-Fin k {x} {y} p)
is-injective-succ-Fin (succ-ℕ k) {inl x} {inr star} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl x} (ap inl p))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inl y} p =
  ex-falso (neq-zero-succ-Fin {succ-ℕ k} {inl y} (ap inl (inv p)))
is-injective-succ-Fin (succ-ℕ k) {inr star} {inr star} p = refl
```

We define a function `skip-neg-two-Fin` in order to define `pred-Fin`.

```agda
skip-neg-two-Fin :
  (k : ℕ) → Fin k → Fin (succ-ℕ k)
skip-neg-two-Fin (succ-ℕ k) (inl x) = inl (inl x)
skip-neg-two-Fin (succ-ℕ k) (inr x) = neg-one-Fin (succ-ℕ k)
```

We define the predecessor function on `Fin k`.

```agda
pred-Fin : (k : ℕ) → Fin k → Fin k
pred-Fin (succ-ℕ k) (inl x) = skip-neg-two-Fin k (pred-Fin k x)
pred-Fin (succ-ℕ k) (inr x) = neg-two-Fin k
```

We now turn to the exercise.

```agda
pred-zero-Fin :
  (k : ℕ) → is-neg-one-Fin (succ-ℕ k) (pred-Fin (succ-ℕ k) (zero-Fin k))
pred-zero-Fin (zero-ℕ) = refl
pred-zero-Fin (succ-ℕ k) = ap (skip-neg-two-Fin (succ-ℕ k)) (pred-zero-Fin k)

succ-skip-neg-two-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ (succ-ℕ k)) (skip-neg-two-Fin (succ-ℕ k) x) ＝
  inl (succ-Fin (succ-ℕ k) x)
succ-skip-neg-two-Fin zero-ℕ (inr star) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inl x) = refl
succ-skip-neg-two-Fin (succ-ℕ k) (inr star) = refl

is-section-pred-Fin :
  (k : ℕ) (x : Fin k) → succ-Fin k (pred-Fin k x) ＝ x
is-section-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
is-section-pred-Fin (succ-ℕ (succ-ℕ k)) (inl x) =
  ( succ-skip-neg-two-Fin k (pred-Fin (succ-ℕ k) x)) ∙
  ( ap inl (is-section-pred-Fin (succ-ℕ k) x))
is-section-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = refl

is-retraction-pred-Fin :
  (k : ℕ) (x : Fin k) → pred-Fin k (succ-Fin k x) ＝ x
is-retraction-pred-Fin (succ-ℕ zero-ℕ) (inr star) = refl
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inl x)) =
  ap (skip-neg-two-Fin (succ-ℕ k)) (is-retraction-pred-Fin (succ-ℕ k) (inl x))
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inl (inr star)) = refl
is-retraction-pred-Fin (succ-ℕ (succ-ℕ k)) (inr star) = pred-zero-Fin (succ-ℕ k)

is-equiv-succ-Fin : (k : ℕ) → is-equiv (succ-Fin k)
pr1 (pr1 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr1 (is-equiv-succ-Fin k)) = is-section-pred-Fin k
pr1 (pr2 (is-equiv-succ-Fin k)) = pred-Fin k
pr2 (pr2 (is-equiv-succ-Fin k)) = is-retraction-pred-Fin k

equiv-succ-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-succ-Fin k) = succ-Fin k
pr2 (equiv-succ-Fin k) = is-equiv-succ-Fin k

is-equiv-pred-Fin : (k : ℕ) → is-equiv (pred-Fin k)
pr1 (pr1 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr1 (is-equiv-pred-Fin k)) = is-retraction-pred-Fin k
pr1 (pr2 (is-equiv-pred-Fin k)) = succ-Fin k
pr2 (pr2 (is-equiv-pred-Fin k)) = is-section-pred-Fin k

equiv-pred-Fin : (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-pred-Fin k) = pred-Fin k
pr2 (equiv-pred-Fin k) = is-equiv-pred-Fin k
```

```agda
leq-nat-succ-Fin :
  (k : ℕ) (x : Fin k) → leq-ℕ (nat-Fin k (succ-Fin k x)) (succ-ℕ (nat-Fin k x))
leq-nat-succ-Fin (succ-ℕ k) (inl x) =
  leq-eq-ℕ
    ( nat-Fin (succ-ℕ k) (skip-zero-Fin k x))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inl x)))
    ( nat-skip-zero-Fin k x)
leq-nat-succ-Fin (succ-ℕ k) (inr star) =
  concatenate-eq-leq-ℕ
    ( succ-ℕ (nat-Fin (succ-ℕ k) (inr star)))
    ( is-zero-nat-zero-Fin {succ-ℕ k})
    ( leq-zero-ℕ (succ-ℕ (nat-Fin (succ-ℕ k) (inr star))))
```

### `Fin` is injective

```agda
is-equivalence-injective-Fin : is-equivalence-injective Fin
is-equivalence-injective-Fin {zero-ℕ} {zero-ℕ} e =
  refl
is-equivalence-injective-Fin {zero-ℕ} {succ-ℕ l} e =
  ex-falso (map-inv-equiv e (zero-Fin l))
is-equivalence-injective-Fin {succ-ℕ k} {zero-ℕ} e =
  ex-falso (map-equiv e (zero-Fin k))
is-equivalence-injective-Fin {succ-ℕ k} {succ-ℕ l} e =
  ap succ-ℕ (is-equivalence-injective-Fin (equiv-equiv-Maybe e))

abstract
  is-injective-Fin : is-injective Fin
  is-injective-Fin =
    is-injective-is-equivalence-injective is-equivalence-injective-Fin

compute-is-equivalence-injective-Fin-id-equiv :
  {n : ℕ} → is-equivalence-injective-Fin {n} {n} id-equiv ＝ refl
compute-is-equivalence-injective-Fin-id-equiv {zero-ℕ} = refl
compute-is-equivalence-injective-Fin-id-equiv {succ-ℕ n} =
  ap² succ-ℕ
    ( ( ap is-equivalence-injective-Fin compute-equiv-equiv-Maybe-id-equiv) ∙
      ( compute-is-equivalence-injective-Fin-id-equiv {n}))
```

### `Fin` is a preunivalent type family

The proof does not rely on the (pre-)univalence axiom.

```agda
is-section-on-diagonal-is-equivalence-injective-Fin :
  {n : ℕ} →
  equiv-tr Fin (is-equivalence-injective-Fin {n} {n} id-equiv) ＝ id-equiv
is-section-on-diagonal-is-equivalence-injective-Fin =
  ap (equiv-tr Fin) compute-is-equivalence-injective-Fin-id-equiv

is-retraction-is-equivalence-injective-Fin :
  {n m : ℕ} →
  is-retraction (equiv-tr Fin) (is-equivalence-injective-Fin {n} {m})
is-retraction-is-equivalence-injective-Fin refl =
  compute-is-equivalence-injective-Fin-id-equiv

retraction-equiv-tr-Fin : (n m : ℕ) → retraction (equiv-tr Fin {n} {m})
pr1 (retraction-equiv-tr-Fin n m) = is-equivalence-injective-Fin
pr2 (retraction-equiv-tr-Fin n m) = is-retraction-is-equivalence-injective-Fin

is-preunivalent-Fin : is-preunivalent Fin
is-preunivalent-Fin =
  is-preunivalent-retraction-equiv-tr-Set Fin-Set retraction-equiv-tr-Fin
```

## See also

- [The bounded natural numbers](elementary-number-theory.bounded-natural-numbers.md)
- [The strictly bounded natural numbers](elementary-number-theory.strictly-bounded-natural-numbers.md)
- [Modular arithmetic on the standard finite types](elementary-number-theory.modular-arithmetic-standard-finite-types.md)
