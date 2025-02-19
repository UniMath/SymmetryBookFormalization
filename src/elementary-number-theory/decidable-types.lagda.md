# Decidable types in elementary number theory

```agda
module elementary-number-theory.decidable-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We describe conditions under which dependent sums and dependent products are
decidable.

## Properties

### Given a family of decidable types and a number `m` such that `Σ (m ≤ x), P x` is decidable, then `Σ ℕ P` is decidable

```agda
is-decidable-Σ-ℕ :
  {l : Level} (m : ℕ) (P : ℕ → UU l) → is-decidable-fam P →
  is-decidable (Σ ℕ (λ x → m ≤-ℕ x × P x)) → is-decidable (Σ ℕ P)
is-decidable-Σ-ℕ m P d (inl (x , l , p)) =
  inl (x , p)
is-decidable-Σ-ℕ zero-ℕ P d (inr f) =
  inr (λ p → f (pr1 p , star , pr2 p))
is-decidable-Σ-ℕ (succ-ℕ m) P d (inr f)
  with
  d 0
... | inl p = inl (0 , p)
... | inr g with
  is-decidable-Σ-ℕ m
    ( P ∘ succ-ℕ)
    ( λ x → d (succ-ℕ x))
    ( inr (λ p → f (succ-ℕ (pr1 p) , pr2 p)))
... | inl p = inl (succ-ℕ (pr1 p) , pr2 p)
... | inr h = inr α
  where
  α : Σ ℕ P → empty
  α (zero-ℕ , p) = g p
  α (succ-ℕ x , p) = h (x , p)
```

### Bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2) →
  is-decidable-fam P → is-decidable-fam Q →
  is-upper-bound-ℕ P m → is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-Σ-ℕ
    ( succ-ℕ m)
    ( λ x → (P x) × (Q x))
    ( λ x → is-decidable-product (dP x) (dQ x))
    ( inr
      ( λ p →
        contradiction-leq-ℕ
          ( pr1 p)
          ( m)
          ( H (pr1 p) (pr1 (pr2 (pr2 p))))
          ( pr1 (pr2 p))))

is-decidable-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) →
  is-decidable-fam P → is-decidable (Σ ℕ (λ x → x ≤-ℕ m × P x))
is-decidable-bounded-Σ-ℕ' m P d =
  is-decidable-bounded-Σ-ℕ m
    ( λ x → x ≤-ℕ m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( λ x → id)
```

### Strictly bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-strictly-bounded-Σ-ℕ :
  {l1 l2 : Level} (m : ℕ) (P : ℕ → UU l1) (Q : ℕ → UU l2) →
  is-decidable-fam P → is-decidable-fam Q → is-strict-upper-bound-ℕ P m →
  is-decidable (Σ ℕ (λ x → (P x) × (Q x)))
is-decidable-strictly-bounded-Σ-ℕ m P Q dP dQ H =
  is-decidable-bounded-Σ-ℕ m P Q dP dQ
    ( is-upper-bound-is-strict-upper-bound-ℕ P m H)

is-decidable-strictly-bounded-Σ-ℕ' :
  {l : Level} (m : ℕ) (P : ℕ → UU l) →
  is-decidable-fam P → is-decidable (Σ ℕ (λ x → x <-ℕ m × P x))
is-decidable-strictly-bounded-Σ-ℕ' m P d =
  is-decidable-strictly-bounded-Σ-ℕ m
    ( λ x → x <-ℕ m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( λ x → id)
```

### Given a family `P `of decidable types over ℕ and a number `m` such that `Π (m ≤ x), P x`, the type `Π ℕ P` is decidable

```agda
is-decidable-Π-ℕ :
  {l : Level} (P : ℕ → UU l) →
  is-decidable-fam P → (m : ℕ) → is-decidable ((x : ℕ) → m ≤-ℕ x → P x) →
  is-decidable ((x : ℕ) → P x)
is-decidable-Π-ℕ P d zero-ℕ (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d zero-ℕ (inl H) = inl (λ x → H x (leq-zero-ℕ x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inr nH) = inr (λ f → nH (λ x y → f x))
is-decidable-Π-ℕ P d (succ-ℕ m) (inl H) with d zero-ℕ
... | inr np = inr (λ f → np (f zero-ℕ))
... | inl p with
  is-decidable-Π-ℕ
    ( λ x → P (succ-ℕ x))
    ( λ x → d (succ-ℕ x))
    ( m)
    ( inl (λ x → H (succ-ℕ x)))
... | inl g = inl (ind-ℕ p (λ x y → g x))
... | inr ng = inr (λ f → ng (λ x → f (succ-ℕ x)))
```

### Bounded dependent products of decidable types are decidable

```agda
is-decidable-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) →
  is-decidable-fam P → is-decidable-fam Q →
  (m : ℕ) → is-upper-bound-ℕ P m →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-Π-ℕ
    ( λ x → P x → Q x)
    ( λ x → is-decidable-function-type (dP x) (dQ x))
    ( succ-ℕ m)
    ( inl (λ x l p → ex-falso (contradiction-leq-ℕ x m (H x p) l)))

is-decidable-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) →
  is-decidable-fam P → (m : ℕ) → is-decidable ((x : ℕ) → x ≤-ℕ m → P x)
is-decidable-bounded-Π-ℕ' P d m =
  is-decidable-bounded-Π-ℕ
    ( λ x → x ≤-ℕ m)
    ( P)
    ( λ x → is-decidable-leq-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)
```

### Strictly bounded dependent products of decidable types are decidable

```agda
is-decidable-strictly-bounded-Π-ℕ :
  {l1 l2 : Level} (P : ℕ → UU l1) (Q : ℕ → UU l2) →
  is-decidable-fam P → is-decidable-fam Q →
  (m : ℕ) → is-strict-upper-bound-ℕ P m →
  is-decidable ((x : ℕ) → P x → Q x)
is-decidable-strictly-bounded-Π-ℕ P Q dP dQ m H =
  is-decidable-bounded-Π-ℕ P Q dP dQ m (λ x p → leq-le-ℕ x m (H x p))

is-decidable-strictly-bounded-Π-ℕ' :
  {l : Level} (P : ℕ → UU l) → is-decidable-fam P →
  (m : ℕ) → is-decidable ((x : ℕ) → x <-ℕ m → P x)
is-decidable-strictly-bounded-Π-ℕ' P d m =
  is-decidable-strictly-bounded-Π-ℕ
    ( λ x → x <-ℕ m)
    ( P)
    ( λ x → is-decidable-le-ℕ x m)
    ( d)
    ( m)
    ( λ x → id)
```
