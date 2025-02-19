# Unit similarity of integers

```agda
module elementary-number-theory.unit-similarity-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.unit-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Two [integers](elementary-number-theory.integers.md) $a$ and $b$ are said to be
{{#concept "unit similar" Disambiguation="integers" Agda=sim-unit-ℤ}} if

```text
¬ (is-nonzero-ℤ a × is-nonzero-ℤ b) → Σ (u : unit-ℤ) ua=b.
```

The idea is that $a$ and $b$ are unit similar if there exists a
[unit integer](elementary-number-theory.unit-integers.md) $u$ such that $ua=b$.
However, this type is not a proposition if both $a$ and $b$ are $0$. The unit
similarity relation has therefore a slightly more complicated expression.

The unit similarity relation is an
[equivalence relation](foundation.equivalence-relations.md) on the integers.

## Definitions

### The equivalence relation `sim-unit-ℤ`

```agda
presim-unit-ℤ : ℤ → ℤ → UU lzero
presim-unit-ℤ x y = Σ unit-ℤ (λ u → int-unit-ℤ u *ℤ x ＝ y)

sim-unit-ℤ : ℤ → ℤ → UU lzero
sim-unit-ℤ x y = ¬ (is-zero-ℤ x × is-zero-ℤ y) → presim-unit-ℤ x y
```

## Properties

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are logically equivalent

```agda
sim-unit-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → sim-unit-ℤ x y
sim-unit-presim-unit-ℤ {x} {y} H f = H

presim-unit-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → presim-unit-ℤ x y
presim-unit-sim-unit-ℤ {inl x} {inl y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inl x} {inr y} H = H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr x} {inl y} H = H (λ t → Eq-eq-ℤ (pr2 t))
pr1 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = one-unit-ℤ
pr2 (presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inl star)} H) = refl
presim-unit-sim-unit-ℤ {inr (inl star)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr2 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inl star)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))
presim-unit-sim-unit-ℤ {inr (inr x)} {inr (inr y)} H =
  H (λ t → Eq-eq-ℤ (pr1 t))
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` relate `zero-ℤ` only to itself

```agda
is-nonzero-presim-unit-ℤ :
  {x y : ℤ} → presim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-presim-unit-ℤ {x} {y} ((v , (u , (α , α'))) , β) f p =
  Eq-eq-ℤ (ap (_*ℤ u) (inv q) ∙ commutative-mul-ℤ v u ∙ α')
  where
  q : is-zero-ℤ v
  q = is-injective-right-mul-ℤ x f (β ∙ p)

is-nonzero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ x → is-nonzero-ℤ y
is-nonzero-sim-unit-ℤ H f =
  is-nonzero-presim-unit-ℤ (H (f ∘ pr1)) f

is-zero-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ x → is-zero-ℤ y
is-zero-sim-unit-ℤ {x} {y} H p =
  double-negation-elim-is-decidable
    ( has-decidable-equality-ℤ y zero-ℤ)
    ( λ g → g (inv (β g) ∙ (ap ((u g) *ℤ_) p ∙ right-zero-law-mul-ℤ (u g))))
  where
  K : is-nonzero-ℤ y → presim-unit-ℤ x y
  K g = H (λ (u , v) → g v)
  u : is-nonzero-ℤ y → ℤ
  u g = pr1 (pr1 (K g))
  v : is-nonzero-ℤ y → ℤ
  v g = pr1 (pr2 (pr1 (K g)))
  β : (g : is-nonzero-ℤ y) → (u g) *ℤ x ＝ y
  β g = pr2 (K g)
```

### The relations `presim-unit-ℤ` and `sim-unit-ℤ` are equivalence relations

```agda
refl-presim-unit-ℤ : is-reflexive presim-unit-ℤ
pr1 (refl-presim-unit-ℤ x) = one-unit-ℤ
pr2 (refl-presim-unit-ℤ x) = left-unit-law-mul-ℤ x

refl-sim-unit-ℤ : is-reflexive sim-unit-ℤ
refl-sim-unit-ℤ x f = refl-presim-unit-ℤ x

presim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → presim-unit-ℤ x y
presim-unit-eq-ℤ {x} refl = refl-presim-unit-ℤ x

sim-unit-eq-ℤ : {x y : ℤ} → x ＝ y → sim-unit-ℤ x y
sim-unit-eq-ℤ {x} refl = refl-sim-unit-ℤ x

symmetric-presim-unit-ℤ : is-symmetric presim-unit-ℤ
symmetric-presim-unit-ℤ x y (pair (pair u H) p) =
  f (is-one-or-neg-one-is-unit-ℤ u H)
  where
  f : is-one-or-neg-one-ℤ u → presim-unit-ℤ y x
  pr1 (f (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl)) = inv p
  pr1 (f (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl)) = inv (inv (neg-neg-ℤ x) ∙ ap (neg-one-ℤ *ℤ_) p)

symmetric-sim-unit-ℤ : is-symmetric sim-unit-ℤ
symmetric-sim-unit-ℤ x y H f =
  symmetric-presim-unit-ℤ x y (H (λ p → f (pair (pr2 p) (pr1 p))))

is-nonzero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-nonzero-ℤ y → is-nonzero-ℤ x
is-nonzero-sim-unit-ℤ' {x} {y} H =
  is-nonzero-sim-unit-ℤ (symmetric-sim-unit-ℤ x y H)

is-zero-sim-unit-ℤ' :
  {x y : ℤ} → sim-unit-ℤ x y → is-zero-ℤ y → is-zero-ℤ x
is-zero-sim-unit-ℤ' {x} {y} H = is-zero-sim-unit-ℤ (symmetric-sim-unit-ℤ x y H)

transitive-presim-unit-ℤ : is-transitive presim-unit-ℤ
transitive-presim-unit-ℤ x y z (pair (pair v K) q) (pair (pair u H) p) =
  f (is-one-or-neg-one-is-unit-ℤ u H) (is-one-or-neg-one-is-unit-ℤ v K)
  where
  f : is-one-or-neg-one-ℤ u → is-one-or-neg-one-ℤ v → presim-unit-ℤ x z
  pr1 (f (inl refl) (inl refl)) = one-unit-ℤ
  pr2 (f (inl refl) (inl refl)) = p ∙ q
  pr1 (f (inl refl) (inr refl)) = neg-one-unit-ℤ
  pr2 (f (inl refl) (inr refl)) = ap neg-ℤ p ∙ q
  pr1 (f (inr refl) (inl refl)) = neg-one-unit-ℤ
  pr2 (f (inr refl) (inl refl)) = p ∙ q
  pr1 (f (inr refl) (inr refl)) = one-unit-ℤ
  pr2 (f (inr refl) (inr refl)) = inv (neg-neg-ℤ x) ∙ (ap neg-ℤ p ∙ q)

transitive-sim-unit-ℤ : is-transitive sim-unit-ℤ
transitive-sim-unit-ℤ x y z K H f =
  transitive-presim-unit-ℤ x y z
    ( K (λ (p , q) → f (is-zero-sim-unit-ℤ' H p , q)))
    ( H (λ (p , q) → f (p , is-zero-sim-unit-ℤ K q)))
```

### `sim-unit-ℤ |x| x` holds

```agda
sim-unit-abs-ℤ : (x : ℤ) → sim-unit-ℤ (int-abs-ℤ x) x
pr1 (sim-unit-abs-ℤ (inl x) f) = neg-one-unit-ℤ
pr2 (sim-unit-abs-ℤ (inl x) f) = refl
sim-unit-abs-ℤ (inr (inl star)) = refl-sim-unit-ℤ zero-ℤ
sim-unit-abs-ℤ (inr (inr x)) = refl-sim-unit-ℤ (inr (inr x))
```

### If we have that `sim-unit-ℤ x y`, then they must differ only by sign

```agda
is-plus-or-minus-sim-unit-ℤ :
  {x y : ℤ} → sim-unit-ℤ x y → is-plus-or-minus-ℤ x y
is-plus-or-minus-sim-unit-ℤ {x} {y} H with ( is-decidable-is-zero-ℤ x)
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inl z =
  inl (z ∙ inv (is-zero-sim-unit-ℤ H z))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz
  with
  ( is-one-or-neg-one-is-unit-ℤ
    ( int-unit-ℤ (pr1 (H (λ u → nz (pr1 u)))))
    ( is-unit-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inl pos =
  inl
    ( equational-reasoning
      x
      ＝ one-ℤ *ℤ x
        by (inv (left-unit-law-mul-ℤ x))
      ＝ (int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))) *ℤ x
        by inv (ap (_*ℤ x) pos)
      ＝ y
        by pr2 (H (λ u → nz (pr1 u))))
is-plus-or-minus-sim-unit-ℤ {x} {y} H | inr nz | inr p =
  inr
    ( equational-reasoning
      neg-ℤ x
      ＝ (int-unit-ℤ (pr1 (H (λ u → nz (pr1 u))))) *ℤ x
        by ap (_*ℤ x) (inv p)
      ＝ y
        by pr2 (H (λ u → nz (pr1 u))))
```

### If `sim-unit-ℤ x y` holds and both `x` and `y` have the same sign, then `x ＝ y`

```agda
eq-sim-unit-is-nonnegative-ℤ :
  {a b : ℤ} → is-nonnegative-ℤ a → is-nonnegative-ℤ b → sim-unit-ℤ a b → a ＝ b
eq-sim-unit-is-nonnegative-ℤ {a} {b} H H' K =
  rec-coproduct
    ( id)
    ( λ K' →
      eq-is-zero-ℤ
        ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ H
          ( is-nonnegative-eq-ℤ (inv K') H'))
        ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ H'
          ( is-nonnegative-eq-ℤ (inv (neg-neg-ℤ a) ∙ ap neg-ℤ K') H)))
    ( is-plus-or-minus-sim-unit-ℤ K)
```
