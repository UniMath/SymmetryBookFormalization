# Products of natural numbers

```agda
module elementary-number-theory.products-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type

open import lists.lists

open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product" Disambiguation="standard finite family of natural numbers"}}
of a [standard finite](univalent-combinatorics.standard-finite-types.md) family
of [natural numbers](elementary-number-theory.natural-numbers.md) is defined by
iterated
[multiplication](elementary-number-theory.multiplication-natural-numbers.md).

## Definitions

### Products of families of natural numbers indexed by standard finite types

```agda
Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = 1
Π-ℕ (succ-ℕ k) x = (Π-ℕ k (λ i → x (inl i))) *ℕ (x (inr star))
```

## Properties

### The product of one natural number is that natural number itself

```agda
unit-law-Π-ℕ : (f : Fin 1 → ℕ) (x : Fin 1) → Π-ℕ 1 f ＝ f x
unit-law-Π-ℕ f (inr star) = left-unit-law-mul-ℕ _
```

### Any nonempty product of natural numbers greater than 1 is greater than 1

```agda
le-one-Π-ℕ :
  (k : ℕ) (f : Fin k → ℕ) →
  0 <-ℕ k → ((i : Fin k) → 1 <-ℕ f i) → 1 <-ℕ Π-ℕ k f
le-one-Π-ℕ (succ-ℕ zero-ℕ) f H K =
  concatenate-le-eq-ℕ 1
    ( f (inr star))
    ( Π-ℕ 1 f)
    ( K (inr star))
    ( inv (unit-law-Π-ℕ f (inr star)))
le-one-Π-ℕ (succ-ℕ (succ-ℕ k)) f H K =
  le-one-mul-ℕ
    ( Π-ℕ (succ-ℕ k) (f ∘ inl))
    ( f (inr star))
    ( le-one-Π-ℕ (succ-ℕ k) (f ∘ inl) star (K ∘ inl))
    ( K (inr star))
```

### Products preserve pointwise identifications

```agda
preserves-htpy-Π-ℕ :
  (k : ℕ) {f g : Fin k → ℕ} (H : f ~ g) → Π-ℕ k f ＝ Π-ℕ k g
preserves-htpy-Π-ℕ k H =
  ap (Π-ℕ k) (eq-htpy H)
```

### Any factor of a product of natural numbers divides the product

```agda
quotient-div-factor-Π-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) → ℕ
quotient-div-factor-Π-ℕ (succ-ℕ k) f i =
  Π-ℕ k (f ∘ skip-Fin k i)

eq-quotient-div-factor-Π-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) →
  quotient-div-factor-Π-ℕ k f i *ℕ f i ＝ Π-ℕ k f
eq-quotient-div-factor-Π-ℕ (succ-ℕ zero-ℕ) f (inr star) =
  refl
eq-quotient-div-factor-Π-ℕ (succ-ℕ (succ-ℕ k)) f (inl i) =
  ( right-swap-mul-ℕ
    ( Π-ℕ k (f ∘ inl ∘ skip-Fin k i))
    ( f (inr star))
    ( f (inl i))) ∙
  ( ap (_*ℕ f (inr star)) (eq-quotient-div-factor-Π-ℕ (succ-ℕ k) (f ∘ inl) i))
eq-quotient-div-factor-Π-ℕ (succ-ℕ (succ-ℕ k)) f (inr star) =
  refl

div-factor-Π-ℕ :
  (k : ℕ) (f : Fin k → ℕ) (i : Fin k) → div-ℕ (f i) (Π-ℕ k f)
pr1 (div-factor-Π-ℕ k f i) =
  quotient-div-factor-Π-ℕ k f i
pr2 (div-factor-Π-ℕ k f i) =
  eq-quotient-div-factor-Π-ℕ k f i
```

## See also

- [Products of lists of natural numbers](elementary-number-theory.products-lists-of-natural-numbers.md)
