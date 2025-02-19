# Multiplication of integers

```agda
module elementary-number-theory.multiplication-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We introduce the
{{#concept "multiplication" Disambiguation="integers" Agda=mul-ℤ}} of integers
and derive its basic properties with respect to `succ-ℤ`, `pred-ℤ`, `neg-ℤ` and
`add-ℤ`.

## Definitions

### The standard definition of multiplication on ℤ

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = (neg-ℤ l) +ℤ (mul-ℤ (inl x) l)
mul-ℤ (inr (inl star)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = l +ℤ (mul-ℤ (inr (inr x)) l)

infixl 40 _*ℤ_
_*ℤ_ = mul-ℤ

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = mul-ℤ y x

ap-mul-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x *ℤ y ＝ x' *ℤ y'
ap-mul-ℤ p q = ap-binary mul-ℤ p q
```

### A definition of multiplication that connects with multiplication on ℕ

```agda
explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))
explicit-mul-ℤ (inl x) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inl x) (inr (inr y)) = neg-ℤ (int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inl y) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inl y) = neg-ℤ (int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inl star)) (inr (inr y)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = explicit-mul-ℤ y x
```

### A definition of being equal up to sign

```agda
is-plus-or-minus-ℤ : ℤ → ℤ → UU lzero
is-plus-or-minus-ℤ x y = (x ＝ y) + (neg-one-ℤ *ℤ x ＝ y)
```

## Properties

### Multiplication by zero is zero

```agda
left-zero-law-mul-ℤ : (k : ℤ) → zero-ℤ *ℤ k ＝ zero-ℤ
left-zero-law-mul-ℤ k = refl

right-zero-law-mul-ℤ : (k : ℤ) → k *ℤ zero-ℤ ＝ zero-ℤ
right-zero-law-mul-ℤ (inl zero-ℕ) = refl
right-zero-law-mul-ℤ (inl (succ-ℕ n)) =
  right-zero-law-mul-ℤ (inl n)
right-zero-law-mul-ℤ (inr (inl star)) = refl
right-zero-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-zero-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  right-zero-law-mul-ℤ (inr (inr n))
```

### Unit laws

```agda
left-unit-law-mul-ℤ : (k : ℤ) → one-ℤ *ℤ k ＝ k
left-unit-law-mul-ℤ k = refl

right-unit-law-mul-ℤ : (k : ℤ) → k *ℤ one-ℤ ＝ k
right-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap ((neg-one-ℤ) +ℤ_) (right-unit-law-mul-ℤ (inl n))
right-unit-law-mul-ℤ (inr (inl star)) = refl
right-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (one-ℤ +ℤ_) (right-unit-law-mul-ℤ (inr (inr n)))
```

### Multiplication of an integer by `-1` is equal to the negative

```agda
left-neg-unit-law-mul-ℤ : (k : ℤ) → neg-one-ℤ *ℤ k ＝ neg-ℤ k
left-neg-unit-law-mul-ℤ k = refl

right-neg-unit-law-mul-ℤ : (k : ℤ) → k *ℤ neg-one-ℤ ＝ neg-ℤ k
right-neg-unit-law-mul-ℤ (inl zero-ℕ) = refl
right-neg-unit-law-mul-ℤ (inl (succ-ℕ n)) =
  ap (one-ℤ +ℤ_) (right-neg-unit-law-mul-ℤ (inl n))
right-neg-unit-law-mul-ℤ (inr (inl star)) = refl
right-neg-unit-law-mul-ℤ (inr (inr zero-ℕ)) = refl
right-neg-unit-law-mul-ℤ (inr (inr (succ-ℕ n))) =
  ap (neg-one-ℤ +ℤ_) (right-neg-unit-law-mul-ℤ (inr (inr n)))
```

### Multiplication by the successor or the predecessor of an integer

```agda
left-successor-law-mul-ℤ :
  (k l : ℤ) → (succ-ℤ k) *ℤ l ＝ l +ℤ (k *ℤ l)
left-successor-law-mul-ℤ (inl zero-ℕ) l =
  inv (right-inverse-law-add-ℤ l)
left-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ( inv (left-unit-law-add-ℤ ((inl n) *ℤ l))) ∙
    ( ap
      ( _+ℤ ((inl n) *ℤ l))
      ( inv (right-inverse-law-add-ℤ l)))) ∙
  ( associative-add-ℤ l (neg-ℤ l) ((inl n) *ℤ l))
left-successor-law-mul-ℤ (inr (inl star)) l =
  inv (right-unit-law-add-ℤ l)
left-successor-law-mul-ℤ (inr (inr n)) l = refl

left-successor-law-mul-ℤ' :
  (k l : ℤ) → succ-ℤ k *ℤ l ＝ k *ℤ l +ℤ l
left-successor-law-mul-ℤ' k l =
  left-successor-law-mul-ℤ k l ∙ commutative-add-ℤ l (k *ℤ l)

left-predecessor-law-mul-ℤ :
  (k l : ℤ) → (pred-ℤ k) *ℤ l ＝ (neg-ℤ l) +ℤ (k *ℤ l)
left-predecessor-law-mul-ℤ (inl n) l = refl
left-predecessor-law-mul-ℤ (inr (inl star)) l =
  ( left-neg-unit-law-mul-ℤ l) ∙
  ( inv (right-unit-law-add-ℤ (neg-ℤ l)))
left-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l =
  inv (left-inverse-law-add-ℤ l)
left-predecessor-law-mul-ℤ (inr (inr (succ-ℕ x))) l =
  ( ap
    ( _+ℤ ((in-pos-ℤ x) *ℤ l))
    ( inv (left-inverse-law-add-ℤ l))) ∙
  ( associative-add-ℤ (neg-ℤ l) l ((in-pos-ℤ x) *ℤ l))

left-predecessor-law-mul-ℤ' :
  (k l : ℤ) → pred-ℤ k *ℤ l ＝ k *ℤ l -ℤ l
left-predecessor-law-mul-ℤ' k l =
  left-predecessor-law-mul-ℤ k l ∙ commutative-add-ℤ (neg-ℤ l) (k *ℤ l)

right-successor-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (succ-ℤ l) ＝ k +ℤ (k *ℤ l)
right-successor-law-mul-ℤ (inl zero-ℕ) l = inv (pred-neg-ℤ l)
right-successor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (succ-ℤ l)) ∙
  ( ( ap ((neg-ℤ (succ-ℤ l)) +ℤ_) (right-successor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv (associative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl n) ((inl n) *ℤ l))) ∙
      ( ( ap
          ( _+ℤ ((inl n) *ℤ l))
          { x = (neg-ℤ (succ-ℤ l)) +ℤ (inl n)}
          { y = (inl (succ-ℕ n)) +ℤ (neg-ℤ l)}
          ( ( right-successor-law-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n))) ∙
            ( ( ap succ-ℤ
                ( commutative-add-ℤ (neg-ℤ (succ-ℤ l)) (inl (succ-ℕ n)))) ∙
              ( ( inv
                  ( right-successor-law-add-ℤ
                    ( inl (succ-ℕ n))
                    ( neg-ℤ (succ-ℤ l)))) ∙
                ( ap
                  ( (inl (succ-ℕ n)) +ℤ_)
                  ( ( ap succ-ℤ (inv (pred-neg-ℤ l))) ∙
                    ( is-section-pred-ℤ (neg-ℤ l)))))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) (neg-ℤ l) ((inl n) *ℤ l)))))
right-successor-law-mul-ℤ (inr (inl star)) l = refl
right-successor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-successor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos-ℤ n) (succ-ℤ l)) ∙
  ( ( ap ((succ-ℤ l) +ℤ_) (right-successor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (succ-ℤ l) (in-pos-ℤ n) ((in-pos-ℤ n) *ℤ l))) ∙
      ( ( ap
          ( _+ℤ ((in-pos-ℤ n) *ℤ l))
          { x = (succ-ℤ l) +ℤ (in-pos-ℤ n)}
          { y = (in-pos-ℤ (succ-ℕ n)) +ℤ l}
          ( ( left-successor-law-add-ℤ l (in-pos-ℤ n)) ∙
            ( ( ap succ-ℤ (commutative-add-ℤ l (in-pos-ℤ n))) ∙
              ( inv (left-successor-law-add-ℤ (in-pos-ℤ n) l))))) ∙
        ( associative-add-ℤ (inr (inr (succ-ℕ n))) l ((inr (inr n)) *ℤ l)))))

right-successor-law-mul-ℤ' :
  (k l : ℤ) → k *ℤ succ-ℤ l ＝ k *ℤ l +ℤ k
right-successor-law-mul-ℤ' k l =
  right-successor-law-mul-ℤ k l ∙ commutative-add-ℤ k (k *ℤ l)

right-predecessor-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (pred-ℤ l) ＝ (neg-ℤ k) +ℤ (k *ℤ l)
right-predecessor-law-mul-ℤ (inl zero-ℕ) l =
  ( left-neg-unit-law-mul-ℤ (pred-ℤ l)) ∙
  ( neg-pred-ℤ l)
right-predecessor-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( left-predecessor-law-mul-ℤ (inl n) (pred-ℤ l)) ∙
  ( ( ap ((neg-ℤ (pred-ℤ l)) +ℤ_) (right-predecessor-law-mul-ℤ (inl n) l)) ∙
    ( ( inv
        ( associative-add-ℤ (neg-ℤ (pred-ℤ l)) (in-pos-ℤ n) ((inl n) *ℤ l))) ∙
      ( ( ap
          ( _+ℤ ((inl n) *ℤ l))
          { x = (neg-ℤ (pred-ℤ l)) +ℤ (inr (inr n))}
          { y = (neg-ℤ (inl (succ-ℕ n))) +ℤ (neg-ℤ l)}
          ( ( ap (_+ℤ (in-pos-ℤ n)) (neg-pred-ℤ l)) ∙
            ( ( left-successor-law-add-ℤ (neg-ℤ l) (in-pos-ℤ n)) ∙
              ( ( ap succ-ℤ (commutative-add-ℤ (neg-ℤ l) (in-pos-ℤ n))) ∙
                ( inv (left-successor-law-add-ℤ (in-pos-ℤ n) (neg-ℤ l))))))) ∙
        ( associative-add-ℤ (in-pos-ℤ (succ-ℕ n)) (neg-ℤ l) ((inl n) *ℤ l)))))
right-predecessor-law-mul-ℤ (inr (inl star)) l = refl
right-predecessor-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
right-predecessor-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-successor-law-mul-ℤ (in-pos-ℤ n) (pred-ℤ l)) ∙
  ( ( ap ((pred-ℤ l) +ℤ_) (right-predecessor-law-mul-ℤ (inr (inr n)) l)) ∙
    ( ( inv (associative-add-ℤ (pred-ℤ l) (inl n) ((inr (inr n)) *ℤ l))) ∙
      ( ( ap
          ( _+ℤ ((in-pos-ℤ n) *ℤ l))
          { x = (pred-ℤ l) +ℤ (inl n)}
          { y = (neg-ℤ (in-pos-ℤ (succ-ℕ n))) +ℤ l}
          ( ( left-predecessor-law-add-ℤ l (inl n)) ∙
            ( ( ap pred-ℤ (commutative-add-ℤ l (inl n))) ∙
              ( inv (left-predecessor-law-add-ℤ (inl n) l))))) ∙
        ( associative-add-ℤ (inl (succ-ℕ n)) l ((inr (inr n)) *ℤ l)))))

right-predecessor-law-mul-ℤ' :
  (k l : ℤ) → k *ℤ pred-ℤ l ＝ k *ℤ l -ℤ k
right-predecessor-law-mul-ℤ' k l =
  right-predecessor-law-mul-ℤ k l ∙ commutative-add-ℤ (neg-ℤ k) (k *ℤ l)

double-successor-law-mul-ℤ :
  (k l : ℤ) → succ-ℤ k *ℤ succ-ℤ l ＝ k *ℤ l +ℤ k +ℤ l +ℤ int-ℕ 1
double-successor-law-mul-ℤ k l =
  left-successor-law-mul-ℤ' k (succ-ℤ l) ∙
  ap-add-ℤ
    ( right-successor-law-mul-ℤ' k l)
    ( inv (right-add-one-ℤ l)) ∙
  inv (associative-add-ℤ (k *ℤ l +ℤ k) l (int-ℕ 1))

double-predecessor-law-mul-ℤ :
  (k l : ℤ) → pred-ℤ k *ℤ pred-ℤ l ＝ ((k *ℤ l -ℤ k) -ℤ l) +ℤ int-ℕ 1
double-predecessor-law-mul-ℤ k l =
  left-predecessor-law-mul-ℤ' k (pred-ℤ l) ∙
  ap-add-ℤ
    ( right-predecessor-law-mul-ℤ' k l)
    ( ap neg-ℤ (inv (right-add-neg-one-ℤ l)) ∙
      distributive-neg-add-ℤ l neg-one-ℤ) ∙
  inv (associative-add-ℤ (k *ℤ l -ℤ k) (neg-ℤ l) (int-ℕ 1))
```

### Multiplication on the integers distributes on the right over addition

```agda
right-distributive-mul-add-ℤ :
  (k l m : ℤ) → (k +ℤ l) *ℤ m ＝ (k *ℤ m) +ℤ (l *ℤ m)
right-distributive-mul-add-ℤ (inl zero-ℕ) l m =
  ( left-predecessor-law-mul-ℤ l m) ∙
  ( ap
    ( _+ℤ (l *ℤ m))
    ( inv
      ( ( left-predecessor-law-mul-ℤ zero-ℤ m) ∙
        ( right-unit-law-add-ℤ (neg-ℤ m)))))
right-distributive-mul-add-ℤ (inl (succ-ℕ x)) l m =
  ( left-predecessor-law-mul-ℤ ((inl x) +ℤ l) m) ∙
  ( ( ap ((neg-ℤ m) +ℤ_) (right-distributive-mul-add-ℤ (inl x) l m)) ∙
    ( inv (associative-add-ℤ (neg-ℤ m) ((inl x) *ℤ m) (l *ℤ m))))
right-distributive-mul-add-ℤ (inr (inl star)) l m = refl
right-distributive-mul-add-ℤ (inr (inr zero-ℕ)) l m =
  left-successor-law-mul-ℤ l m
right-distributive-mul-add-ℤ (inr (inr (succ-ℕ n))) l m =
  ( left-successor-law-mul-ℤ ((in-pos-ℤ n) +ℤ l) m) ∙
  ( ( ap (m +ℤ_) (right-distributive-mul-add-ℤ (inr (inr n)) l m)) ∙
    ( inv (associative-add-ℤ m ((in-pos-ℤ n) *ℤ m) (l *ℤ m))))
```

### Left multiplication by the negative of an integer is the negative of the multiplication

```agda
left-negative-law-mul-ℤ :
  (k l : ℤ) → (neg-ℤ k) *ℤ l ＝ neg-ℤ (k *ℤ l)
left-negative-law-mul-ℤ (inl zero-ℕ) l =
  ( left-unit-law-mul-ℤ l) ∙
  ( inv (neg-neg-ℤ l))
left-negative-law-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap (_*ℤ l) (neg-pred-ℤ (inl n))) ∙
  ( ( left-successor-law-mul-ℤ (neg-ℤ (inl n)) l) ∙
    ( ( ap (l +ℤ_) (left-negative-law-mul-ℤ (inl n) l)) ∙
      ( right-negative-law-add-ℤ l ((inl n) *ℤ l))))
left-negative-law-mul-ℤ (inr (inl star)) l = refl
left-negative-law-mul-ℤ (inr (inr zero-ℕ)) l = refl
left-negative-law-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( left-predecessor-law-mul-ℤ (inl n) l) ∙
  ( ( ap ((neg-ℤ l) +ℤ_) (left-negative-law-mul-ℤ (inr (inr n)) l)) ∙
    ( inv (distributive-neg-add-ℤ l ((in-pos-ℤ n) *ℤ l))))
```

### Multiplication on the integers is associative

```agda
associative-mul-ℤ :
  (k l m : ℤ) → (k *ℤ l) *ℤ m ＝ k *ℤ (l *ℤ m)
associative-mul-ℤ (inl zero-ℕ) l m =
  left-negative-law-mul-ℤ l m
associative-mul-ℤ (inl (succ-ℕ n)) l m =
  ( right-distributive-mul-add-ℤ (neg-ℤ l) ((inl n) *ℤ l) m) ∙
  ( ( ap (((neg-ℤ l) *ℤ m) +ℤ_) (associative-mul-ℤ (inl n) l m)) ∙
    ( ap
      ( _+ℤ ((inl n) *ℤ (l *ℤ m)))
      ( left-negative-law-mul-ℤ l m)))
associative-mul-ℤ (inr (inl star)) l m = refl
associative-mul-ℤ (inr (inr zero-ℕ)) l m = refl
associative-mul-ℤ (inr (inr (succ-ℕ n))) l m =
  ( right-distributive-mul-add-ℤ l ((in-pos-ℤ n) *ℤ l) m) ∙
  ( ap ((l *ℤ m) +ℤ_) (associative-mul-ℤ (inr (inr n)) l m))
```

### Multiplication on the integers is commutative

```agda
commutative-mul-ℤ :
  (k l : ℤ) → k *ℤ l ＝ l *ℤ k
commutative-mul-ℤ (inl zero-ℕ) l = inv (right-neg-unit-law-mul-ℤ l)
commutative-mul-ℤ (inl (succ-ℕ n)) l =
  ( ap ((neg-ℤ l) +ℤ_) (commutative-mul-ℤ (inl n) l)) ∙
  ( inv (right-predecessor-law-mul-ℤ l (inl n)))
commutative-mul-ℤ (inr (inl star)) l = inv (right-zero-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr zero-ℕ)) l = inv (right-unit-law-mul-ℤ l)
commutative-mul-ℤ (inr (inr (succ-ℕ n))) l =
  ( ap (l +ℤ_) (commutative-mul-ℤ (inr (inr n)) l)) ∙
  ( inv (right-successor-law-mul-ℤ l (in-pos-ℤ n)))
```

### Multiplication on the integers distributes on the left over addition

```agda
left-distributive-mul-add-ℤ :
  (m k l : ℤ) → m *ℤ (k +ℤ l) ＝ (m *ℤ k) +ℤ (m *ℤ l)
left-distributive-mul-add-ℤ m k l =
  commutative-mul-ℤ m (k +ℤ l) ∙
    ( ( right-distributive-mul-add-ℤ k l m) ∙
      ( ap-add-ℤ (commutative-mul-ℤ k m) (commutative-mul-ℤ l m)))
```

### Distributivity of multiplication over addition on both sides

For any four integers `a`, `b`, `c`, and `d` we have

```text
  (a + b)(c + d) ＝ (ac + ad) + (bc + bd).
```

```agda
double-distributive-mul-add-ℤ :
  (a b c d : ℤ) →
  (a +ℤ b) *ℤ (c +ℤ d) ＝ (a *ℤ c +ℤ a *ℤ d) +ℤ (b *ℤ c +ℤ b *ℤ d)
double-distributive-mul-add-ℤ a b c d =
  right-distributive-mul-add-ℤ a b (c +ℤ d) ∙
  ap-add-ℤ
    ( left-distributive-mul-add-ℤ a c d)
    ( left-distributive-mul-add-ℤ b c d)
```

### Right multiplication by the negative of an integer is the negative of the multiplication

```agda
right-negative-law-mul-ℤ :
  (k l : ℤ) → k *ℤ (neg-ℤ l) ＝ neg-ℤ (k *ℤ l)
right-negative-law-mul-ℤ k l =
  ( ( commutative-mul-ℤ k (neg-ℤ l)) ∙
    ( left-negative-law-mul-ℤ l k)) ∙
  ( ap neg-ℤ (commutative-mul-ℤ l k))
```

### The multiplication of the negatives of two integers is equal to their multiplication

```agda
double-negative-law-mul-ℤ : (k l : ℤ) → (neg-ℤ k) *ℤ (neg-ℤ l) ＝ k *ℤ l
double-negative-law-mul-ℤ k l =
  equational-reasoning
    (neg-ℤ k) *ℤ (neg-ℤ l)
    ＝ neg-ℤ (k *ℤ (neg-ℤ l))
      by left-negative-law-mul-ℤ k (neg-ℤ l)
    ＝ neg-ℤ (neg-ℤ (k *ℤ l))
      by ap neg-ℤ (right-negative-law-mul-ℤ k l)
    ＝ k *ℤ l
      by neg-neg-ℤ (k *ℤ l)
```

### Interchange law

```agda
interchange-law-mul-mul-ℤ :
  (x y u v : ℤ) → (x *ℤ y) *ℤ (u *ℤ v) ＝ (x *ℤ u) *ℤ (y *ℤ v)
interchange-law-mul-mul-ℤ =
  interchange-law-commutative-and-associative
    mul-ℤ
    commutative-mul-ℤ
    associative-mul-ℤ
```

### Swapping the order of multiplication from one side

```agda
right-swap-mul-ℤ :
  (x y z : ℤ) → (x *ℤ y) *ℤ z ＝ (x *ℤ z) *ℤ y
right-swap-mul-ℤ x y z =
  associative-mul-ℤ x y z ∙
  ap (x *ℤ_) (commutative-mul-ℤ y z) ∙
  inv (associative-mul-ℤ x z y)

left-swap-mul-ℤ :
  (x y z : ℤ) → x *ℤ (y *ℤ z) ＝ y *ℤ (x *ℤ z)
left-swap-mul-ℤ x y z =
  inv (associative-mul-ℤ x y z) ∙
  ap (_*ℤ z) (commutative-mul-ℤ x y) ∙
  associative-mul-ℤ y x z
```

### Computing multiplication of integers that come from natural numbers

```agda
mul-int-ℕ : (x y : ℕ) → (int-ℕ x) *ℤ (int-ℕ y) ＝ int-ℕ (x *ℕ y)
mul-int-ℕ zero-ℕ y = refl
mul-int-ℕ (succ-ℕ x) y =
  ( ap (_*ℤ (int-ℕ y)) (inv (succ-int-ℕ x))) ∙
  ( ( left-successor-law-mul-ℤ (int-ℕ x) (int-ℕ y)) ∙
    ( ( ( ap ((int-ℕ y) +ℤ_) (mul-int-ℕ x y)) ∙
        ( add-int-ℕ y (x *ℕ y))) ∙
      ( ap int-ℕ (commutative-add-ℕ y (x *ℕ y)))))

compute-mul-ℤ : (x y : ℤ) → x *ℤ y ＝ explicit-mul-ℤ x y
compute-mul-ℤ (inl zero-ℕ) (inl y) =
  inv (ap int-ℕ (left-unit-law-mul-ℕ (succ-ℕ y)))
compute-mul-ℤ (inl (succ-ℕ x)) (inl y) =
  ( ( ap ((int-ℕ (succ-ℕ y)) +ℤ_) (compute-mul-ℤ (inl x) (inl y))) ∙
    ( commutative-add-ℤ
      ( int-ℕ (succ-ℕ y))
      ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y))))) ∙
  ( add-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)) (succ-ℕ y))
compute-mul-ℤ (inl zero-ℕ) (inr (inl star)) = refl
compute-mul-ℤ (inl zero-ℕ) (inr (inr x)) = ap inl (inv (left-unit-law-add-ℕ x))
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inl star)) = right-zero-law-mul-ℤ (inl x)
compute-mul-ℤ (inl (succ-ℕ x)) (inr (inr y)) =
  ( ( ( ap ((inl y) +ℤ_) (compute-mul-ℤ (inl x) (inr (inr y)))) ∙
      ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))))) ∙
    ( ap
      ( neg-ℤ)
      ( commutative-add-ℤ
        ( int-ℕ (succ-ℕ y))
        ( int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))))) ∙
  ( ap neg-ℤ (add-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)) (succ-ℕ y)))
compute-mul-ℤ (inr (inl star)) (inl y) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inl y) = ap inl (inv (left-unit-law-add-ℕ y))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inl y) =
  ( ap ((inl y) +ℤ_) (compute-mul-ℤ (inr (inr x)) (inl y))) ∙
  ( ( ( inv
        ( distributive-neg-add-ℤ
          ( inr (inr y))
          ( inr (inr ((x *ℕ (succ-ℕ y)) +ℕ y))))) ∙
      ( ap
        ( neg-ℤ)
        ( ( add-int-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y))) ∙
          ( ap
            ( inr ∘ inr)
            ( left-successor-law-add-ℕ y ((x *ℕ (succ-ℕ y)) +ℕ y)))))) ∙
    ( ap inl (commutative-add-ℕ y ((succ-ℕ x) *ℕ (succ-ℕ y)))))
compute-mul-ℤ (inr (inl star)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inl star)) (inr (inr y)) = refl
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inl star)) = refl
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inl star)) =
  right-zero-law-mul-ℤ (inr (inr (succ-ℕ x)))
compute-mul-ℤ (inr (inr zero-ℕ)) (inr (inr y)) =
  ap
    ( inr ∘ inr)
    ( inv
      ( ( ap (_+ℕ y) (left-zero-law-mul-ℕ (succ-ℕ y))) ∙
        ( left-unit-law-add-ℕ y)))
compute-mul-ℤ (inr (inr (succ-ℕ x))) (inr (inr y)) =
  ( ap ((inr (inr y)) +ℤ_) (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) ∙
  ( ( add-int-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y))) ∙
    ( ap int-ℕ (commutative-add-ℕ (succ-ℕ y) ((succ-ℕ x) *ℕ (succ-ℕ y)))))
```

### Multiplication on integers distributes over the difference

```agda
left-distributive-mul-diff-ℤ :
  (z x y : ℤ) → z *ℤ (x -ℤ y) ＝ (z *ℤ x) -ℤ (z *ℤ y)
left-distributive-mul-diff-ℤ z x y =
  ( left-distributive-mul-add-ℤ z x (neg-ℤ y)) ∙
  ( ap ((z *ℤ x) +ℤ_) (right-negative-law-mul-ℤ z y))

right-distributive-mul-diff-ℤ :
  (x y z : ℤ) → (x -ℤ y) *ℤ z ＝ (x *ℤ z) -ℤ (y *ℤ z)
right-distributive-mul-diff-ℤ x y z =
  ( right-distributive-mul-add-ℤ x (neg-ℤ y) z) ∙
  ( ap ((x *ℤ z) +ℤ_) (left-negative-law-mul-ℤ y z))
```

### If the product of two integers is zero, one of the factors is zero

```agda
is-zero-is-zero-mul-ℤ :
  (x y : ℤ) → is-zero-ℤ (x *ℤ y) → (is-zero-ℤ x) + (is-zero-ℤ y)
is-zero-is-zero-mul-ℤ (inl x) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inl x) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inl x) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inl x) (inr (inr y))) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inl star)) y H = inl refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inl y) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inl y)) ∙ H))
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inl star)) H = inr refl
is-zero-is-zero-mul-ℤ (inr (inr x)) (inr (inr y)) H =
  ex-falso (Eq-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y))) ∙ H))
```

### Injectivity of multiplication by a nonzero integer

```agda
is-injective-left-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (x *ℤ_)
is-injective-left-mul-ℤ x f {y} {z} p =
  eq-diff-ℤ
    ( map-left-unit-law-coproduct-is-empty
      ( is-zero-ℤ x)
      ( is-zero-ℤ (y -ℤ z))
      ( f)
      ( is-zero-is-zero-mul-ℤ x
        ( y -ℤ z)
        ( left-distributive-mul-diff-ℤ x y z ∙ is-zero-diff-ℤ p)))

is-injective-right-mul-ℤ :
  (x : ℤ) → is-nonzero-ℤ x → is-injective (_*ℤ x)
is-injective-right-mul-ℤ x f {y} {z} p =
  is-injective-left-mul-ℤ
    ( x)
    ( f)
    ( commutative-mul-ℤ x y ∙ (p ∙ commutative-mul-ℤ z x))
```

### Multiplication by a nonzero integer is an embedding

```agda
is-emb-left-mul-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-emb (x *ℤ_)
is-emb-left-mul-ℤ x f =
  is-emb-is-injective is-set-ℤ (is-injective-left-mul-ℤ x f)

is-emb-right-mul-ℤ : (x : ℤ) → is-nonzero-ℤ x → is-emb (_*ℤ x)
is-emb-right-mul-ℤ x f =
  is-emb-is-injective is-set-ℤ (is-injective-right-mul-ℤ x f)
```

## See also

- Properties of multiplication with respect to inequality and positivity,
  nonnegativity, negativity and nonnpositivity of integers are derived in
  [`multiplication-positive-and-negative-integers`](elementary-number-theory.multiplication-positive-and-negative-integers.md)
