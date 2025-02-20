# Concatenation of lists

```agda
module lists.concatenation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import lists.lists
```

</details>

## Idea

Two lists can be concatenated to form a single list.

## Definition

```agda
concat-list : {l : Level} {A : UU l} → list A → (list A → list A)
concat-list {l} {A} = fold-list id (λ a f → (cons a) ∘ f)
```

## Properties

### List concatenation is associative and unital

Concatenation of lists is an associative operation and nil is the unit for list
concatenation.

```agda
associative-concat-list :
  {l1 : Level} {A : UU l1} (x y z : list A) →
  Id (concat-list (concat-list x y) z) (concat-list x (concat-list y z))
associative-concat-list nil y z = refl
associative-concat-list (cons a x) y z =
  ap (cons a) (associative-concat-list x y z)

left-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list nil x) x
left-unit-law-concat-list x = refl

right-unit-law-concat-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list x nil) x
right-unit-law-concat-list nil = refl
right-unit-law-concat-list (cons a x) =
  ap (cons a) (right-unit-law-concat-list x)

list-Monoid : {l : Level} (X : Set l) → Monoid l
list-Monoid X =
  pair
    ( pair (list-Set X) (pair concat-list associative-concat-list))
    ( pair nil (pair left-unit-law-concat-list right-unit-law-concat-list))
```

### `snoc`-laws for list concatenation

```agda
snoc-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) (a : A) →
  snoc (concat-list x y) a ＝ concat-list x (snoc y a)
snoc-concat-list nil y a = refl
snoc-concat-list (cons b x) y a = ap (cons b) (snoc-concat-list x y a)
```

```agda
snoc-concat-unit :
  {l1 : Level} {A : UU l1} (xs : list A) (a : A) →
  snoc xs a ＝ concat-list xs (unit-list a)
snoc-concat-unit nil a = refl
snoc-concat-unit (cons x xs) a = ap (cons x) (snoc-concat-unit xs a)
```

### The length of a concatenation of two lists is the sum of the length of the two lists

```agda
length-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id (length-list (concat-list x y)) ((length-list x) +ℕ (length-list y))
length-concat-list nil y = inv (left-unit-law-add-ℕ (length-list y))
length-concat-list (cons a x) y =
  ( ap succ-ℕ (length-concat-list x y)) ∙
  ( inv (left-successor-law-add-ℕ (length-list x) (length-list y)))
```

### An `η`-rule for lists

```agda
eta-list :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (head-list x) (tail-list x)) x
eta-list nil = refl
eta-list (cons a x) = refl

eta-list' :
  {l1 : Level} {A : UU l1} (x : list A) →
  Id (concat-list (remove-last-element-list x) (last-element-list x)) x
eta-list' nil = refl
eta-list' (cons a nil) = refl
eta-list' (cons a (cons b x)) = ap (cons a) (eta-list' (cons b x))
```

### Heads and tails of concatenated lists

```agda
head-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( head-list (concat-list x y))
    ( head-list (concat-list (head-list x) (head-list y)))
head-concat-list nil nil = refl
head-concat-list nil (cons x y) = refl
head-concat-list (cons a x) y = refl

tail-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( tail-list (concat-list x y))
    ( concat-list (tail-list x) (tail-list (concat-list (head-list x) y)))
tail-concat-list nil y = refl
tail-concat-list (cons a x) y = refl

last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( last-element-list (concat-list x y))
    ( last-element-list
      ( concat-list (last-element-list x) (last-element-list y)))
last-element-concat-list nil nil = refl
last-element-concat-list nil (cons b nil) = refl
last-element-concat-list nil (cons b (cons c y)) =
  last-element-concat-list nil (cons c y)
last-element-concat-list (cons a nil) nil = refl
last-element-concat-list (cons a nil) (cons b nil) = refl
last-element-concat-list (cons a nil) (cons b (cons c y)) =
  last-element-concat-list (cons a nil) (cons c y)
last-element-concat-list (cons a (cons b x)) y =
  last-element-concat-list (cons b x) y

remove-last-element-concat-list :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( remove-last-element-list (concat-list x y))
    ( concat-list
      ( remove-last-element-list (concat-list x (head-list y)))
      ( remove-last-element-list y))
remove-last-element-concat-list nil nil = refl
remove-last-element-concat-list nil (cons a nil) = refl
remove-last-element-concat-list nil (cons a (cons b y)) = refl
remove-last-element-concat-list (cons a nil) nil = refl
remove-last-element-concat-list (cons a nil) (cons b y) = refl
remove-last-element-concat-list (cons a (cons b x)) y =
  ap (cons a) (remove-last-element-concat-list (cons b x) y)

tail-concat-list' :
  {l1 : Level} {A : UU l1} (x y : list A) →
  Id
    ( tail-list (concat-list x y))
    ( concat-list
      ( tail-list x)
      ( tail-list (concat-list (last-element-list x) y)))
tail-concat-list' nil y = refl
tail-concat-list' (cons a nil) y = refl
tail-concat-list' (cons a (cons b x)) y =
  ap (cons b) (tail-concat-list' (cons b x) y)
```
