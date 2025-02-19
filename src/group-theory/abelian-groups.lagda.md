# Abelian groups

```agda
module group-theory.abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.central-elements-groups
open import group-theory.commutative-monoids
open import group-theory.commutator-subgroups
open import group-theory.commutators-of-elements-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.monoids
open import group-theory.nullifying-group-homomorphisms
open import group-theory.pullbacks-subgroups
open import group-theory.semigroups
open import group-theory.subgroups
open import group-theory.subgroups-generated-by-families-of-elements-groups
open import group-theory.trivial-subgroups

open import lists.concatenation-lists
open import lists.lists

open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

**Abelian groups** are [groups](group-theory.groups.md) of which the group
operation is commutative. It is common to write abelian groups additively, i.e.,
to write

```text
  x + y
```

for the group operation of an abelian group, `0` for its unit element, and `-x`
for the inverse of `x`.

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Group : {l : Level} → Group l → Prop l
is-abelian-prop-Group G =
  Π-Prop
    ( type-Group G)
    ( λ x →
      Π-Prop
        ( type-Group G)
        ( λ y →
          Id-Prop (set-Group G) (mul-Group G x y) (mul-Group G y x)))

is-abelian-Group : {l : Level} → Group l → UU l
is-abelian-Group G = type-Prop (is-abelian-prop-Group G)

is-prop-is-abelian-Group :
  {l : Level} (G : Group l) → is-prop (is-abelian-Group G)
is-prop-is-abelian-Group G =
  is-prop-type-Prop (is-abelian-prop-Group G)
```

### The type of abelian groups

```agda
Ab : (l : Level) → UU (lsuc l)
Ab l = Σ (Group l) is-abelian-Group

module _
  {l : Level} (A : Ab l)
  where

  group-Ab : Group l
  group-Ab = pr1 A

  set-Ab : Set l
  set-Ab = set-Group group-Ab

  type-Ab : UU l
  type-Ab = type-Group group-Ab

  is-set-type-Ab : is-set type-Ab
  is-set-type-Ab = is-set-type-Group group-Ab

  has-associative-add-Ab : has-associative-mul-Set set-Ab
  has-associative-add-Ab = has-associative-mul-Group group-Ab

  add-Ab : type-Ab → type-Ab → type-Ab
  add-Ab = mul-Group group-Ab

  add-Ab' : type-Ab → type-Ab → type-Ab
  add-Ab' = mul-Group' group-Ab

  ap-add-Ab :
    {x y x' y' : type-Ab} → x ＝ x' → y ＝ y' → add-Ab x y ＝ add-Ab x' y'
  ap-add-Ab p q = ap-binary add-Ab p q

  associative-add-Ab :
    (x y z : type-Ab) → add-Ab (add-Ab x y) z ＝ add-Ab x (add-Ab y z)
  associative-add-Ab = associative-mul-Group group-Ab

  semigroup-Ab : Semigroup l
  semigroup-Ab = semigroup-Group group-Ab

  is-group-Ab : is-group-Semigroup semigroup-Ab
  is-group-Ab = is-group-Group group-Ab

  has-zero-Ab : is-unital-Semigroup semigroup-Ab
  has-zero-Ab = is-unital-Group group-Ab

  zero-Ab : type-Ab
  zero-Ab = unit-Group group-Ab

  is-zero-Ab : type-Ab → UU l
  is-zero-Ab = is-unit-Group group-Ab

  is-zero-Ab' : type-Ab → UU l
  is-zero-Ab' = is-unit-Group' group-Ab

  is-prop-is-zero-Ab : (x : type-Ab) → is-prop (is-zero-Ab x)
  is-prop-is-zero-Ab = is-prop-is-unit-Group group-Ab

  is-zero-prop-Ab : type-Ab → Prop l
  is-zero-prop-Ab = is-unit-prop-Group group-Ab

  left-unit-law-add-Ab : (x : type-Ab) → add-Ab zero-Ab x ＝ x
  left-unit-law-add-Ab = left-unit-law-mul-Group group-Ab

  right-unit-law-add-Ab : (x : type-Ab) → add-Ab x zero-Ab ＝ x
  right-unit-law-add-Ab = right-unit-law-mul-Group group-Ab

  has-negatives-Ab : is-group-is-unital-Semigroup semigroup-Ab has-zero-Ab
  has-negatives-Ab = has-inverses-Group group-Ab

  neg-Ab : type-Ab → type-Ab
  neg-Ab = inv-Group group-Ab

  left-inverse-law-add-Ab :
    (x : type-Ab) → add-Ab (neg-Ab x) x ＝ zero-Ab
  left-inverse-law-add-Ab = left-inverse-law-mul-Group group-Ab

  right-inverse-law-add-Ab :
    (x : type-Ab) → add-Ab x (neg-Ab x) ＝ zero-Ab
  right-inverse-law-add-Ab = right-inverse-law-mul-Group group-Ab

  commutative-add-Ab : (x y : type-Ab) → Id (add-Ab x y) (add-Ab y x)
  commutative-add-Ab = pr2 A

  interchange-add-add-Ab :
    (a b c d : type-Ab) →
    add-Ab (add-Ab a b) (add-Ab c d) ＝ add-Ab (add-Ab a c) (add-Ab b d)
  interchange-add-add-Ab =
    interchange-law-commutative-and-associative
      add-Ab
      commutative-add-Ab
      associative-add-Ab

  right-swap-add-Ab :
    (a b c : type-Ab) → add-Ab (add-Ab a b) c ＝ add-Ab (add-Ab a c) b
  right-swap-add-Ab a b c =
    ( associative-add-Ab a b c) ∙
    ( ap (add-Ab a) (commutative-add-Ab b c)) ∙
    ( inv (associative-add-Ab a c b))

  left-swap-add-Ab :
    (a b c : type-Ab) → add-Ab a (add-Ab b c) ＝ add-Ab b (add-Ab a c)
  left-swap-add-Ab a b c =
    ( inv (associative-add-Ab a b c)) ∙
    ( ap (add-Ab' c) (commutative-add-Ab a b)) ∙
    ( associative-add-Ab b a c)

  distributive-neg-add-Ab :
    (x y : type-Ab) →
    neg-Ab (add-Ab x y) ＝ add-Ab (neg-Ab x) (neg-Ab y)
  distributive-neg-add-Ab x y =
    ( distributive-inv-mul-Group group-Ab) ∙
    ( commutative-add-Ab (neg-Ab y) (neg-Ab x))

  neg-neg-Ab : (x : type-Ab) → neg-Ab (neg-Ab x) ＝ x
  neg-neg-Ab = inv-inv-Group group-Ab

  neg-zero-Ab : neg-Ab zero-Ab ＝ zero-Ab
  neg-zero-Ab = inv-unit-Group group-Ab

  transpose-eq-neg-Ab :
    {x y : type-Ab} → neg-Ab x ＝ y → x ＝ neg-Ab y
  transpose-eq-neg-Ab = transpose-eq-inv-Group group-Ab

  transpose-eq-neg-Ab' :
    {x y : type-Ab} → x ＝ neg-Ab y → neg-Ab x ＝ y
  transpose-eq-neg-Ab' = transpose-eq-inv-Group' group-Ab
```

### The underlying commutative monoid of an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  monoid-Ab : Monoid l
  pr1 monoid-Ab = semigroup-Ab A
  pr1 (pr2 monoid-Ab) = zero-Ab A
  pr1 (pr2 (pr2 monoid-Ab)) = left-unit-law-add-Ab A
  pr2 (pr2 (pr2 monoid-Ab)) = right-unit-law-add-Ab A

  commutative-monoid-Ab : Commutative-Monoid l
  pr1 commutative-monoid-Ab = monoid-Ab
  pr2 commutative-monoid-Ab = commutative-add-Ab A
```

### The structure of an abelian group

```agda
structure-abelian-group :
  {l1 : Level} → UU l1 → UU l1
structure-abelian-group X =
  Σ (structure-group X) (λ p → is-abelian-Group (group-structure-group X p))

abelian-group-structure-abelian-group :
  {l1 : Level} → (X : UU l1) → structure-abelian-group X → Ab l1
pr1 (abelian-group-structure-abelian-group X (p , q)) =
  group-structure-group X p
pr2 (abelian-group-structure-abelian-group X (p , q)) = q
```

### Conjugation in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  equiv-left-conjugation-Ab : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-left-conjugation-Ab = equiv-left-conjugation-Group (group-Ab A)

  equiv-right-conjugation-Ab : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-right-conjugation-Ab = equiv-right-conjugation-Group (group-Ab A)

  equiv-conjugation-Ab : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-conjugation-Ab = equiv-conjugation-Group (group-Ab A)

  left-conjugation-Ab : (x : type-Ab A) → type-Ab A → type-Ab A
  left-conjugation-Ab = left-conjugation-Group (group-Ab A)

  right-conjugation-Ab : (x : type-Ab A) → type-Ab A → type-Ab A
  right-conjugation-Ab = right-conjugation-Group (group-Ab A)

  conjugation-Ab : (x : type-Ab A) → type-Ab A → type-Ab A
  conjugation-Ab = conjugation-Group (group-Ab A)

  equiv-conjugation-Ab' : (x : type-Ab A) → type-Ab A ≃ type-Ab A
  equiv-conjugation-Ab' = equiv-conjugation-Group' (group-Ab A)

  conjugation-Ab' : (x : type-Ab A) → type-Ab A → type-Ab A
  conjugation-Ab' = conjugation-Group' (group-Ab A)

  left-right-conjugation-Ab :
    (x : type-Ab A) → left-conjugation-Ab x ~ right-conjugation-Ab x
  left-right-conjugation-Ab = left-right-conjugation-Group (group-Ab A)
```

### Commutators in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  commutator-Ab : type-Ab A → type-Ab A → type-Ab A
  commutator-Ab x y = commutator-Group (group-Ab A) x y
```

### The commutator subgroup of an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  family-of-commutators-Ab : type-Ab A × type-Ab A → type-Ab A
  family-of-commutators-Ab = family-of-commutators-Group (group-Ab A)

  commutator-subgroup-Ab : Subgroup l (group-Ab A)
  commutator-subgroup-Ab = commutator-subgroup-Group (group-Ab A)
```

### Any abelian group element yields a type equipped with an automorphism

```agda
module _
  {l : Level} (A : Ab l) (a : type-Ab A)
  where

  pointed-type-with-aut-Ab : Pointed-Type-With-Aut l
  pointed-type-with-aut-Ab = pointed-type-with-aut-Group (group-Ab A) a
```

## Properties

### Addition on an abelian group is a binary equivalence

#### Addition on the left is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  left-subtraction-Ab : type-Ab A → type-Ab A → type-Ab A
  left-subtraction-Ab = left-div-Group (group-Ab A)

  ap-left-subtraction-Ab :
    {x x' y y' : type-Ab A} → x ＝ x' → y ＝ y' →
    left-subtraction-Ab x y ＝ left-subtraction-Ab x' y'
  ap-left-subtraction-Ab = ap-left-div-Group (group-Ab A)

  is-section-left-subtraction-Ab :
    (x : type-Ab A) → (add-Ab A x ∘ left-subtraction-Ab x) ~ id
  is-section-left-subtraction-Ab = is-section-left-div-Group (group-Ab A)

  is-retraction-left-subtraction-Ab :
    (x : type-Ab A) → (left-subtraction-Ab x ∘ add-Ab A x) ~ id
  is-retraction-left-subtraction-Ab = is-retraction-left-div-Group (group-Ab A)

  is-equiv-add-Ab : (x : type-Ab A) → is-equiv (add-Ab A x)
  is-equiv-add-Ab = is-equiv-mul-Group (group-Ab A)

  equiv-add-Ab : type-Ab A → (type-Ab A ≃ type-Ab A)
  equiv-add-Ab = equiv-mul-Group (group-Ab A)
```

#### Addition on the right is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  right-subtraction-Ab : type-Ab A → type-Ab A → type-Ab A
  right-subtraction-Ab = right-div-Group (group-Ab A)

  ap-right-subtraction-Ab :
    {x x' y y' : type-Ab A} → x ＝ x' → y ＝ y' →
    right-subtraction-Ab x y ＝ right-subtraction-Ab x' y'
  ap-right-subtraction-Ab = ap-right-div-Group (group-Ab A)

  is-section-right-subtraction-Ab :
    (x : type-Ab A) →
    (add-Ab' A x ∘ (λ y → right-subtraction-Ab y x)) ~ id
  is-section-right-subtraction-Ab = is-section-right-div-Group (group-Ab A)

  is-retraction-right-subtraction-Ab :
    (x : type-Ab A) →
    ((λ y → right-subtraction-Ab y x) ∘ add-Ab' A x) ~ id
  is-retraction-right-subtraction-Ab =
    is-retraction-right-div-Group (group-Ab A)

  is-equiv-add-Ab' : (x : type-Ab A) → is-equiv (add-Ab' A x)
  is-equiv-add-Ab' = is-equiv-mul-Group' (group-Ab A)

  equiv-add-Ab' : type-Ab A → (type-Ab A ≃ type-Ab A)
  equiv-add-Ab' = equiv-mul-Group' (group-Ab A)
```

#### Addition on an abelian group is a binary equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-equiv-add-Ab : is-binary-equiv (add-Ab A)
  is-binary-equiv-add-Ab = is-binary-equiv-mul-Group (group-Ab A)
```

### Addition on an abelian group is a binary embedding

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-binary-emb-add-Ab : is-binary-emb (add-Ab A)
  is-binary-emb-add-Ab = is-binary-emb-mul-Group (group-Ab A)

  is-emb-add-Ab : (x : type-Ab A) → is-emb (add-Ab A x)
  is-emb-add-Ab = is-emb-mul-Group (group-Ab A)

  is-emb-add-Ab' : (x : type-Ab A) → is-emb (add-Ab' A x)
  is-emb-add-Ab' = is-emb-mul-Group' (group-Ab A)
```

### Addition on an abelian group is pointwise injective from both sides

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-injective-add-Ab : (x : type-Ab A) → is-injective (add-Ab A x)
  is-injective-add-Ab = is-injective-mul-Group (group-Ab A)

  is-injective-add-Ab' : (x : type-Ab A) → is-injective (add-Ab' A x)
  is-injective-add-Ab' = is-injective-mul-Group' (group-Ab A)
```

### Transposing identifications in abelian groups

```agda
module _
  {l : Level} (A : Ab l)
  where

  transpose-eq-add-Ab :
    {x y z : type-Ab A} →
    Id (add-Ab A x y) z → Id x (add-Ab A z (neg-Ab A y))
  transpose-eq-add-Ab = transpose-eq-mul-Group (group-Ab A)

  inv-transpose-eq-add-Ab :
    {x y z : type-Ab A} →
    Id x (add-Ab A z (neg-Ab A y)) → add-Ab A x y ＝ z
  inv-transpose-eq-add-Ab = inv-transpose-eq-mul-Group (group-Ab A)

  transpose-eq-add-Ab' :
    {x y z : type-Ab A} →
    Id (add-Ab A x y) z → Id y (add-Ab A (neg-Ab A x) z)
  transpose-eq-add-Ab' = transpose-eq-mul-Group' (group-Ab A)

  inv-transpose-eq-add-Ab' :
    {x y z : type-Ab A} →
    Id y (add-Ab A (neg-Ab A x) z) → Id (add-Ab A x y) z
  inv-transpose-eq-add-Ab' = inv-transpose-eq-mul-Group' (group-Ab A)

  double-transpose-eq-add-Ab :
    {x y z w : type-Ab A} →
    add-Ab A y w ＝ add-Ab A x z →
    left-subtraction-Ab A x y ＝ right-subtraction-Ab A z w
  double-transpose-eq-add-Ab =
    double-transpose-eq-mul-Group (group-Ab A)

  double-transpose-eq-add-Ab' :
    {x y z w : type-Ab A} →
    add-Ab A z x ＝ add-Ab A w y →
    right-subtraction-Ab A x y ＝ left-subtraction-Ab A z w
  double-transpose-eq-add-Ab' =
    double-transpose-eq-mul-Group' (group-Ab A)
```

### Any idempotent element in an abelian group is zero

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-idempotent-Ab : type-Ab A → UU l
  is-idempotent-Ab = is-idempotent-Group (group-Ab A)

  is-zero-is-idempotent-Ab :
    {x : type-Ab A} → is-idempotent-Ab x → is-zero-Ab A x
  is-zero-is-idempotent-Ab = is-unit-is-idempotent-Group (group-Ab A)
```

### Taking negatives of elements of an abelian group is an equivalence

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-equiv-neg-Ab : is-equiv (neg-Ab A)
  is-equiv-neg-Ab = is-equiv-inv-Group (group-Ab A)

  equiv-equiv-neg-Ab : type-Ab A ≃ type-Ab A
  equiv-equiv-neg-Ab = equiv-equiv-inv-Group (group-Ab A)
```

### Two elements `x` and `y` are equal iff `-x + y = 0`

```agda
module _
  {l : Level} (A : Ab l)
  where

  eq-is-zero-left-subtraction-Ab :
    {x y : type-Ab A} →
    is-zero-Ab A (left-subtraction-Ab A x y) → x ＝ y
  eq-is-zero-left-subtraction-Ab =
    eq-is-unit-left-div-Group (group-Ab A)

  is-zero-left-subtraction-Ab :
    {x y : type-Ab A} →
    x ＝ y → is-zero-Ab A (left-subtraction-Ab A x y)
  is-zero-left-subtraction-Ab = is-unit-left-div-eq-Group (group-Ab A)
```

### Two elements `x` and `y` are equal iff `x - y = 0`

```agda
module _
  {l : Level} (A : Ab l)
  where

  eq-is-zero-right-subtraction-Ab :
    {x y : type-Ab A} →
    is-zero-Ab A (right-subtraction-Ab A x y) → x ＝ y
  eq-is-zero-right-subtraction-Ab =
    eq-is-unit-right-div-Group (group-Ab A)

  is-zero-right-subtraction-eq-Ab :
    {x y : type-Ab A} →
    x ＝ y → is-zero-Ab A (right-subtraction-Ab A x y)
  is-zero-right-subtraction-eq-Ab =
    is-unit-right-div-eq-Group (group-Ab A)
```

### The negative of `-x + y` is `-y + x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  neg-left-subtraction-Ab :
    (x y : type-Ab A) →
    neg-Ab A (left-subtraction-Ab A x y) ＝ left-subtraction-Ab A y x
  neg-left-subtraction-Ab = inv-left-div-Group (group-Ab A)
```

### The negative of `x - y` is `y - x`

```agda
module _
  {l : Level} (A : Ab l)
  where

  neg-right-subtraction-Ab :
    (x y : type-Ab A) →
    neg-Ab A (right-subtraction-Ab A x y) ＝ right-subtraction-Ab A y x
  neg-right-subtraction-Ab = inv-right-div-Group (group-Ab A)
```

### The sum of `-x + y` and `-y + z` is `-x + z`

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-left-subtraction-Ab :
    (x y z : type-Ab A) →
    add-Ab A (left-subtraction-Ab A x y) (left-subtraction-Ab A y z) ＝
    left-subtraction-Ab A x z
  add-left-subtraction-Ab = mul-left-div-Group (group-Ab A)
```

### The sum of `x - y` and `y - z` is `x - z`

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-right-subtraction-Ab :
    (x y z : type-Ab A) →
    add-Ab A (right-subtraction-Ab A x y) (right-subtraction-Ab A y z) ＝
    right-subtraction-Ab A x z
  add-right-subtraction-Ab = mul-right-div-Group (group-Ab A)
```

### Conjugation is the identity function

**Proof:** Consider two elements `x` and `y` of an abelian group. Then

```text
  (x + y) - x ＝ (y + x) - x ＝ y,
```

where the last step holds at once since the function `_ - x` is a
[retraction](foundation-core.retractions.md) of the function `_ + x`.

Note that this is a fairly common way to make quick calculations.

```agda
module _
  {l : Level} (A : Ab l)
  where

  abstract
    is-identity-left-conjugation-Ab :
      (x : type-Ab A) → left-conjugation-Ab A x ~ id
    is-identity-left-conjugation-Ab x y =
      ( ap (add-Ab' A (neg-Ab A x)) (commutative-add-Ab A x y)) ∙
      ( is-retraction-right-subtraction-Ab A x y)

    is-identity-right-conjugation-Ab :
      (x : type-Ab A) → right-conjugation-Ab A x ~ id
    is-identity-right-conjugation-Ab x =
      inv-htpy (left-right-conjugation-Ab A x) ∙h
      is-identity-left-conjugation-Ab x

  is-identity-conjugation-Ab :
    (x : type-Ab A) → conjugation-Ab A x ~ id
  is-identity-conjugation-Ab = is-identity-left-conjugation-Ab
```

### Laws for conjugation and addition

```agda
module _
  {l : Level} (A : Ab l)
  where

  htpy-conjugation-Ab :
    (x : type-Ab A) →
    conjugation-Ab' A x ~ conjugation-Ab A (neg-Ab A x)
  htpy-conjugation-Ab = htpy-conjugation-Group (group-Ab A)

  htpy-conjugation-Ab' :
    (x : type-Ab A) →
    conjugation-Ab A x ~ conjugation-Ab' A (neg-Ab A x)
  htpy-conjugation-Ab' = htpy-conjugation-Group' (group-Ab A)

  conjugation-zero-Ab :
    (x : type-Ab A) → conjugation-Ab A x (zero-Ab A) ＝ zero-Ab A
  conjugation-zero-Ab = conjugation-unit-Group (group-Ab A)

  right-conjugation-law-add-Ab :
    (x y : type-Ab A) →
    add-Ab A (neg-Ab A x) (conjugation-Ab A x y) ＝
    right-subtraction-Ab A y x
  right-conjugation-law-add-Ab =
    right-conjugation-law-mul-Group (group-Ab A)

  right-conjugation-law-add-Ab' :
    (x y : type-Ab A) →
    add-Ab A x (conjugation-Ab' A x y) ＝ add-Ab A y x
  right-conjugation-law-add-Ab' =
    right-conjugation-law-mul-Group' (group-Ab A)

  left-conjugation-law-add-Ab :
    (x y : type-Ab A) →
    add-Ab A (conjugation-Ab A x y) x ＝ add-Ab A x y
  left-conjugation-law-add-Ab =
    left-conjugation-law-mul-Group (group-Ab A)

  left-conjugation-law-add-Ab' :
    (x y : type-Ab A) →
    add-Ab A (conjugation-Ab' A x y) (neg-Ab A x) ＝
    left-subtraction-Ab A x y
  left-conjugation-law-add-Ab' =
    left-conjugation-law-mul-Group' (group-Ab A)

  distributive-conjugation-add-Ab :
    (x y z : type-Ab A) →
    conjugation-Ab A x (add-Ab A y z) ＝
    add-Ab A (conjugation-Ab A x y) (conjugation-Ab A x z)
  distributive-conjugation-add-Ab =
    distributive-conjugation-mul-Group (group-Ab A)

  conjugation-neg-Ab :
    (x y : type-Ab A) →
    conjugation-Ab A x (neg-Ab A y) ＝ neg-Ab A (conjugation-Ab A x y)
  conjugation-neg-Ab = conjugation-inv-Group (group-Ab A)

  conjugation-neg-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab' A x (neg-Ab A y) ＝
    neg-Ab A (conjugation-Ab' A x y)
  conjugation-neg-Ab' = conjugation-inv-Group' (group-Ab A)

  conjugation-left-subtraction-Ab :
    (x y : type-Ab A) →
    conjugation-Ab A x (left-subtraction-Ab A x y) ＝
    right-subtraction-Ab A y x
  conjugation-left-subtraction-Ab =
    conjugation-left-div-Group (group-Ab A)

  conjugation-left-subtraction-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab A y (left-subtraction-Ab A x y) ＝
    right-subtraction-Ab A y x
  conjugation-left-subtraction-Ab' =
    conjugation-left-div-Group' (group-Ab A)

  conjugation-right-subtraction-Ab :
    (x y : type-Ab A) →
    conjugation-Ab' A y (right-subtraction-Ab A x y) ＝
    left-subtraction-Ab A y x
  conjugation-right-subtraction-Ab =
    conjugation-right-div-Group (group-Ab A)

  conjugation-right-subtraction-Ab' :
    (x y : type-Ab A) →
    conjugation-Ab' A x (right-subtraction-Ab A x y) ＝
    left-subtraction-Ab A y x
  conjugation-right-subtraction-Ab' =
    conjugation-right-div-Group' (group-Ab A)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  add-list-Ab : list (type-Ab A) → type-Ab A
  add-list-Ab = mul-list-Group (group-Ab A)

  preserves-concat-add-list-Ab :
    (l1 l2 : list (type-Ab A)) →
    Id
      ( add-list-Ab (concat-list l1 l2))
      ( add-Ab A (add-list-Ab l1) (add-list-Ab l2))
  preserves-concat-add-list-Ab =
    preserves-concat-mul-list-Group (group-Ab A)
```

### A group is abelian if and only if every element is central

**Proof:** These two conditions are the same on the nose.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-every-element-central-Group :
    ((x : type-Group G) → is-central-element-Group G x) → is-abelian-Group G
  is-abelian-every-element-central-Group = id

  every-element-central-is-abelian-Group :
    is-abelian-Group G → ((x : type-Group G) → is-central-element-Group G x)
  every-element-central-is-abelian-Group = id
```

### A group is abelian if and only if every commutator is equal to the unit

**Proof:** For any two elements `u` and `v` in a group we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (uv⁻¹ ＝ 1) ↔ (u ＝ v).
```

Since the [commutator](group-theory.commutators-of-elements-groups.md) of `x`
and `y` is defined as `[x,y] := (xy)(yx)⁻¹`, we see that the claim is a direct
consequence of this logical equivalence.

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-is-unit-commutator-Group :
    ((x y : type-Group G) → is-unit-Group G (commutator-Group G x y)) →
    is-abelian-Group G
  is-abelian-is-unit-commutator-Group H x y =
    eq-is-unit-right-div-Group G (H x y)

  is-abelian-is-unit-commutator-Group' :
    ((x y : type-Group G) → is-unit-Group' G (commutator-Group G x y)) →
    is-abelian-Group G
  is-abelian-is-unit-commutator-Group' H x y =
    eq-is-unit-right-div-Group G (inv (H x y))

  is-unit-commutator-is-abelian-Group :
    is-abelian-Group G →
    (x y : type-Group G) → is-unit-Group G (commutator-Group G x y)
  is-unit-commutator-is-abelian-Group H x y =
    is-unit-right-div-eq-Group G (H x y)

  is-unit-commutator-is-abelian-Group' :
    is-abelian-Group G →
    (x y : type-Group G) → is-unit-Group' G (commutator-Group G x y)
  is-unit-commutator-is-abelian-Group' H x y =
    inv (is-unit-right-div-eq-Group G (H x y))

module _
  {l : Level} (A : Ab l)
  where

  is-zero-commutator-Ab :
    (x y : type-Ab A) → is-zero-Ab A (commutator-Ab A x y)
  is-zero-commutator-Ab =
    is-unit-commutator-is-abelian-Group (group-Ab A) (commutative-add-Ab A)

  is-zero-commutator-Ab' :
    (x y : type-Ab A) → is-zero-Ab' A (commutator-Ab A x y)
  is-zero-commutator-Ab' =
    is-unit-commutator-is-abelian-Group' (group-Ab A) (commutative-add-Ab A)
```

### A group is abelian if and only if its commutator subgroup is trivial

**Proof:** We saw above that a group is abelian if and only if every commutator
is the unit element. The latter condition holds if and only if the
[subgroup generated by](group-theory.subgroups-generated-by-families-of-elements-groups.md)
the commutators, i.e., the commutator subgroup, is
[trivial](group-theory.trivial-subgroups.md).

```agda
module _
  {l : Level} (G : Group l)
  where

  is-abelian-is-trivial-commutator-subgroup-Group :
    is-trivial-Subgroup G (commutator-subgroup-Group G) →
    is-abelian-Group G
  is-abelian-is-trivial-commutator-subgroup-Group H =
    is-abelian-is-unit-commutator-Group' G
      ( λ x y →
        is-family-of-units-is-trivial-subgroup-family-of-elements-Group G
          ( family-of-commutators-Group G)
          ( H)
          ( x , y))

module _
  {l : Level} (A : Ab l)
  where

  abstract
    is-trivial-commutator-subgroup-Ab :
      is-trivial-Subgroup (group-Ab A) (commutator-subgroup-Ab A)
    is-trivial-commutator-subgroup-Ab =
      is-trivial-subgroup-family-of-elements-Group
        ( group-Ab A)
        ( family-of-commutators-Ab A)
        ( λ (x , y) → is-zero-commutator-Ab' A x y)
```

### Every group homomorphism into an abelian group nullifies the commutator subgroup

**Proof:** Consider a [group homomorphism](group-theory.homomorphisms-groups.md)
`f : G → A` into an abelian group `A`. Our goal is to show that `f`
[nullifies](group-theory.nullifying-group-homomorphisms.md) the commutator
subgroup `[G,G]`, i.e., that `[G,G]` is contained in the
[kernel](group-theory.kernels-homomorphisms-groups.md) of `f`.

Since `A` is abelian it follows that the commutator subgroup of `A` is
[trivial](group-theory.trivial-subgroups.md). Furthermore, any group
homomorphism maps the commutator subgroup to the commutator subgroup, i.e., we
have `f [G,G] ⊆ [A,A]`. Since the commutator subgroup `[A,A]` is trivial, this
means that `f` nullifies the commutator subgroup of `G`.

```agda
module _
  {l1 l2 : Level} (G : Group l1) (A : Ab l2)
  where

  nullifies-commutator-normal-subgroup-hom-group-Ab :
    (f : hom-Group G (group-Ab A)) →
    nullifies-normal-subgroup-hom-Group G
      ( group-Ab A)
      ( f)
      ( commutator-normal-subgroup-Group G)
  nullifies-commutator-normal-subgroup-hom-group-Ab f =
    transitive-leq-Subgroup G
      ( commutator-subgroup-Group G)
      ( pullback-Subgroup G
        ( group-Ab A)
        ( f)
        ( commutator-subgroup-Group (group-Ab A)))
      ( pullback-Subgroup G (group-Ab A) f (trivial-Subgroup (group-Ab A)))
      ( λ x → is-trivial-commutator-subgroup-Ab A _)
      ( preserves-commutator-subgroup-hom-Group G (group-Ab A) f)

  is-equiv-hom-nullifying-hom-group-Ab :
    is-equiv
      ( hom-nullifying-hom-Group G
        ( group-Ab A)
        ( commutator-normal-subgroup-Group G))
  is-equiv-hom-nullifying-hom-group-Ab =
    is-equiv-inclusion-is-full-subtype
      ( λ f →
        nullifies-normal-subgroup-prop-hom-Group G
          ( group-Ab A)
          ( f)
          ( commutator-normal-subgroup-Group G))
      ( nullifies-commutator-normal-subgroup-hom-group-Ab)

  compute-nullifying-hom-group-Ab :
    nullifying-hom-Group G (group-Ab A) (commutator-normal-subgroup-Group G) ≃
    hom-Group G (group-Ab A)
  compute-nullifying-hom-group-Ab =
    equiv-inclusion-is-full-subtype
      ( λ f →
        nullifies-normal-subgroup-prop-hom-Group G
          ( group-Ab A)
          ( f)
          ( commutator-normal-subgroup-Group G))
      ( nullifies-commutator-normal-subgroup-hom-group-Ab)
```
