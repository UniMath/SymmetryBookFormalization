# Ideals of commutative semirings

```agda
module commutative-algebra.ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An **ideal** in a commutative semiring is a two-sided ideal in the underlying
semiring.

## Definitions

### Ideals in commutative semirings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-ideal-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Semiring =
    is-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

ideal-Commutative-Semiring :
  {l1 : Level} (l2 : Level) → Commutative-Semiring l1 → UU (l1 ⊔ lsuc l2)
ideal-Commutative-Semiring l2 A =
  ideal-Semiring l2 (semiring-Commutative-Semiring A)

module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (I : ideal-Commutative-Semiring l2 A)
  where

  subset-ideal-Commutative-Semiring : subset-Commutative-Semiring l2 A
  subset-ideal-Commutative-Semiring =
    subset-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-in-ideal-Commutative-Semiring : type-Commutative-Semiring A → UU l2
  is-in-ideal-Commutative-Semiring =
    is-in-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-prop-is-in-ideal-Commutative-Semiring :
    (x : type-Commutative-Semiring A) →
    is-prop (is-in-ideal-Commutative-Semiring x)
  is-prop-is-in-ideal-Commutative-Semiring =
    is-prop-is-in-ideal-Semiring (semiring-Commutative-Semiring A) I

  type-ideal-Commutative-Semiring : UU (l1 ⊔ l2)
  type-ideal-Commutative-Semiring =
    type-ideal-Semiring (semiring-Commutative-Semiring A) I

  inclusion-ideal-Commutative-Semiring :
    type-ideal-Commutative-Semiring → type-Commutative-Semiring A
  inclusion-ideal-Commutative-Semiring =
    inclusion-ideal-Semiring (semiring-Commutative-Semiring A) I

  ap-inclusion-ideal-Commutative-Semiring :
    (x y : type-ideal-Commutative-Semiring) → x ＝ y →
    inclusion-ideal-Commutative-Semiring x ＝
    inclusion-ideal-Commutative-Semiring y
  ap-inclusion-ideal-Commutative-Semiring =
    ap-inclusion-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-in-subset-inclusion-ideal-Commutative-Semiring :
    (x : type-ideal-Commutative-Semiring) →
    is-in-ideal-Commutative-Semiring (inclusion-ideal-Commutative-Semiring x)
  is-in-subset-inclusion-ideal-Commutative-Semiring =
    is-in-subset-inclusion-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-eq-ideal-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} → is-in-ideal-Commutative-Semiring x →
    (x ＝ y) → is-in-ideal-Commutative-Semiring y
  is-closed-under-eq-ideal-Commutative-Semiring =
    is-closed-under-eq-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-eq-ideal-Commutative-Semiring' :
    {x y : type-Commutative-Semiring A} → is-in-ideal-Commutative-Semiring y →
    (x ＝ y) → is-in-ideal-Commutative-Semiring x
  is-closed-under-eq-ideal-Commutative-Semiring' =
    is-closed-under-eq-ideal-Semiring' (semiring-Commutative-Semiring A) I

  is-ideal-subset-ideal-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring A subset-ideal-Commutative-Semiring
  is-ideal-subset-ideal-Commutative-Semiring =
    is-ideal-subset-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-additive-submonoid-ideal-Commutative-Semiring :
    is-additive-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( subset-ideal-Commutative-Semiring)
  is-additive-submonoid-ideal-Commutative-Semiring =
    is-additive-submonoid-ideal-Semiring (semiring-Commutative-Semiring A) I

  contains-zero-ideal-Commutative-Semiring :
    contains-zero-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  contains-zero-ideal-Commutative-Semiring =
    contains-zero-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-addition-ideal-Commutative-Semiring :
    is-closed-under-addition-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-addition-ideal-Commutative-Semiring =
    is-closed-under-addition-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-left-multiplication-ideal-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-left-multiplication-ideal-Commutative-Semiring =
    is-closed-under-left-multiplication-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-closed-under-right-multiplication-ideal-Commutative-Semiring :
    is-closed-under-right-multiplication-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-right-multiplication-ideal-Commutative-Semiring =
    is-closed-under-right-multiplication-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

ideal-left-ideal-Commutative-Semiring :
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A) →
  contains-zero-subset-Commutative-Semiring A S →
  is-closed-under-addition-subset-Commutative-Semiring A S →
  is-closed-under-left-multiplication-subset-Commutative-Semiring A S →
  ideal-Commutative-Semiring l2 A
pr1 (ideal-left-ideal-Commutative-Semiring A S z a m) = S
pr1 (pr1 (pr2 (ideal-left-ideal-Commutative-Semiring A S z a m))) = z
pr2 (pr1 (pr2 (ideal-left-ideal-Commutative-Semiring A S z a m))) = a
pr1 (pr2 (pr2 (ideal-left-ideal-Commutative-Semiring A S z a m))) = m
pr2 (pr2 (pr2 (ideal-left-ideal-Commutative-Semiring A S z a m))) x y H =
  is-closed-under-eq-subset-Commutative-Semiring A S
    ( m y x H)
    ( commutative-mul-Commutative-Semiring A y x)

ideal-right-ideal-Commutative-Semiring :
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A) →
  contains-zero-subset-Commutative-Semiring A S →
  is-closed-under-addition-subset-Commutative-Semiring A S →
  is-closed-under-right-multiplication-subset-Commutative-Semiring A S →
  ideal-Commutative-Semiring l2 A
pr1 (ideal-right-ideal-Commutative-Semiring A S z a m) = S
pr1 (pr1 (pr2 (ideal-right-ideal-Commutative-Semiring A S z a m))) = z
pr2 (pr1 (pr2 (ideal-right-ideal-Commutative-Semiring A S z a m))) = a
pr1 (pr2 (pr2 (ideal-right-ideal-Commutative-Semiring A S z a m))) x y H =
  is-closed-under-eq-subset-Commutative-Semiring A S
    ( m y x H)
    ( commutative-mul-Commutative-Semiring A y x)
pr2 (pr2 (pr2 (ideal-right-ideal-Commutative-Semiring A S z a m))) = m
```
