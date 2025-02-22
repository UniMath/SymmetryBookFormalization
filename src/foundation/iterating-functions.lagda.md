# Iterating functions

```agda
module foundation.iterating-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplicative-monoid-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.endomorphisms
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoid-actions
```

</details>

## Idea

Any map `f : X → X` can be iterated by repeatedly applying `f`

## Definition

### Iterating functions

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate : ℕ → (X → X) → (X → X)
  iterate zero-ℕ f x = x
  iterate (succ-ℕ k) f x = f (iterate k f x)

  iterate' : ℕ → (X → X) → (X → X)
  iterate' zero-ℕ f x = x
  iterate' (succ-ℕ k) f x = iterate' k f (f x)
```

### Homotopies of iterating functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (s : A → A) (t : B → B)
  where

  coherence-square-iterate :
    {f : A → B} (H : coherence-square-maps f s t f) →
    (n : ℕ) → coherence-square-maps f (iterate n s) (iterate n t) f
  coherence-square-iterate {f} H zero-ℕ x = refl
  coherence-square-iterate {f} H (succ-ℕ n) =
    pasting-vertical-coherence-square-maps
      ( f)
      ( iterate n s)
      ( iterate n t)
      ( f)
      ( s)
      ( t)
      ( f)
      ( coherence-square-iterate H n)
      ( H)
```

## Properties

### The two definitions of iterating are homotopic

```agda
module _
  {l : Level} {X : UU l}
  where

  reassociate-iterate-succ-ℕ :
    (k : ℕ) (f : X → X) (x : X) → iterate (succ-ℕ k) f x ＝ iterate k f (f x)
  reassociate-iterate-succ-ℕ zero-ℕ f x = refl
  reassociate-iterate-succ-ℕ (succ-ℕ k) f x =
    ap f (reassociate-iterate-succ-ℕ k f x)

  reassociate-iterate : (k : ℕ) (f : X → X) → iterate k f ~ iterate' k f
  reassociate-iterate zero-ℕ f x = refl
  reassociate-iterate (succ-ℕ k) f x =
    reassociate-iterate-succ-ℕ k f x ∙ reassociate-iterate k f (f x)
```

### For any map `f : X → X`, iterating `f` defines a monoid action of ℕ on `X`

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate-add-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k +ℕ l) f x ＝ iterate k f (iterate l f x)
  iterate-add-ℕ k zero-ℕ f x = refl
  iterate-add-ℕ k (succ-ℕ l) f x =
    ap f (iterate-add-ℕ k l f x) ∙
    reassociate-iterate-succ-ℕ k f (iterate l f x)

  left-unit-law-iterate-add-ℕ :
    (l : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ 0 l f x ＝ ap (λ t → iterate t f x) (left-unit-law-add-ℕ l)
  left-unit-law-iterate-add-ℕ zero-ℕ f x = refl
  left-unit-law-iterate-add-ℕ (succ-ℕ l) f x =
    ( right-unit) ∙
    ( ( ap² f (left-unit-law-iterate-add-ℕ l f x)) ∙
      ( ( inv (ap-comp f (λ t → iterate t f x) (left-unit-law-add-ℕ l))) ∙
        ( ap-comp (λ t → iterate t f x) succ-ℕ (left-unit-law-add-ℕ l))))

  right-unit-law-iterate-add-ℕ :
    (k : ℕ) (f : X → X) (x : X) →
    iterate-add-ℕ k 0 f x ＝ ap (λ t → iterate t f x) (right-unit-law-add-ℕ k)
  right-unit-law-iterate-add-ℕ k f x = refl

  iterate-iterate :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate k f (iterate l f x) ＝ iterate l f (iterate k f x)
  iterate-iterate k l f x =
    ( inv (iterate-add-ℕ k l f x)) ∙
    ( ( ap (λ t → iterate t f x) (commutative-add-ℕ k l)) ∙
      ( iterate-add-ℕ l k f x))

  iterate-mul-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (k *ℕ l) f x ＝ iterate k (iterate l f) x
  iterate-mul-ℕ zero-ℕ l f x = refl
  iterate-mul-ℕ (succ-ℕ k) l f x =
    ( iterate-add-ℕ (k *ℕ l) l f x) ∙
    ( ( iterate-mul-ℕ k l f (iterate l f x)) ∙
      ( inv (reassociate-iterate-succ-ℕ k (iterate l f) x)))

  iterate-exp-ℕ :
    (k l : ℕ) (f : X → X) (x : X) →
    iterate (exp-ℕ l k) f x ＝ iterate k (iterate l) f x
  iterate-exp-ℕ zero-ℕ l f x = refl
  iterate-exp-ℕ (succ-ℕ k) l f x =
    ( iterate-mul-ℕ (exp-ℕ l k) l f x) ∙
    ( ( iterate-exp-ℕ k l (iterate l f) x) ∙
      ( inv (htpy-eq (reassociate-iterate-succ-ℕ k (iterate l) f) x)))

module _
  {l : Level} (X : Set l)
  where

  iterative-action-Monoid : action-Monoid l ℕ*-Monoid
  pr1 iterative-action-Monoid = endo-Set X
  pr1 (pr1 (pr2 iterative-action-Monoid)) k f = iterate k f
  pr2 (pr1 (pr2 iterative-action-Monoid)) {k} {l} =
    eq-htpy (λ f → eq-htpy (λ x → iterate-mul-ℕ k l f x))
  pr2 (pr2 iterative-action-Monoid) = refl
```

## External links

- [Function iteration](https://www.wikidata.org/wiki/Q5254619) on Wikidata
