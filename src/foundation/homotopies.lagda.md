---
title: Homotopies
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.homotopies where

open import foundation-core.homotopies public

open import foundation-core.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path; is-contr-total-path')
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; is-equiv-id)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.functoriality-dependent-function-types using
  ( is-equiv-map-Π)
open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)
open import foundation-core.sections using (sec)
open import foundation-core.universe-levels using (UU; Level; _⊔_)

open import foundation.function-extensionality using
  ( equiv-funext; eq-htpy; FUNEXT; htpy-eq; funext)
open import foundation.identity-systems using
  ( Ind-identity-system; fundamental-theorem-id-IND-identity-system)
open import foundation.identity-types using
  ( Id; _＝_; refl; _∙_; concat; inv; assoc; left-unit; right-unit; left-inv;
    right-inv; ap; inv-con; con-inv; concat'; distributive-inv-concat; ap-inv;
    ap-id; is-injective-concat'; inv-inv; issec-inv-concat'; isretr-inv-concat';
    is-equiv-inv-con; is-equiv-con-inv)
```

## Idea

A homotopy of identifications is a pointwise equality between dependent functions.

### Transpositions of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  inv-con-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
  inv-con-htpy H K L M x = inv-con (H x) (K x) (L x) (M x)

  con-inv-htpy :
    (H : f ~ g) (K : g ~ h) (L : f ~ h) → (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
  con-inv-htpy H K L M x = con-inv (H x) (K x) (L x) (M x)
```

### Homotopies preserve the laws of the acion on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) (K K' : g ~ h) → K ~ K' → (H ∙h K) ~ (H ∙h K')
  ap-concat-htpy H K K' L x = ap (concat (H x) (h x)) (L x)

  ap-concat-htpy' :
    (H H' : f ~ g) (K : g ~ h) → H ~ H' → (H ∙h K) ~ (H' ∙h K)
  ap-concat-htpy' H H' K L x =
    ap (concat' _ (K x)) (L x)
    
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy :
    H ~ H' → (inv-htpy H) ~ (inv-htpy H')
  ap-inv-htpy K x = ap inv (K x)
```

### Whiskering an inverted homotopy

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  left-whisk-inv-htpy :
    {f f' : A → B} (g : B → C) (H : f ~ f') →
    (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
  left-whisk-inv-htpy g H x = ap-inv g (H x)

  right-whisk-inv-htpy :
    {g g' : B → C} (H : g ~ g') (f : A → B) →
    ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
  right-whisk-inv-htpy H f = refl-htpy
```

### The total space of homotopies is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where
  
  abstract
    is-contr-total-htpy : is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
    is-contr-total-htpy =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (Id f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path f)

  abstract
    is-contr-total-htpy' : is-contr (Σ ((x : A) → B x) (λ g → g ~ f))
    is-contr-total-htpy' =
      is-contr-equiv'
        ( Σ ((x : A) → B x) (λ g → g ＝ f))
        ( equiv-tot (λ g → equiv-funext))
        ( is-contr-total-path' f)
```

### Homotopy induction

```agda
ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-refl-htpy f C)
```

## Properties

```agda
abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system f
      ( refl-htpy)
      ( is-contr-total-htpy f)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    ({l : Level} → IND-HTPY {l3 = l} f) → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ g → htpy-eq)
```

```agda
abstract
  Ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l3} f
  Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
  ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
  ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
  comp-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    (c : C f refl-htpy) → ind-htpy f C c refl-htpy ＝ c
  comp-htpy f C = pr2 (Ind-htpy f C)
```

## Properties

```agda
abstract
  is-equiv-inv-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    (f g : (x : A) → B x) → is-equiv (inv-htpy {f = f} {g = g})
  is-equiv-inv-htpy f g =
    is-equiv-has-inverse
      ( inv-htpy)
      ( λ H → eq-htpy (λ x → inv-inv (H x)))
      ( λ H → eq-htpy (λ x → inv-inv (H x)))

equiv-inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → (f ~ g) ≃ (g ~ f)
pr1 (equiv-inv-htpy f g) = inv-htpy
pr2 (equiv-inv-htpy f g) = is-equiv-inv-htpy f g

abstract
  is-equiv-concat-htpy :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    {f g : (x : A) → B x} (H : f ~ g) →
    (h : (x : A) → B x) → is-equiv (concat-htpy H h)
  is-equiv-concat-htpy {A = A} {B = B} {f} =
    ind-htpy f
      ( λ g H → (h : (x : A) → B x) → is-equiv (concat-htpy H h))
      ( λ h → is-equiv-id)

equiv-concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g) (h : (x : A) → B x) →
  (g ~ h) ≃ (f ~ h)
pr1 (equiv-concat-htpy H h) = concat-htpy H h
pr2 (equiv-concat-htpy H h) = is-equiv-concat-htpy H h

inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ h) → (f ~ g)
inv-concat-htpy' f K = concat-htpy' f (inv-htpy K)

issec-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((concat-htpy' f K) ∘ (inv-concat-htpy' f K)) ~ id
issec-inv-concat-htpy' f K L =
  eq-htpy (λ x → issec-inv-concat' (f x) (K x) (L x))

isretr-inv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x}
  (K : g ~ h) → ((inv-concat-htpy' f K) ∘ (concat-htpy' f K)) ~ id
isretr-inv-concat-htpy' f K L =
  eq-htpy (λ x → isretr-inv-concat' (f x) (K x) (L x))

is-equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  is-equiv (concat-htpy' f K)
is-equiv-concat-htpy' f K =
  is-equiv-has-inverse
    ( inv-concat-htpy' f K)
    ( issec-inv-concat-htpy' f K)
    ( isretr-inv-concat-htpy' f K)

equiv-concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} (K : g ~ h) →
  (f ~ g) ≃ (f ~ h)
pr1 (equiv-concat-htpy' f K) = concat-htpy' f K
pr2 (equiv-concat-htpy' f K) = is-equiv-concat-htpy' f K
```

### Transposing homotopies

```agda
abstract
  is-equiv-inv-con-htpy :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (inv-con-htpy H K L)
  is-equiv-inv-con-htpy H K L =
    is-equiv-map-Π _ (λ x → is-equiv-inv-con (H x) (K x) (L x))

equiv-inv-con-htpy :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (K ~ ((inv-htpy H) ∙h L))
pr1 (equiv-inv-con-htpy H K L) = inv-con-htpy H K L
pr2 (equiv-inv-con-htpy H K L) = is-equiv-inv-con-htpy H K L

abstract
  is-equiv-con-inv-htpy :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
    ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
    is-equiv (con-inv-htpy H K L)
  is-equiv-con-inv-htpy H K L =
    is-equiv-map-Π _ (λ x → is-equiv-con-inv (H x) (K x) (L x))

equiv-con-inv-htpy :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  ( H : f ~ g) (K : g ~ h) (L : f ~ h) →
  ( (H ∙h K) ~ L) ≃ (H ~ (L ∙h (inv-htpy K)))
pr1 (equiv-con-inv-htpy H K L) = con-inv-htpy H K L
pr2 (equiv-con-inv-htpy H K L) = is-equiv-con-inv-htpy H K L
```
