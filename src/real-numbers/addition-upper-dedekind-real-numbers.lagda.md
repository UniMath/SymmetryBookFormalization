# Addition of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.minkowski-multiplication-commutative-monoids

open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

We introduce
{{#concept "addition" Disambiguation="upper Dedekind real numbers" Agda=add-upper-ℝ}}
of two
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md) `x`
and `y`, which is an upper Dedekind real number with cut equal to the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
the cuts of `x` and `y`.

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  cut-add-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-add-upper-ℝ =
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)

  is-in-cut-add-upper-ℝ : ℚ → UU (l1 ⊔ l2)
  is-in-cut-add-upper-ℝ = is-in-subtype cut-add-upper-ℝ

  is-inhabited-cut-add-upper-ℝ : exists ℚ cut-add-upper-ℝ
  is-inhabited-cut-add-upper-ℝ =
    minkowski-mul-inhabited-is-inhabited-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)
      ( is-inhabited-cut-upper-ℝ x)
      ( is-inhabited-cut-upper-ℝ y)

  abstract
    is-rounded-cut-add-upper-ℝ :
      (q : ℚ) →
      is-in-cut-add-upper-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-add-upper-ℝ p)
    pr1 (is-rounded-cut-add-upper-ℝ q) q<x+y =
      do
        ((ux , uy) , (x<ux , y<uy , q=ux+uy)) ← q<x+y
        (ux' , ux'<ux , x<ux') ←
          forward-implication (is-rounded-cut-upper-ℝ x ux) x<ux
        (uy' , uy'<uy , y<uy') ←
          forward-implication (is-rounded-cut-upper-ℝ y uy) y<uy
        intro-exists
          ( ux' +ℚ uy')
          ( tr
              ( le-ℚ (ux' +ℚ uy'))
              ( inv (q=ux+uy))
              ( preserves-le-add-ℚ {ux'} {ux} {uy'} {uy} ux'<ux uy'<uy) ,
            intro-exists (ux' , uy') (x<ux' , y<uy' , refl))
      where
        open
          do-syntax-trunc-Prop (∃ ℚ (λ p → le-ℚ-Prop p q ∧ cut-add-upper-ℝ p))
    pr2 (is-rounded-cut-add-upper-ℝ q) exists-p =
      do
        (p , p<q , x+y<p) ← exists-p
        ((px , py) , (x<px , y<py , p=px+py)) ← x+y<p
        let
          q-p⁺ = positive-diff-le-ℚ p q p<q
          ε⁺ = mediant-zero-ℚ⁺ q-p⁺
          ε = rational-ℚ⁺ ε⁺
          ε<q-p = le-mediant-zero-ℚ⁺ q-p⁺
        intro-exists
          ( px +ℚ ε , q -ℚ (px +ℚ ε))
          ( is-in-cut-add-rational-ℚ⁺-upper-ℝ x px ε⁺ x<px ,
            is-in-cut-le-ℚ-upper-ℝ
              ( y)
              ( py)
              ( q -ℚ (px +ℚ ε))
              ( binary-tr
                ( le-ℚ)
                ( equational-reasoning
                    (q -ℚ px) -ℚ (q -ℚ p)
                    ＝ neg-ℚ px -ℚ neg-ℚ p
                      by left-translation-diff-ℚ (neg-ℚ px) (neg-ℚ p) q
                    ＝ neg-ℚ px +ℚ (px +ℚ py)
                      by ap (neg-ℚ px +ℚ_) (neg-neg-ℚ p ∙ p=px+py)
                    ＝ py
                      by is-retraction-left-div-Group group-add-ℚ px py)
                ( equational-reasoning
                  (q -ℚ px) -ℚ ε
                  ＝ q +ℚ (neg-ℚ px +ℚ neg-ℚ ε)
                    by associative-add-ℚ q (neg-ℚ px) (neg-ℚ ε)
                  ＝ q -ℚ (px +ℚ ε)
                    by ap (q +ℚ_) (inv (distributive-neg-add-ℚ px ε)))
                ( preserves-le-right-add-ℚ
                  ( q -ℚ px)
                  ( neg-ℚ (q -ℚ p))
                  ( neg-ℚ ε)
                  ( neg-le-ℚ ε (q -ℚ p) ε<q-p)))
              ( y<py) ,
            inv ( is-identity-right-conjugation-add-ℚ (px +ℚ ε) q))
      where open do-syntax-trunc-Prop (cut-add-upper-ℝ q)

  add-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  pr1 add-upper-ℝ = cut-add-upper-ℝ
  pr1 (pr2 add-upper-ℝ) = is-inhabited-cut-add-upper-ℝ
  pr2 (pr2 add-upper-ℝ) = is-rounded-cut-add-upper-ℝ
```

## Properties

### Addition of upper Dedekind real numbers is commutative

```agda
module _
  {l1 l2 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2)
  where

  commutative-add-upper-ℝ : add-upper-ℝ x y ＝ add-upper-ℝ y x
  commutative-add-upper-ℝ =
    eq-eq-cut-upper-ℝ
      ( add-upper-ℝ x y)
      ( add-upper-ℝ y x)
      ( commutative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-upper-ℝ x)
        ( cut-upper-ℝ y))
```

### Addition of upper Dedekind real numbers is associative

```agda
module _
  {l1 l2 l3 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2) (z : upper-ℝ l3)
  where

  associative-add-upper-ℝ :
    add-upper-ℝ (add-upper-ℝ x y) z ＝ add-upper-ℝ x (add-upper-ℝ y z)
  associative-add-upper-ℝ =
    eq-eq-cut-upper-ℝ
      ( add-upper-ℝ (add-upper-ℝ x y) z)
      ( add-upper-ℝ x (add-upper-ℝ y z))
      ( associative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-upper-ℝ x)
        ( cut-upper-ℝ y)
        ( cut-upper-ℝ z))
```

### Unit laws for addition of upper Dedekind real numbers

```agda
module _
  {l : Level} (x : upper-ℝ l)
  where

  right-unit-law-add-upper-ℝ : add-upper-ℝ x (upper-real-ℚ zero-ℚ) ＝ x
  right-unit-law-add-upper-ℝ =
    eq-sim-cut-upper-ℝ
      ( add-upper-ℝ x (upper-real-ℚ zero-ℚ))
      ( x)
      ( (λ r →
          elim-exists
            ( cut-upper-ℝ x r)
            ( λ (p , q) (x<p , 0<q , r=p+q) →
              inv-tr
                ( is-in-cut-upper-ℝ x)
                ( r=p+q)
                ( is-in-cut-add-rational-ℚ⁺-upper-ℝ
                  ( x)
                  ( p)
                  ( q , is-positive-le-zero-ℚ q 0<q)
                  ( x<p)))) ,
        ( λ q x<q →
          elim-exists
            ( cut-add-upper-ℝ x (upper-real-ℚ zero-ℚ) q)
            ( λ r (r<q , x<r) →
              intro-exists
                ( r , q -ℚ r)
                ( x<r ,
                  backward-implication (iff-translate-diff-le-zero-ℚ r q) r<q ,
                  inv (is-identity-right-conjugation-add-ℚ r q)))
            ( forward-implication (is-rounded-cut-upper-ℝ x q) x<q)))
```
