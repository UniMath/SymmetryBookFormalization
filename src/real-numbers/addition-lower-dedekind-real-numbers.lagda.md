# Addition of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-lower-dedekind-real-numbers where
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

open import logic.functoriality-existential-quantification

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
```

</details>

## Idea

We introduce
{{#concept "addition" Disambiguation="lower Dedekind real numbers" Agda=add-lower-ℝ}}
of two
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md) `x`
and `y`, which is a lower Dedekind real number with cut equal to the
[Minkowski sum](group-theory.minkowski-multiplication-commutative-monoids.md) of
the cuts of `x` and `y`.

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-add-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-add-lower-ℝ =
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)

  is-in-cut-add-lower-ℝ : ℚ → UU (l1 ⊔ l2)
  is-in-cut-add-lower-ℝ = is-in-subtype cut-add-lower-ℝ

  is-inhabited-cut-add-lower-ℝ : exists ℚ cut-add-lower-ℝ
  is-inhabited-cut-add-lower-ℝ =
    minkowski-mul-inhabited-is-inhabited-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      ( is-inhabited-cut-lower-ℝ x)
      ( is-inhabited-cut-lower-ℝ y)

  abstract
    is-rounded-cut-add-lower-ℝ :
      (q : ℚ) →
      is-in-cut-add-lower-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-add-lower-ℝ r)
    pr1 (is-rounded-cut-add-lower-ℝ q) q<x+y =
      do
        ((lx , ly) , (lx<x , ly<y , q=lx+ly)) ← q<x+y
        (lx' , lx<lx' , lx'<x) ←
          forward-implication (is-rounded-cut-lower-ℝ x lx) lx<x
        (ly' , ly<ly' , ly'<y) ←
          forward-implication (is-rounded-cut-lower-ℝ y ly) ly<y
        intro-exists
          ( lx' +ℚ ly')
          ( tr
              ( λ p → le-ℚ p (lx' +ℚ ly'))
              ( inv q=lx+ly)
              ( preserves-le-add-ℚ {lx} {lx'} {ly} {ly'} lx<lx' ly<ly') ,
            intro-exists (lx' , ly') (lx'<x , ly'<y , refl))
      where
        open
          do-syntax-trunc-Prop (∃ ℚ (λ r → le-ℚ-Prop q r ∧ cut-add-lower-ℝ r))
    pr2 (is-rounded-cut-add-lower-ℝ q) exists-r =
      do
        (r , q<r , r<x+y) ← exists-r
        ((rx , ry) , (rx<x , ry<y , r=rx+ry)) ← r<x+y
        let
          r-q⁺ = positive-diff-le-ℚ q r q<r
          ε⁺ = mediant-zero-ℚ⁺ r-q⁺
          ε = rational-ℚ⁺ ε⁺
          ε<r-q = le-mediant-zero-ℚ⁺ r-q⁺
        intro-exists
          ( rx -ℚ ε , q -ℚ (rx -ℚ ε))
          ( is-in-cut-diff-rational-ℚ⁺-lower-ℝ x rx ε⁺ rx<x ,
            is-in-cut-le-ℚ-lower-ℝ
              ( y)
              ( q -ℚ (rx -ℚ ε))
              ( ry)
              ( binary-tr
                ( le-ℚ)
                ( equational-reasoning
                  (q -ℚ rx) +ℚ ε
                  ＝ q +ℚ (neg-ℚ rx +ℚ ε)
                    by associative-add-ℚ q (neg-ℚ rx) ε
                  ＝ q +ℚ (ε -ℚ rx)
                    by ap (q +ℚ_) (commutative-add-ℚ (neg-ℚ rx) ε)
                  ＝ q -ℚ (rx -ℚ ε)
                    by ap (q +ℚ_) (inv (distributive-neg-diff-ℚ rx ε)))
                ( equational-reasoning
                  (q -ℚ rx) +ℚ (r -ℚ q)
                  ＝ (q -ℚ rx) -ℚ (q -ℚ r)
                    by ap ((q -ℚ rx) +ℚ_) (inv (distributive-neg-diff-ℚ q r))
                  ＝ neg-ℚ rx -ℚ neg-ℚ r
                    by left-translation-diff-ℚ (neg-ℚ rx) (neg-ℚ r) q
                  ＝ neg-ℚ rx +ℚ (rx +ℚ ry)
                    by ap (neg-ℚ rx +ℚ_) (neg-neg-ℚ r ∙ r=rx+ry)
                  ＝ ry
                    by is-retraction-left-div-Group group-add-ℚ rx ry)
                ( preserves-le-right-add-ℚ (q -ℚ rx) ε (r -ℚ q) ε<r-q))
              ( ry<y) ,
            inv ( is-identity-right-conjugation-add-ℚ (rx -ℚ ε) q))
      where open do-syntax-trunc-Prop (cut-add-lower-ℝ q)

  add-lower-ℝ : lower-ℝ (l1 ⊔ l2)
  pr1 add-lower-ℝ = cut-add-lower-ℝ
  pr1 (pr2 add-lower-ℝ) = is-inhabited-cut-add-lower-ℝ
  pr2 (pr2 add-lower-ℝ) = is-rounded-cut-add-lower-ℝ
```

## Properties

### Addition of lower Dedekind real numbers is commutative

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : lower-ℝ l2)
  where

  commutative-add-lower-ℝ : add-lower-ℝ x y ＝ add-lower-ℝ y x
  commutative-add-lower-ℝ =
    eq-eq-cut-lower-ℝ
      ( add-lower-ℝ x y)
      ( add-lower-ℝ y x)
      ( commutative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-lower-ℝ x)
        ( cut-lower-ℝ y))
```

### Addition of lower Dedekind real numbers is associative

```agda
module _
  {l1 l2 l3 : Level} (x : lower-ℝ l1) (y : lower-ℝ l2) (z : lower-ℝ l3)
  where

  associative-add-lower-ℝ :
    add-lower-ℝ (add-lower-ℝ x y) z ＝ add-lower-ℝ x (add-lower-ℝ y z)
  associative-add-lower-ℝ =
    eq-eq-cut-lower-ℝ
      ( add-lower-ℝ (add-lower-ℝ x y) z)
      ( add-lower-ℝ x (add-lower-ℝ y z))
      ( associative-minkowski-mul-Commutative-Monoid
        ( commutative-monoid-add-ℚ)
        ( cut-lower-ℝ x)
        ( cut-lower-ℝ y)
        ( cut-lower-ℝ z))
```

### Unit laws for the addition of lower Dedekind real numbers

```agda
module _
  {l : Level} (x : lower-ℝ l)
  where

  abstract
    right-unit-law-add-lower-ℝ : add-lower-ℝ x (lower-real-ℚ zero-ℚ) ＝ x
    right-unit-law-add-lower-ℝ =
      eq-sim-cut-lower-ℝ
        ( add-lower-ℝ x (lower-real-ℚ zero-ℚ))
        ( x)
        ( (λ r →
            elim-exists
              ( cut-lower-ℝ x r)
              ( λ (p , q) (p<x , q<0 , r=p+q) →
                inv-tr
                  ( is-in-cut-lower-ℝ x)
                  ( r=p+q ∙ ap (p +ℚ_) (inv (neg-neg-ℚ q)))
                  ( is-in-cut-diff-rational-ℚ⁺-lower-ℝ
                    ( x)
                    ( p)
                    ( neg-ℚ q ,
                      is-positive-le-zero-ℚ (neg-ℚ q) (neg-le-ℚ q zero-ℚ q<0))
                    ( p<x)))) ,
          (λ p p<x →
            elim-exists
              ( cut-add-lower-ℝ x (lower-real-ℚ zero-ℚ) p)
              ( λ q (p<q , q<x) →
                intro-exists
                  ( q , p -ℚ q)
                  ( q<x ,
                    tr
                      ( λ r → le-ℚ r zero-ℚ)
                      ( distributive-neg-diff-ℚ q p)
                      ( neg-le-ℚ
                        ( zero-ℚ)
                        ( q -ℚ p)
                        ( backward-implication
                          ( iff-translate-diff-le-zero-ℚ p q)
                          ( p<q))) ,
                    inv (is-identity-right-conjugation-add-ℚ q p)))
              ( forward-implication (is-rounded-cut-lower-ℝ x p) p<x)))

  left-unit-law-add-lower-ℝ : add-lower-ℝ (lower-real-ℚ zero-ℚ) x ＝ x
  left-unit-law-add-lower-ℝ =
    commutative-add-lower-ℝ (lower-real-ℚ zero-ℚ) x ∙ right-unit-law-add-lower-ℝ
```
