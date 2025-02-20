# Arithmetically located Dedekind cuts

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.arithmetically-located-dedekind-cuts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Definition

A pair of a [lower Dedekind cut](real-numbers.lower-dedekind-real-numbers.md)
`L` and an [upper Dedekind cut](real-numbers.upper-dedekind-real-numbers.md) `U`
is
{{#concept "arithmetically located" Disambiguation="Dedekind cut" Agda=is-arithmetically-located-lower-upper-ℝ}}
if for any [positive](elementary-number-theory.positive-rational-numbers.md)
[rational number](elementary-number-theory.rational-numbers.md) `ε : ℚ⁺`, there
exists `p, q : ℚ` where `p ∈ L` and `q ∈ U`, such that `0 < q - p < ε`.
Intuitively, when `L , U` represent the cuts of a real number `x`, `p` and `q`
are rational approximations of `x` to within `ε`.

This follows parts of Section 11 in {{#cite BauerTaylor2009}}.

## Definitions

### The predicate of being arithmetically located on pairs of lower and upper Dedekind real numbers

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  arithmetically-located-prop-lower-upper-ℝ : Prop (l1 ⊔ l2)
  arithmetically-located-prop-lower-upper-ℝ =
    Π-Prop
      ( ℚ⁺)
      ( λ ε⁺ → ∃
        ( ℚ × ℚ)
        ( λ (p , q) →
          le-ℚ-Prop q (p +ℚ rational-ℚ⁺ ε⁺) ∧
          cut-lower-ℝ x p ∧
          cut-upper-ℝ y q))

  is-arithmetically-located-lower-upper-ℝ : UU (l1 ⊔ l2)
  is-arithmetically-located-lower-upper-ℝ =
    type-Prop (arithmetically-located-prop-lower-upper-ℝ)
```

## Properties

### Arithmetically located cuts are located

If a pair of lower and upper Dedekind cuts is arithmetically located, it is also
located.

```agda
module _
  {l1 l2 : Level} (x : lower-ℝ l1) (y : upper-ℝ l2)
  where

  abstract
    is-located-is-arithmetically-located-lower-upper-ℝ :
      is-arithmetically-located-lower-upper-ℝ x y →
      is-located-lower-upper-ℝ x y
    is-located-is-arithmetically-located-lower-upper-ℝ
      arithmetically-located p q p<q =
      elim-exists
        ( cut-lower-ℝ x p ∨ cut-upper-ℝ y q)
        ( λ (p' , q') (q'<p'+q-p , p'∈L , q'∈U) →
          rec-coproduct
            ( λ p<p' →
              inl-disjunction
                ( is-in-cut-le-ℚ-lower-ℝ x p p' p<p' p'∈L))
            ( λ p'≤p →
              inr-disjunction
                ( is-in-cut-le-ℚ-upper-ℝ
                  ( y)
                  ( q')
                  ( q)
                  ( concatenate-le-leq-ℚ
                    ( q')
                    ( p' +ℚ (q -ℚ p))
                    ( q)
                    ( q'<p'+q-p)
                  ( tr
                    ( leq-ℚ (p' +ℚ (q -ℚ p)))
                    ( is-identity-right-conjugation-Ab abelian-group-add-ℚ p q)
                    ( preserves-leq-left-add-ℚ (q -ℚ p) p' p p'≤p)))
                  ( q'∈U)))
            ( decide-le-leq-ℚ p p'))
        ( arithmetically-located (positive-diff-le-ℚ p q p<q))
```

### The Dedekind cuts of real numbers are arithmetically located

```agda
module _
  {l : Level}
  (x : ℝ l)
  where

  abstract
    arithmetic-location-from-multiple-difference-in-lower-upper-cut-ℝ :
      (p ε : ℚ) →
      (n : ℕ) →
      is-positive-ℚ ε →
      is-in-lower-cut-ℝ x p →
      is-in-upper-cut-ℝ x (p +ℚ (rational-ℤ (int-ℕ n) *ℚ ε)) →
      exists ℚ ( λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ ε +ℚ ε))
    arithmetic-location-from-multiple-difference-in-lower-upper-cut-ℝ
      p ε zero-ℕ positive-ε p<x p-plus-0-ε-in-U =
      ex-falso
        ( is-disjoint-cut-ℝ
          ( x)
          ( p)
          ( p<x ,
            tr
              ( is-in-upper-cut-ℝ x)
              ( ap (p +ℚ_) (left-zero-law-mul-ℚ ε) ∙ right-unit-law-add-ℚ p)
              ( p-plus-0-ε-in-U)))
    arithmetic-location-from-multiple-difference-in-lower-upper-cut-ℝ
      p ε (succ-ℕ n) positive-ε p<x p-plus-sn-ε-in-U =
      elim-disjunction
        ( ∃ ℚ ( λ q → lower-cut-ℝ x q ∧ upper-cut-ℝ x (q +ℚ ε +ℚ ε)))
        ( λ p+ε-in-L →
          arithmetic-location-from-multiple-difference-in-lower-upper-cut-ℝ
            ( p +ℚ ε)
            ( ε)
            ( n)
            ( positive-ε)
            ( p+ε-in-L)
            ( tr
              ( is-in-upper-cut-ℝ x)
              ( equational-reasoning
                p +ℚ (rational-ℤ (int-ℕ (succ-ℕ n)) *ℚ ε)
                ＝ p +ℚ (rational-ℤ (succ-ℤ (int-ℕ n)) *ℚ ε)
                  by ap
                      ( λ x → p +ℚ (rational-ℤ x *ℚ ε))
                      ( inv (succ-int-ℕ n))
                ＝ p +ℚ (succ-ℚ (rational-ℤ (int-ℕ n)) *ℚ ε)
                  by ap (p +ℚ_) (ap (_*ℚ ε) (inv (succ-rational-ℤ (int-ℕ n))))
                ＝ p +ℚ (ε +ℚ rational-ℤ (int-ℕ n) *ℚ ε)
                  by ap (p +ℚ_) (mul-left-succ-ℚ (rational-ℤ (int-ℕ n)) ε)
                ＝ (p +ℚ ε) +ℚ (rational-ℤ (int-ℕ n) *ℚ ε)
                  by inv (associative-add-ℚ p ε (rational-ℤ (int-ℕ n) *ℚ ε)))
              ( p-plus-sn-ε-in-U)))
        ( λ p+2ε-in-U → intro-exists p (p<x , p+2ε-in-U))
        ( is-located-lower-upper-cut-ℝ
          ( x)
          ( p +ℚ ε)
          ( (p +ℚ ε) +ℚ ε)
          ( le-right-add-rational-ℚ⁺ (p +ℚ ε) (ε , positive-ε)))

  abstract
    bounded-arithmetic-location-twice-ε :
      (p q ε : ℚ) →
      is-positive-ℚ ε →
      is-in-lower-cut-ℝ x p →
      is-in-upper-cut-ℝ x q →
      exists
        ℚ
        ( λ r →
          lower-cut-ℝ x r ∧
          upper-cut-ℝ x (r +ℚ ε +ℚ ε))
    bounded-arithmetic-location-twice-ε p q ε pos-ε p<x x<q =
      elim-exists
        ( ∃ ℚ ( λ r → lower-cut-ℝ x r ∧ upper-cut-ℝ x (r +ℚ ε +ℚ ε)))
        ( λ n q-p<nε →
          arithmetic-location-from-multiple-difference-in-lower-upper-cut-ℝ
            ( p)
            ( ε)
            ( n)
            ( pos-ε)
            ( p<x)
            ( le-upper-cut-ℝ
              ( x)
              ( q)
              ( p +ℚ rational-ℤ (int-ℕ n) *ℚ ε)
              ( tr
                ( λ r → le-ℚ r (p +ℚ rational-ℤ (int-ℕ n) *ℚ ε))
                ( is-identity-right-conjugation-Ab abelian-group-add-ℚ p q)
                ( preserves-le-right-add-ℚ
                  ( p)
                  ( q -ℚ p)
                  ( rational-ℤ (int-ℕ n) *ℚ ε) q-p<nε))
              ( x<q)))
        ( archimedean-property-ℚ ε (q -ℚ p) pos-ε)

  abstract
    is-arithmetically-located-lower-upper-real-ℝ :
      is-arithmetically-located-lower-upper-ℝ
        ( lower-real-ℝ x)
        ( upper-real-ℝ x)
    is-arithmetically-located-lower-upper-real-ℝ ε⁺@(ε , positive-ε) =
      do
        (ε' , pos-ε') , 2ε'<ε ← double-le-ℚ⁺ ε⁺
        (p , p<x) ← is-inhabited-lower-cut-ℝ x
        (q , x<q) ← is-inhabited-upper-cut-ℝ x
        (r , r<x , x<r+2ε') ←
          bounded-arithmetic-location-twice-ε p q ε' pos-ε' p<x x<q
        intro-exists
          ( r , r +ℚ ε' +ℚ ε')
          ( tr
              ( λ s → le-ℚ s (r +ℚ ε))
              ( inv (associative-add-ℚ r ε' ε'))
              ( preserves-le-right-add-ℚ r (ε' +ℚ ε') ε 2ε'<ε) ,
            r<x ,
            x<r+2ε')
      where
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ × ℚ)
              ( λ (p , q) →
                le-ℚ-Prop q (p +ℚ ε) ∧ lower-cut-ℝ x p ∧ upper-cut-ℝ x q))
```

## References

{{#bibliography}}
