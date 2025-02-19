# Bezout's lemma in the integers

```agda
module elementary-number-theory.bezouts-lemma-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.bezouts-lemma-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

Bézout's Lemma is the [60th](literature.100-theorems.md#60) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}. It was
originally added to agda-unimath by [Bryan Lu](https://blu-bird.github.io).

## Lemma

```agda
bezouts-lemma-eqn-to-int :
  (x y : ℤ) → (H : is-nonzero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))) →
  nat-gcd-ℤ x y ＝
  dist-ℕ
    ( abs-ℤ
      ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H) *ℤ x))
    ( abs-ℤ
      ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) *ℤ y))
bezouts-lemma-eqn-to-int x y H =
  equational-reasoning
    nat-gcd-ℤ x y
    ＝ dist-ℕ
      ( (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H) *ℕ (abs-ℤ x))
      ( (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H) *ℕ (abs-ℤ y))
      by (inv (bezouts-lemma-eqn-ℕ (abs-ℤ x) (abs-ℤ y) H))
    ＝ dist-ℕ
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ x))
        ( mul-ℕ
          ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( K *ℕ (abs-ℤ x))
              ( mul-ℕ
                ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)
                ( abs-ℤ y)))
          ( inv
            ( abs-int-ℕ
              ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ x))
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( mul-ℕ
                ( abs-ℤ
                  ( int-ℕ
                    ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H)))
                ( abs-ℤ x))
              ( K *ℕ (abs-ℤ y)))
        (inv
          ( abs-int-ℕ
            ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))))
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( x)))
        ( mul-ℕ
          ( abs-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
          ( abs-ℤ y))
      by
        ( ap
          ( λ K →
            dist-ℕ
              ( K)
              ( mul-ℕ
                ( abs-ℤ
                  ( int-ℕ
                    ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H)))
                ( abs-ℤ y)))
          ( inv
            ( distributive-abs-mul-ℤ
              ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
              ( x))))
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( x)))
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))
            ( y)))
      by
        ( ap
          ( dist-ℕ
            ( abs-ℤ
              ( mul-ℤ
                ( int-ℕ
                  ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) H))
                ( x))))
          ( inv
            ( distributive-abs-mul-ℤ
              ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) H))
              ( y))))

refactor-pos-cond :
  (x y : ℤ) → (H : is-positive-ℤ x) → (K : is-positive-ℤ y) →
  is-nonzero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
refactor-pos-cond x y H _ =
  is-nonzero-abs-ℤ x H ∘ is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

bezouts-lemma-refactor-hypotheses :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  nat-gcd-ℤ x y ＝
  abs-ℤ
    ( diff-ℤ
      ( mul-ℤ
        ( int-ℕ
          ( minimal-positive-distance-x-coeff
            ( abs-ℤ x)
            ( abs-ℤ y)
            ( refactor-pos-cond x y H K)))
        ( x))
      ( mul-ℤ
        ( int-ℕ
          ( minimal-positive-distance-y-coeff
            ( abs-ℤ x)
            ( abs-ℤ y)
            ( refactor-pos-cond x y H K)))
        ( y)))
bezouts-lemma-refactor-hypotheses x y H K =
  equational-reasoning
    nat-gcd-ℤ x y
    ＝ dist-ℕ
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( x)))
        ( abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( y)))
      by bezouts-lemma-eqn-to-int x y P
    ＝ dist-ℤ
        ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P) *ℤ x)
        ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P) *ℤ y)
      by
        dist-abs-ℤ
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( x))
          ( mul-ℤ
            ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
            ( y))
        x-product-nonneg y-product-nonneg
  where
  P : is-nonzero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
  P = (refactor-pos-cond x y H K)
  x-product-nonneg :
    is-nonnegative-ℤ
      ( int-ℕ (minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P) *ℤ x)
  x-product-nonneg =
    is-nonnegative-mul-ℤ
      ( is-nonnegative-int-ℕ
        ( minimal-positive-distance-x-coeff (abs-ℤ x) (abs-ℤ y) P))
      ( is-nonnegative-is-positive-ℤ H)
  y-product-nonneg :
    is-nonnegative-ℤ
      ( int-ℕ (minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P) *ℤ y)
  y-product-nonneg =
    is-nonnegative-mul-ℤ
      ( is-nonnegative-int-ℕ
        ( minimal-positive-distance-y-coeff (abs-ℤ x) (abs-ℤ y) P))
      ( is-nonnegative-is-positive-ℤ K)

bezouts-lemma-pos-ints :
  (x y : ℤ) (H : is-positive-ℤ x) (K : is-positive-ℤ y) →
  Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
bezouts-lemma-pos-ints x y H K =
  sx-ty-nonneg-case-split
    ( decide-is-nonnegative-is-nonnegative-neg-ℤ {(s *ℤ x) -ℤ (t *ℤ y)})
  where
  s : ℤ
  s = int-ℕ (minimal-positive-distance-x-coeff
    (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))
  t : ℤ
  t = int-ℕ (minimal-positive-distance-y-coeff
    (abs-ℤ x) (abs-ℤ y) (refactor-pos-cond x y H K))

  sx-ty-nonneg-case-split :
    ( is-nonnegative-ℤ ((s *ℤ x) -ℤ (t *ℤ y)) +
      is-nonnegative-ℤ (neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y)))) →
    Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
  pr1 (sx-ty-nonneg-case-split (inl pos)) = s
  pr1 (pr2 (sx-ty-nonneg-case-split (inl pos))) = neg-ℤ t
  pr2 (pr2 (sx-ty-nonneg-case-split (inl pos))) =
    inv
    ( equational-reasoning
        gcd-ℤ x y
        ＝ int-ℕ (abs-ℤ ((s *ℤ x) -ℤ (t *ℤ y)))
          by ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K)
        ＝ (s *ℤ x) -ℤ (t *ℤ y)
          by int-abs-is-nonnegative-ℤ ((s *ℤ x) -ℤ (t *ℤ y)) pos
        ＝ (s *ℤ x) +ℤ ((neg-ℤ t) *ℤ y)
          by ap ((s *ℤ x) +ℤ_) (inv (left-negative-law-mul-ℤ t y)))

  pr1 (sx-ty-nonneg-case-split (inr neg)) = neg-ℤ s
  pr1 (pr2 (sx-ty-nonneg-case-split (inr neg))) = t
  pr2 (pr2 (sx-ty-nonneg-case-split (inr neg))) =
    inv
      ( equational-reasoning
          gcd-ℤ x y
          ＝ int-ℕ (abs-ℤ ((s *ℤ x) -ℤ (t *ℤ y)))
            by ap int-ℕ (bezouts-lemma-refactor-hypotheses x y H K)
          ＝ int-ℕ (abs-ℤ (neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y))))
            by ap (int-ℕ) (inv (abs-neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y))))
          ＝ neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y))
            by
              int-abs-is-nonnegative-ℤ
                ( neg-ℤ ((s *ℤ x) -ℤ (t *ℤ y)))
                ( neg)
          ＝ (neg-ℤ (s *ℤ x)) +ℤ (neg-ℤ (neg-ℤ (t *ℤ y)))
            by distributive-neg-add-ℤ (s *ℤ x) (neg-ℤ (t *ℤ y))
          ＝ ((neg-ℤ s) *ℤ x) +ℤ (neg-ℤ (neg-ℤ (t *ℤ y)))
            by ap (_+ℤ (neg-ℤ (neg-ℤ (t *ℤ y))))
              (inv (left-negative-law-mul-ℤ s x))
          ＝ ((neg-ℤ s) *ℤ x) +ℤ (t *ℤ y)
            by ap (((neg-ℤ s) *ℤ x) +ℤ_) (neg-neg-ℤ (t *ℤ y)))

bezouts-lemma-ℤ :
  (x y : ℤ) → Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
bezouts-lemma-ℤ (inl x) (inl y) = pair (neg-ℤ s) (pair (neg-ℤ t) eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            ( (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y)))) ＝
            ( gcd-ℤ (inr (inr x)) (inr (inr y)))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    ((neg-ℤ s) *ℤ (inl x)) +ℤ ((neg-ℤ t) *ℤ (inl y)) ＝
    gcd-ℤ (inl x) (inl y)
  eqn =
    equational-reasoning
      ( (neg-ℤ s) *ℤ (neg-ℤ (inr (inr x)))) +ℤ
      ( (neg-ℤ t) *ℤ (neg-ℤ (inr (inr y))))
      ＝ (s *ℤ (inr (inr x))) +ℤ ((neg-ℤ t) *ℤ (neg-ℤ (inr (inr y))))
        by
          ( ap
            ( _+ℤ ((neg-ℤ t) *ℤ (neg-ℤ (inr (inr y)))))
            ( double-negative-law-mul-ℤ s (inr (inr x))))
      ＝ (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y)))
        by
          ( ap
            ( (s *ℤ (inr (inr x))) +ℤ_)
            ( double-negative-law-mul-ℤ t (inr (inr y))))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inl x) (inr (inr y))
        by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x)))
      ＝ gcd-ℤ (inl x) (inl y)
        by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y)))
bezouts-lemma-ℤ (inl x) (inr (inl star)) = pair neg-one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    (neg-one-ℤ *ℤ (inl x)) +ℤ (one-ℤ *ℤ (inr (inl star))) ＝
    gcd-ℤ (inl x) (inr (inl star))
  eqn =
    equational-reasoning
      (neg-one-ℤ *ℤ (inl x)) +ℤ (one-ℤ *ℤ (inr (inl star)))
      ＝ (inr (inr x)) +ℤ (one-ℤ *ℤ (inr (inl star)))
        by
          ap
            ( _+ℤ (one-ℤ *ℤ (inr (inl star))))
            ( left-neg-unit-law-mul-ℤ (inl x))
      ＝ (inr (inr x)) +ℤ zero-ℤ
        by ap ((inr (inr x)) +ℤ_) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inl x))
        by right-unit-law-add-ℤ (inr (inr x))
      ＝ gcd-ℤ (inl x) zero-ℤ
        by inv (is-id-is-gcd-zero-ℤ' {inl x} {gcd-ℤ (inl x) zero-ℤ} refl)
bezouts-lemma-ℤ (inl x) (inr (inr y)) = pair (neg-ℤ s) (pair t eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y))) ＝
            gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    ((neg-ℤ s) *ℤ (inl x)) +ℤ (t *ℤ (inr (inr y))) ＝
    gcd-ℤ (inl x) (inr (inr y))
  eqn =
    equational-reasoning
      ((neg-ℤ s) *ℤ (neg-ℤ (inr (inr x)))) +ℤ (t *ℤ (inr (inr y)))
      ＝ (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y)))
        by ap (_+ℤ (t *ℤ (inr (inr y))))
          (double-negative-law-mul-ℤ s (inr (inr x)))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inl x) (inr (inr y))
        by ap (λ M → (int-ℕ (gcd-ℕ M (succ-ℕ y)))) (abs-neg-ℤ (inr (inr x)))
bezouts-lemma-ℤ (inr (inl star)) (inl y) = pair one-ℤ (pair neg-one-ℤ eqn)
  where
  eqn :
    (one-ℤ *ℤ (inr (inl star))) +ℤ (neg-one-ℤ *ℤ (inl y)) ＝
    gcd-ℤ (inr (inl star)) (inl y)
  eqn =
    equational-reasoning
      (one-ℤ *ℤ (inr (inl star))) +ℤ (neg-one-ℤ *ℤ (inl y))
      ＝ (one-ℤ *ℤ (inr (inl star))) +ℤ (inr (inr y))
        by
          ap
            ( (one-ℤ *ℤ (inr (inl star))) +ℤ_)
            ( left-neg-unit-law-mul-ℤ (inl y))
      ＝ zero-ℤ +ℤ (inr (inr y))
        by ap (_+ℤ (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inl y))
        by left-unit-law-add-ℤ (inr (inr y))
      ＝ gcd-ℤ zero-ℤ (inl y)
        by inv (is-id-is-gcd-zero-ℤ {inl y} {gcd-ℤ zero-ℤ (inl y)} refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    (one-ℤ *ℤ (inr (inl star))) +ℤ (one-ℤ *ℤ (inr (inl star))) ＝
    gcd-ℤ zero-ℤ zero-ℤ
  eqn =
    equational-reasoning
      (one-ℤ *ℤ (inr (inl star))) +ℤ (one-ℤ *ℤ (inr (inl star)))
      ＝ zero-ℤ +ℤ (one-ℤ *ℤ (inr (inl star)))
        by
          ap
            ( _+ℤ (one-ℤ *ℤ (inr (inl star))))
            ( right-zero-law-mul-ℤ one-ℤ)
      ＝ zero-ℤ +ℤ zero-ℤ
        by ap (zero-ℤ +ℤ_) (right-zero-law-mul-ℤ one-ℤ)
      ＝ gcd-ℤ zero-ℤ zero-ℤ
        by inv (is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl)
bezouts-lemma-ℤ (inr (inl star)) (inr (inr y)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    (one-ℤ *ℤ (inr (inl star))) +ℤ (one-ℤ *ℤ (inr (inr y))) ＝
    gcd-ℤ (inr (inl star)) (inr (inr y))
  eqn =
    equational-reasoning
      (one-ℤ *ℤ (inr (inl star))) +ℤ (one-ℤ *ℤ (inr (inr y)))
      ＝ (one-ℤ *ℤ (inr (inl star))) +ℤ (inr (inr y))
        by ap
          ( (one-ℤ *ℤ (inr (inl star))) +ℤ_)
          ( inv (left-unit-law-mul-ℤ (inr (inr y))))
      ＝ zero-ℤ +ℤ (inr (inr y))
        by ap (_+ℤ (inr (inr y))) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inr (inr y)))
        by left-unit-law-add-ℤ (inr (inr y))
      ＝ gcd-ℤ zero-ℤ (inr (inr y))
        by
          inv
            ( is-id-is-gcd-zero-ℤ
              { inr (inr y)}
              { gcd-ℤ zero-ℤ (inr (inr y))}
              ( refl))
bezouts-lemma-ℤ (inr (inr x)) (inl y) = pair s (pair (neg-ℤ t) eqn)
  where
  pos-bezout :
    Σ ( ℤ)
      ( λ s →
        Σ ( ℤ)
          ( λ t →
            (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y))) ＝
            gcd-ℤ (inr (inr x)) (inr (inr y))))
  pos-bezout = bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
  s : ℤ
  s = pr1 (pos-bezout)
  t : ℤ
  t = pr1 (pr2 (pos-bezout))
  eqn :
    (s *ℤ (inr (inr x))) +ℤ ((neg-ℤ t) *ℤ (inl y)) ＝
    gcd-ℤ (inr (inr x)) (inl y)
  eqn =
    equational-reasoning
      (s *ℤ (inr (inr x))) +ℤ ((neg-ℤ t) *ℤ (neg-ℤ (inr (inr y))))
      ＝ (s *ℤ (inr (inr x))) +ℤ (t *ℤ (inr (inr y)))
        by ap ((s *ℤ (inr (inr x))) +ℤ_)
          (double-negative-law-mul-ℤ t (inr (inr y)))
      ＝ gcd-ℤ (inr (inr x)) (inr (inr y))
        by pr2 (pr2 (pos-bezout))
      ＝ gcd-ℤ (inr (inr x)) (inl y)
        by ap (λ M → (int-ℕ (gcd-ℕ (succ-ℕ x) M))) (abs-neg-ℤ (inr (inr y)))
bezouts-lemma-ℤ (inr (inr x)) (inr (inl star)) = pair one-ℤ (pair one-ℤ eqn)
  where
  eqn :
    (one-ℤ *ℤ (inr (inr x))) +ℤ (one-ℤ *ℤ (inr (inl star))) ＝
    gcd-ℤ (inr (inr x)) (inr (inl star))
  eqn =
    equational-reasoning
      (one-ℤ *ℤ (inr (inr x))) +ℤ (one-ℤ *ℤ (inr (inl star)))
      ＝ (inr (inr x)) +ℤ (one-ℤ *ℤ (inr (inl star)))
        by
          ap
            ( _+ℤ (one-ℤ *ℤ (inr (inl star))))
            ( left-unit-law-mul-ℤ (inr (inr x)))
      ＝ (inr (inr x)) +ℤ zero-ℤ
        by ap ((inr (inr x)) +ℤ_) (right-zero-law-mul-ℤ one-ℤ)
      ＝ int-ℕ (abs-ℤ (inr (inr x)))
        by right-unit-law-add-ℤ (inr (inr x))
      ＝ gcd-ℤ (inr (inr x)) zero-ℤ
        by
          inv
            ( is-id-is-gcd-zero-ℤ'
              { inr (inr x)}
              { gcd-ℤ (inr (inr x)) zero-ℤ}
              ( refl))
bezouts-lemma-ℤ (inr (inr x)) (inr (inr y)) =
  bezouts-lemma-pos-ints (inr (inr x)) (inr (inr y)) star star
```

Now that Bezout's Lemma has been established, we establish a few corollaries of
Bezout.

### If `x | y z` and `gcd-Z x y ＝ 1`, then `x | z`

```agda
div-right-factor-coprime-ℤ :
  (x y z : ℤ) → (div-ℤ x (y *ℤ z)) → (gcd-ℤ x y ＝ one-ℤ) → div-ℤ x z
div-right-factor-coprime-ℤ x y z H K = pair ((s *ℤ z) +ℤ (t *ℤ k)) eqn
  where
  bezout-triple :
    Σ ℤ (λ s → Σ ℤ (λ t → (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y))
  bezout-triple = bezouts-lemma-ℤ x y
  s : ℤ
  s = pr1 bezout-triple
  t : ℤ
  t = pr1 (pr2 bezout-triple)
  bezout-eqn : (s *ℤ x) +ℤ (t *ℤ y) ＝ gcd-ℤ x y
  bezout-eqn = pr2 (pr2 bezout-triple)
  k : ℤ
  k = pr1 H
  div-yz : k *ℤ x ＝ y *ℤ z
  div-yz = pr2 H
  eqn : ((s *ℤ z) +ℤ (t *ℤ k)) *ℤ x ＝ z
  eqn =
    equational-reasoning
      ((s *ℤ z) +ℤ (t *ℤ k)) *ℤ x
      ＝ ((s *ℤ z) *ℤ x) +ℤ ((t *ℤ k) *ℤ x)
        by right-distributive-mul-add-ℤ (s *ℤ z) (t *ℤ k) x
      ＝ ((s *ℤ x) *ℤ z) +ℤ ((t *ℤ k) *ℤ x)
        by ap (_+ℤ ((t *ℤ k) *ℤ x))
        ( equational-reasoning
            (s *ℤ z) *ℤ x
            ＝ s *ℤ (z *ℤ x)
              by associative-mul-ℤ s z x
            ＝ s *ℤ (x *ℤ z)
              by ap (s *ℤ_) (commutative-mul-ℤ z x)
            ＝ (s *ℤ x) *ℤ z
              by inv (associative-mul-ℤ s x z))
      ＝ ((s *ℤ x) *ℤ z) +ℤ ((t *ℤ y) *ℤ z)
        by ap (((s *ℤ x) *ℤ z) +ℤ_)
    ( equational-reasoning
        (t *ℤ k) *ℤ x
        ＝ t *ℤ (k *ℤ x)
          by associative-mul-ℤ t k x
        ＝ t *ℤ (y *ℤ z)
          by ap (t *ℤ_) div-yz
        ＝ (t *ℤ y) *ℤ z
          by inv (associative-mul-ℤ t y z))
    ＝ ((s *ℤ x) +ℤ (t *ℤ y)) *ℤ z
      by inv (right-distributive-mul-add-ℤ (s *ℤ x) (t *ℤ y) z)
    ＝ one-ℤ *ℤ z
      by ap (_*ℤ z) (bezout-eqn ∙ K)
    ＝ z
      by left-unit-law-mul-ℤ z

div-right-factor-coprime-ℕ :
  (x y z : ℕ) → (div-ℕ x (y *ℕ z)) → (gcd-ℕ x y ＝ 1) → div-ℕ x z
div-right-factor-coprime-ℕ x y z H K =
  div-div-int-ℕ
    ( div-right-factor-coprime-ℤ
      ( int-ℕ x)
      ( int-ℕ y)
      ( int-ℕ z)
        ( tr (div-ℤ (int-ℕ x)) (inv (mul-int-ℕ y z)) (div-int-div-ℕ H))
      ( eq-gcd-gcd-int-ℕ x y ∙ ap int-ℕ K))
```

## References

{{#bibliography}}
