# Permutations

```agda
{-# OPTIONS --without-K --exact-split --experimental-lossy-unification #-}

module finite-group-theory.permutations where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-two-ℕ; add-Fin; mod-succ-add-ℕ)

open import finite-group-theory.transpositions using
  ( correct-Fin-succ-Fin-transposition-list; Fin-succ-Fin-transposition;
    left-computation-standard-transposition; map-transposition;
    is-fixed-point-standard-transposition; permutation-list-transpositions;
    right-computation-standard-transposition; transposition; is-transposition-permutation-Prop;
    is-transposition-permutation; transposition-conjugation-equiv;
    correct-transposition-conjugation-equiv-list)
open import finite-group-theory.orbits-permutations using
  ( sign-list-transpositions-count; sign-permutation-orbit)

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr; center; eq-is-contr)
open import foundation.coproduct-types using
  ( coprod; inl; inr; is-injective-inl; is-prop-coprod; neq-inr-inl;
    neq-inl-inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-empty; is-prop-is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop;
    is-prop-type-decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_)
open import foundation.empty-types using (empty; ex-falso; is-prop-empty)
open import foundation.equality-dependent-pair-types using
  ( eq-pair-Σ; pair-eq-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; htpy-equiv; id-equiv; inv-equiv; is-emb-is-equiv;
    is-equiv; is-equiv-has-inverse; left-inverse-law-equiv;
    right-inverse-law-equiv; map-equiv; map-inv-equiv; htpy-eq-equiv)
open import foundation.equivalences-maybe using
  ( extend-equiv-Maybe; comp-extend-equiv-Maybe;
    computation-inv-extend-equiv-Maybe)
open import foundation.functions using (_∘_; id)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functoriality-coproduct-types using
  ( id-map-coprod; map-coprod)
open import foundation.homotopies using (_~_; comp-htpy; refl-htpy; inv-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap)
open import foundation.involutions using (is-involution; is-equiv-is-involution)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.iterating-functions using (iterate)
open import foundation.iterating-involutions using (iterate-involution)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop;
    unit-trunc-Prop; type-trunc-Prop; trunc-Prop)
open import foundation.propositions using (eq-is-prop; is-prop)
open import foundation.sets using (is-set-type-Set; Id-Prop)
open import foundation.type-arithmetic-empty-type using
  ( inv-right-unit-law-coprod-is-empty; map-right-absorption-prod)
open import foundation.truncated-types using (is-trunc-Prop; is-trunc-Π)
open import foundation.truncation-levels using (neg-two-𝕋; zero-𝕋)
open import foundation.unit-type using (star; unit)
open import foundation.universe-levels using (Level; UU; lzero; _⊔_; lsuc)

open import group-theory.groups using
  ( semigroup-Group; Group; type-Group; set-Group; is-set-type-Group; mul-Group; unit-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group; eq-htpy-hom-Group; is-set-type-hom-Group; preserves-unit-hom-Group;
    preserves-mul-hom-Group)
open import group-theory.semigroups using (set-Semigroup; mul-Semigroup)
open import group-theory.subgroups-generated-by-subsets-groups using
  ( is-generating-subset-Group; subset-subgroup-subset-Group; ev-formal-combination-subset-Group)
open import group-theory.symmetric-groups using (symmetric-Group)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( standard-2-Element-Decidable-Subtype; 2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-types using
  ( is-involution-aut-Fin-two-ℕ; ev-zero-aut-Fin-two-ℕ;
    is-equiv-ev-zero-aut-Fin-two-ℕ; aut-point-Fin-two-ℕ)
open import univalent-combinatorics.counting using
  ( count; equiv-count; inv-equiv-count; map-equiv-count; map-inv-equiv-count;
    number-of-elements-count)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using
  ( has-cardinality; UU-Fin-Level; type-UU-Fin-Level;
    has-cardinality-type-UU-Fin-Level; set-UU-Fin-Level)
open import univalent-combinatorics.lists using
  ( cons; list; fold-list; map-list; nil; length-list; concat-list;
    length-concat-list)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; nat-Fin; succ-Fin; equiv-succ-Fin; zero-Fin; Fin-Set)
```

## Properties

### Every permutation on `Fin n` can be described as a composite of transpositions

```agda
list-transpositions-permutation-Fin' :
  (n : ℕ) (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
  (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
  ( list
    ( Σ
      ( Fin (succ-ℕ n) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (P x))))))
list-transpositions-permutation-Fin' zero-ℕ f x p = nil
list-transpositions-permutation-Fin' (succ-ℕ n) f (inl x) p =
  cons
    ( t)
    ( map-list
      ( Fin-succ-Fin-transposition (succ-ℕ n))
      ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl))
  where
  t : ( Σ
    ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
    ( λ P →
      has-cardinality 2
        ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
  t = standard-2-Element-Decidable-Subtype
      ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
      { inr star}
      { inl x}
      ( neq-inr-inl)
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' =
    map-inv-equiv
      ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
      ( pair
        ( transposition t ∘e f)
        ( ( ap (λ y → map-transposition t y) p) ∙
          ( right-computation-standard-transposition
            ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
            { inr star}
            { inl x}
            ( neq-inr-inl))))
list-transpositions-permutation-Fin' (succ-ℕ n) f (inr star) p =
  map-list
    ( Fin-succ-Fin-transposition (succ-ℕ n))
    ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
  where
  f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
  f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

list-transpositions-permutation-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
  ( list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x))))))
list-transpositions-permutation-Fin zero-ℕ f = nil
list-transpositions-permutation-Fin (succ-ℕ n) f = list-transpositions-permutation-Fin' n f (map-equiv f (inr star)) refl

abstract
  retr-permutation-list-transpositions-Fin' : (n : ℕ) → (f : Fin (succ-ℕ n) ≃ Fin (succ-ℕ n)) →
    (x : Fin (succ-ℕ n)) → Id (map-equiv f (inr star)) x →
    (y z : Fin (succ-ℕ n)) → Id (map-equiv f y) z →
    Id
      ( map-equiv (permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) f)) y)
      ( map-equiv f y)
  retr-permutation-list-transpositions-Fin' zero-ℕ f (inr star) p (inr star) z q = inv p
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inl z) q =
    ap 
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inl y)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inl y)) ∙
        (ap
          ( λ g →
            map-equiv
              ( transposition t)
              ( map-equiv
                ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
                ( inl y)))
          { x =
            permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) _)}
          { y = F'} 
          ( eq-htpy-equiv
            ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
            ( (ap (map-equiv (transposition t)) lemma) ∙
              (lemma2 ∙ inv q))))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t =
      standard-2-Element-Decidable-Subtype
        ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
        { inr star}
        { inl x}
        ( neq-inr-inl)
    P :
      Σ ( Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n)))
        ( λ g → Id (map-equiv g (inr star)) (inr star))
    P =
      pair
        ( transposition t ∘e f)
        ( ( ap (λ y → map-transposition t y) p) ∙
          ( right-computation-standard-transposition
            ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
            { inr star}
            { inl x}
            ( neq-inr-inl)))
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
    F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
    lemma2 : Id
      (map-equiv
      (transposition t) (inl z))
      (inl z)
    lemma2 =
      is-fixed-point-standard-transposition
        ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
        { inr star}
        { inl x}
        ( neq-inr-inl)
        ( inl z)
        ( neq-inr-inl)
        ( λ r →
          neq-inr-inl
            ( is-injective-map-equiv f (p ∙ (r ∙ inv q))))
    lemma :
      Id ( map-equiv
           ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F'))
           ( inl y))
         ( inl z)
    lemma =
      ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
        ( ap (map-equiv (transposition t)) q ∙ lemma2)
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inl y) (inr star) q =
    ap 
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inl y)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inl y)) ∙
        (ap
          ( λ g →
            map-equiv
              ( transposition t)
              ( map-equiv
                ( pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) g))
                ( inl y)))
          { x =
            permutation-list-transpositions (list-transpositions-permutation-Fin (succ-ℕ n) _)}
          { y = F'} 
          ( eq-htpy-equiv
            ( λ w → retr-permutation-list-transpositions-Fin' n _ (map-equiv F' (inr star)) refl w (map-equiv F' w) refl)) ∙
          ( (ap (map-equiv (transposition t)) lemma) ∙
            ( (right-computation-standard-transposition
              ( has-decidable-equality-Fin (succ-ℕ (succ-ℕ n)))
              { inr star}
              { inl x}
              ( neq-inr-inl)) ∙
              ( inv q)))))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t = standard-2-Element-Decidable-Subtype (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl 
    P : Σ (Fin (succ-ℕ (succ-ℕ n)) ≃ Fin (succ-ℕ (succ-ℕ n))) (λ g → Id (map-equiv g (inr star)) (inr star))
    P = pair
      ( transposition t ∘e f)
      ( ( ap (λ y → map-transposition t y) p) ∙
        right-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl)
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
    F' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) P
    lemma : Id (map-equiv (pr1 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) (inl y)) (inl x)
    lemma =
      ( ap (λ e → map-equiv (pr1 (map-equiv e P)) (inl y)) (right-inverse-law-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))))) ∙
        ( ap (map-equiv (transposition t)) q ∙
          ( left-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl))
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inl x) p (inr star) z q =
    ap 
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inr star)) {y = pair (inl x) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inl x)))) ∙
      ( ap
        ( map-equiv (transposition t))
        ( correct-Fin-succ-Fin-transposition-list
          ( succ-ℕ n)
          ( list-transpositions-permutation-Fin' n _ (map-equiv F' (inr star)) refl)
          ( inr star)) ∙
        ( ap
          ( map-equiv (transposition t))
          ( pr2 (map-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) F')) ∙
          ( left-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl ∙
            inv p)))
    where
    t : ( Σ
      ( Fin (succ-ℕ (succ-ℕ n)) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ (succ-ℕ n))) (λ x → type-decidable-Prop (P x)))))
    t = standard-2-Element-Decidable-Subtype (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl 
    F' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
    F' =
      map-inv-equiv
        ( extend-equiv-Maybe (Fin-Set (succ-ℕ n)))
        ( pair
          ( transposition t ∘e f)
          ( ( ap (λ y → map-transposition t y) p) ∙
            right-computation-standard-transposition (has-decidable-equality-Fin (succ-ℕ (succ-ℕ n))) {inr star} {inl x} neq-inr-inl))
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inl z) q =
    ap 
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inl y)) {y = pair (inr star) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inr star)))) ∙
      ( ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
        ( inl y)) ∙
        ( ( ap inl (retr-permutation-list-transpositions-Fin' n f' (map-equiv f' (inr star)) refl y (map-equiv f' y) refl)) ∙
          ( computation-inv-extend-equiv-Maybe (Fin-Set (succ-ℕ n)) f p y)))
    where
    f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
    f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inl y) (inr star) q =
    ex-falso
      ( neq-inr-inl
        ( is-injective-map-equiv f (p ∙ inv q)))
  retr-permutation-list-transpositions-Fin' (succ-ℕ n) f (inr star) p (inr star) z q =
    ap 
      (λ w →
        map-equiv
          ( permutation-list-transpositions
            ( list-transpositions-permutation-Fin' (succ-ℕ n) f (pr1 w) (pr2 w)))
        ( inr star)) {y = pair (inr star) p}
      ( eq-pair-Σ p (eq-is-prop (is-set-type-Set (Fin-Set (succ-ℕ (succ-ℕ n))) (map-equiv f (inr star)) (inr star)))) ∙
      ( ( correct-Fin-succ-Fin-transposition-list
        ( succ-ℕ n)
        ( list-transpositions-permutation-Fin' n f' (map-equiv f' (inr star)) refl)
        ( inr star)) ∙
        ( inv p))
    where
    f' : (Fin (succ-ℕ n) ≃ Fin (succ-ℕ n))
    f' = map-inv-equiv (extend-equiv-Maybe (Fin-Set (succ-ℕ n))) (pair f p)

  retr-permutation-list-transpositions-Fin : (n : ℕ) → (f : Fin n ≃ Fin n) →
    htpy-equiv (permutation-list-transpositions (list-transpositions-permutation-Fin n f)) f
  retr-permutation-list-transpositions-Fin zero-ℕ f ()
  retr-permutation-list-transpositions-Fin (succ-ℕ n) f y =
    retr-permutation-list-transpositions-Fin' n f (map-equiv f (inr star)) refl y (map-equiv f y) refl
```

### Every permutation of a type equipped with a counting can be described as a product of transpositions.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (eX : count X) (f : X ≃ X)
  where

  list-transpositions-permutation-count :
    list
      ( Σ
        ( X → decidable-Prop l2)
        ( λ P →
          has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))
  list-transpositions-permutation-count =
    map-list
      ( transposition-conjugation-equiv (Fin (number-of-elements-count eX)) X (equiv-count eX))
      ( list-transpositions-permutation-Fin (number-of-elements-count eX) ((inv-equiv-count eX ∘e f) ∘e equiv-count eX))

  abstract
    retr-permutation-list-transpositions-count :
      htpy-equiv (permutation-list-transpositions list-transpositions-permutation-count) f
    retr-permutation-list-transpositions-count x =
      ( correct-transposition-conjugation-equiv-list
        ( Fin (number-of-elements-count eX))
        ( X)
        ( equiv-count eX)
        ( list-transpositions-permutation-Fin (number-of-elements-count eX) ((inv-equiv-count eX ∘e f) ∘e equiv-count eX))
        ( x)) ∙
        ( (ap
          ( map-equiv-count eX)
          ( retr-permutation-list-transpositions-Fin
            ( number-of-elements-count eX)
            ( (inv-equiv-count eX ∘e f) ∘e equiv-count eX)
            ( map-inv-equiv-count eX x))) ∙
          ( (htpy-eq-equiv (right-inverse-law-equiv (equiv-count eX)) (map-equiv ((f ∘e (equiv-count eX)) ∘e inv-equiv-count eX) x)) ∙
            ap (λ g → map-equiv (f ∘e g) x) (right-inverse-law-equiv (equiv-count eX))))
```

### For `X` finite, the symmetric group of `X` is generated by transpositions

```agda
module _
  {l1 l2 : Level} (n : ℕ) (X : UU-Fin-Level l1 n)
  where

  is-generated-transposition-symmetric-Fin-Level :
    is-generating-subset-Group
      ( symmetric-Group (set-UU-Fin-Level n X))
      ( is-transposition-permutation-Prop)
  is-generated-transposition-symmetric-Fin-Level f _ =
    apply-universal-property-trunc-Prop
      ( has-cardinality-type-UU-Fin-Level n X)
      ( subset-subgroup-subset-Group
        ( symmetric-Group (set-UU-Fin-Level n X))
        ( is-transposition-permutation-Prop)
        ( f))
      ( λ h →
        unit-trunc-Prop
          ( pair
            ( map-list
              ( λ x → pair (inr star) (pair (transposition x) (unit-trunc-Prop (pair x refl))))
              ( list-transpositions-permutation-count (type-UU-Fin-Level n X) (pair n h) f))
            ( ( lemma (list-transpositions-permutation-count (type-UU-Fin-Level n X) (pair n h) f)) ∙
              ( eq-htpy-equiv (retr-permutation-list-transpositions-count (type-UU-Fin-Level n X) (pair n h) f)))))
    where
    lemma : (l : list (2-Element-Decidable-Subtype l2 (type-UU-Fin-Level n X))) →
      Id
        ( ev-formal-combination-subset-Group
          ( symmetric-Group (set-UU-Fin-Level n X))
          ( is-transposition-permutation-Prop)
          ( map-list
            ( λ x →
              pair
                ( inr star)
                ( pair (transposition x) (unit-trunc-Prop (pair x refl))))
            ( l)))
        ( permutation-list-transpositions l)
    lemma nil = refl
    lemma (cons x l) = ap (λ g → (transposition x) ∘e g) (lemma l)
```

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) 
  where

  module _
    (f : (type-UU-Fin-Level n X) ≃ (type-UU-Fin-Level n X))
    where
    
    parity-transposition-permutation : UU (lsuc l)
    parity-transposition-permutation =
      Σ (Fin 2) (λ k →
        type-trunc-Prop
          (Σ
            ( list
              ( Σ ((type-UU-Fin-Level n X) → decidable-Prop l)
                ( λ P → has-cardinality 2 (Σ (type-UU-Fin-Level n X) (λ x → type-decidable-Prop (P x))))))
            ( λ li → Id k (mod-two-ℕ (length-list li)) × Id f (permutation-list-transpositions li))))

    abstract
      is-contr-parity-transposition-permutation : is-contr parity-transposition-permutation
      is-contr-parity-transposition-permutation =
        apply-universal-property-trunc-Prop
          ( has-cardinality-type-UU-Fin-Level n X)
          ( is-trunc-Prop neg-two-𝕋 parity-transposition-permutation)
          ( λ h →
            pair
              ( pair
                ( mod-two-ℕ (length-list (list-transposition-f h)))
                ( unit-trunc-Prop
                  ( pair (list-transposition-f h)
                    ( pair refl
                      ( inv
                        ( eq-htpy-equiv (retr-permutation-list-transpositions-count (type-UU-Fin-Level n X) (pair n h) f)))))))
              ( λ (pair k u) →
                eq-pair-Σ
                  ( apply-universal-property-trunc-Prop u
                    ( Id-Prop (Fin-Set 2) (mod-two-ℕ (length-list (list-transposition-f h))) k)
                    ( λ (pair li (pair q r)) →
                      is-injective-iterate-involution (mod-two-ℕ (length-list (list-transposition-f h))) k
                        ( sign-permutation-orbit n (pair (type-UU-Fin-Level n X) (unit-trunc-Prop h)) id-equiv)
                        ( inv
                          ( iterate-involution (succ-Fin 2) (is-involution-aut-Fin-two-ℕ (equiv-succ-Fin 2))
                            (length-list (list-transposition-f h))
                            (sign-permutation-orbit n (pair (type-UU-Fin-Level n X) (unit-trunc-Prop h)) id-equiv)) ∙
                          ( sign-list-transpositions-count (type-UU-Fin-Level n X) (pair n h) (list-transposition-f h) ∙
                            ( ap
                              ( sign-permutation-orbit n (pair (type-UU-Fin-Level n X) (unit-trunc-Prop h)))
                              { x = permutation-list-transpositions (list-transposition-f h)}
                              { y = permutation-list-transpositions li}
                              ( (eq-htpy-equiv (retr-permutation-list-transpositions-count
                                (type-UU-Fin-Level n X) (pair n h) f)) ∙ r) ∙
                              ( inv (sign-list-transpositions-count (type-UU-Fin-Level n X) (pair n h) li) ∙
                                ( (iterate-involution (succ-Fin 2) (is-involution-aut-Fin-two-ℕ (equiv-succ-Fin 2)) (length-list li)
                                  ( sign-permutation-orbit n (pair (type-UU-Fin-Level n X) (unit-trunc-Prop h)) id-equiv)) ∙
                                  ( ap
                                    ( λ k → iterate (nat-Fin 2 k) (succ-Fin 2)
                                      ( sign-permutation-orbit n (pair (type-UU-Fin-Level n X) (unit-trunc-Prop h)) id-equiv))
                                    ( inv q)))))))))
                  ( eq-is-prop is-prop-type-trunc-Prop)))
        where
        list-transposition-f : (h : Fin n ≃ (type-UU-Fin-Level n X)) →
          list
            (Σ (type-UU-Fin-Level n X → decidable-Prop l)
            (λ P → has-cardinality 2 (Σ (type-UU-Fin-Level n X) (λ x → type-decidable-Prop (P x)))))
        list-transposition-f h = list-transpositions-permutation-count (type-UU-Fin-Level n X) (pair n h) f
        is-injective-iterate-involution : (k k' x : Fin 2) →
          Id (iterate (nat-Fin 2 k) (succ-Fin 2) x) (iterate (nat-Fin 2 k') (succ-Fin 2) x) → Id k k'
        is-injective-iterate-involution (inl (inr star)) (inl (inr star)) x p = refl
        is-injective-iterate-involution (inl (inr star)) (inr star) (inl (inr star)) p = ex-falso (neq-inl-inr p)
        is-injective-iterate-involution (inl (inr star)) (inr star) (inr star) p = ex-falso (neq-inr-inl p)
        is-injective-iterate-involution (inr star) (inl (inr star)) (inl (inr star)) p = ex-falso (neq-inr-inl p)
        is-injective-iterate-involution (inr star) (inl (inr star)) (inr star) p = ex-falso (neq-inl-inr p)
        is-injective-iterate-involution (inr star) (inr star) x p = refl
```
