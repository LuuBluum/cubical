{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Instances.Embedding where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Order.Proset.Properties
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties

private
  variable
    ℓ ℓ' : Level

-- The collection of embeddings on a type happens to form a complete lattice

-- First, we show that it's a poset
isPoset⊆ₑ : {A : Type ℓ} → IsPoset {A = Embedding A ℓ'} _⊆ₑ_
isPoset⊆ₑ = isposet isSetEmbedding
                    isProp⊆ₑ
                    isRefl⊆ₑ
                    isTrans⊆ₑ
                    isAntisym⊆ₑ

EmbeddingPoset : (A : Type ℓ) (ℓ' : Level) → Poset _ _
EmbeddingPoset A ℓ'
  = poset (Embedding A ℓ') _⊆ₑ_ (isPoset⊆ₑ)

-- Then we describe it as both a lattice and a complete lattice
isMeet∩ₑ : {A : Type ℓ}
           (X Y : Embedding A ℓ)
         → isMeet (isPoset→isProset isPoset⊆ₑ) X Y (X ∩ₑ Y)
isMeet∩ₑ X Y Z = propBiimpl→Equiv (isProp⊆ₑ Z (X ∩ₑ Y))
                                  (isProp× (isProp⊆ₑ Z X)
                                  (isProp⊆ₑ Z Y))
                                  (λ Z⊆X∩Y →
                                    (λ x x∈Z →
                                       subst (_∈ₑ X)
                                             (Z⊆X∩Y x x∈Z .snd)
                                             (Z⊆X∩Y x x∈Z .fst .snd .fst)) ,
                                    (λ x x∈Z →
                                       subst (_∈ₑ Y)
                                             (Z⊆X∩Y x x∈Z .snd)
                                             (Z⊆X∩Y x x∈Z .fst .snd .snd)))
                                   λ { (Z⊆X , Z⊆Y) x x∈Z →
                                       (x , ((Z⊆X x x∈Z) ,
                                             (Z⊆Y x x∈Z))) , refl }

isGreatestEmbeddingPosetTotal : {A : Type ℓ}
                              → isGreatest (isPoset→isProset isPoset⊆ₑ)
                                           (Embedding A ℓ , id↪ (Embedding A ℓ))
                                           (A , (id↪ A))
isGreatestEmbeddingPosetTotal _ x _
  = x , refl

isJoin∪ₑ : {A : Type ℓ}
           (X Y : Embedding A ℓ)
         → isJoin (isPoset→isProset isPoset⊆ₑ) X Y (X ∪ₑ Y)
isJoin∪ₑ X Y Z
  = propBiimpl→Equiv (isProp⊆ₑ (X ∪ₑ Y) Z)
                     (isProp× (isProp⊆ₑ X Z)
                              (isProp⊆ₑ Y Z))
                     (λ X∪Y⊆Z →
                          (λ x x∈X → X∪Y⊆Z x ((x , ∣ inl x∈X ∣₁) , refl)) ,
                          (λ x x∈Y → X∪Y⊆Z x ((x , ∣ inr x∈Y ∣₁) , refl)))
                      λ { (X⊆Z , Y⊆Z) x x∈X∪Y →
                          ∥₁.rec (isProp∈ₑ x Z)
                                 (⊎.rec (λ a∈X → subst (_∈ₑ Z)
                                                       (x∈X∪Y .snd)
                                                       (X⊆Z _ a∈X))
                                        (λ a∈Y → subst (_∈ₑ Z)
                                                       (x∈X∪Y .snd)
                                                       (Y⊆Z _ a∈Y)))
                                 (x∈X∪Y .fst .snd) }

isLeast∅ : {A : Type ℓ}
         → isLeast (isPoset→isProset isPoset⊆ₑ) (Embedding A ℓ , id↪ (Embedding A ℓ)) ((Σ[ x ∈ A ] ⊥) , EmbeddingΣProp λ _ → isProp⊥)
isLeast∅ _ _ ((_ , ()) , _)

isInfimum⋂ₑ : {A : Type ℓ}
               {I : Type ℓ}
               (P : I → Embedding A ℓ)
             → isInfimum (isPoset→isProset isPoset⊆ₑ) P (⋂ₑ P)
fst (isInfimum⋂ₑ P) i y ((a , ∀i) , a≡y) = subst (_∈ₑ P i) a≡y (∀i i)
snd (isInfimum⋂ₑ P) (X , lwr) y y∈X = (y , λ i → lwr i y y∈X) , refl

isSupremum⋃ₑ : {A : Type ℓ}
               {I : Type ℓ}
               (P : I → Embedding A ℓ)
              → isSupremum (isPoset→isProset isPoset⊆ₑ) P (⋃ₑ P)
fst (isSupremum⋃ₑ P) i y y∈Pi = (y , ∣ i , y∈Pi ∣₁) , refl
snd (isSupremum⋃ₑ P) (X , upr) y ((a , ∃i) , a≡y)
  = ∥₁.rec (isProp∈ₑ y X) (λ (i , a∈Pi) → upr i y (subst (_∈ₑ P i) a≡y a∈Pi)) ∃i
