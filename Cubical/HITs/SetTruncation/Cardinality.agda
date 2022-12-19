{-

This file contains:

- Treatment of set truncation as cardinality

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SetTruncation.Cardinality where

open import Cubical.HITs.SetTruncation.Base
open import Cubical.HITs.SetTruncation.Properties
  renaming (rec to ∥₂-rec ; rec2 to ∥₂-rec2 ; elim to ∥₂-elim ; elim2 to ∥₂-elim2 ; elim3 to ∥₂-elim3)

open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Data.Empty
  renaming (rec* to ⊥-rec*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
  hiding (rec ; map)
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
  renaming (rec to ∥₁-rec ; rec2 to ∥₁-rec2 ; elim to ∥₁-elim ; map2 to ∥₁-map2) hiding (elim2 ; elim3 ; map)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order
open import Cubical.Relation.Nullary

private
  variable
    {ℓ ℓ'} : Level

-- First, we define a cardinal as the set truncation of Set
Card : Type (ℓ-suc ℓ)
Card {ℓ} = ∥ hSet ℓ ∥₂

-- Verify that it's a set
isSetCard : isSet (Card {ℓ})
isSetCard = squash₂

-- Set truncation of a set is its cardinality
card : hSet ℓ → Card {ℓ}
card = ∣_∣₂

-- Some special cardinalities
𝟘 : Card {ℓ}
𝟘 = card (⊥* , isProp→isSet isProp⊥*)

𝟙 : Card {ℓ}
𝟙 = card (Unit* , isSetUnit*)

-- Now we define some arithmetic
_+_ : Card {ℓ} → Card {ℓ} → Card {ℓ}
_+_ = ∥₂-rec2 isSetCard λ (A , isSetA) (B , isSetB) → card ((A ⊎ B) , (isSet⊎ isSetA isSetB))

_·_ : Card {ℓ} → Card {ℓ} → Card {ℓ}
_·_ = ∥₂-rec2 isSetCard λ (A , isSetA) (B , isSetB) → card ((A × B) , (isSet× isSetA isSetB))

-- Cardinality is a commutative semiring
module _ where
  private
    +Assoc : (A B C : Card {ℓ}) → A + (B + C) ≡ (A + B) + C
    +Assoc = ∥₂-elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _)) λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (sym (isoToPath ⊎-assoc-Iso)))

    ·Assoc : (A B C : Card {ℓ}) → A · (B · C) ≡ (A · B) · C
    ·Assoc = ∥₂-elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _)) λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (sym (isoToPath Σ-assoc-Iso)))

    +Semigroup : IsSemigroup {ℓ-suc ℓ} _+_
    +Semigroup = issemigroup isSetCard
                             +Assoc

    ·Semigroup : IsSemigroup {ℓ-suc ℓ} _·_
    ·Semigroup = issemigroup isSetCard
                             ·Assoc

    +IdR𝟘 : (A : Card {ℓ}) → A + 𝟘 ≡ A
    +IdR𝟘 = ∥₂-elim (λ _ → isProp→isSet (isSetCard _ _)) λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath ⊎-IdR-⊥*-Iso))

    +IdL𝟘 : (A : Card {ℓ}) → 𝟘 + A ≡ A
    +IdL𝟘 = ∥₂-elim (λ _ → isProp→isSet (isSetCard _ _)) λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath ⊎-IdL-⊥*-Iso))

    ·IdR𝟙 : (A : Card {ℓ}) → A · 𝟙 ≡ A
    ·IdR𝟙 = ∥₂-elim (λ _ → isProp→isSet (isSetCard _ _)) λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath rUnit*×Iso))

    ·IdL𝟙 : (A : Card {ℓ}) → 𝟙 · A ≡ A
    ·IdL𝟙 = ∥₂-elim (λ _ → isProp→isSet (isSetCard _ _)) λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath lUnit*×Iso))

    +Monoid : IsMonoid {ℓ-suc ℓ} 𝟘 _+_
    +Monoid = ismonoid +Semigroup
                       +IdR𝟘
                       +IdL𝟘

    ·Monoid : IsMonoid {ℓ-suc ℓ} 𝟙 _·_
    ·Monoid = ismonoid ·Semigroup
                       ·IdR𝟙
                       ·IdL𝟙

    +Comm : (A B : Card {ℓ}) → (A + B) ≡ (B + A)
    +Comm = ∥₂-elim2 (λ _ _ → isProp→isSet (isSetCard _ _)) λ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath ⊎-swap-Iso))

    ·Comm : (A B : Card {ℓ}) → (A · B) ≡ (B · A)
    ·Comm = ∥₂-elim2 (λ _ _ → isProp→isSet (isSetCard _ _)) λ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath Σ-swap-Iso))

    +CommMonoid : IsCommMonoid {ℓ-suc ℓ} 𝟘 _+_
    +CommMonoid = iscommmonoid +Monoid
                               +Comm

    ·CommMonoid : IsCommMonoid {ℓ-suc ℓ} 𝟙 _·_
    ·CommMonoid = iscommmonoid ·Monoid
                               ·Comm

    ·LDist+ : (A B C : Card {ℓ}) → A · (B + C) ≡ (A · B) + (A · C)
    ·LDist+ = ∥₂-elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _)) λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath ×DistL⊎Iso))

    AnnihilL : (A : Card {ℓ}) → 𝟘 · A ≡ 𝟘
    AnnihilL = ∥₂-elim (λ _ → isProp→isSet (isSetCard _ _)) λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet) (isoToPath (ΣEmpty*Iso λ _ → _)))

  isCardCommSemiring : IsCommSemiring {ℓ-suc ℓ} 𝟘 𝟙 _+_ _·_
  isCardCommSemiring = iscommsemiring +CommMonoid
                                      ·CommMonoid
                                      ·LDist+
                                      AnnihilL

-- With basic arithmetic done, we can now define an ordering over cardinals
module _ where
  private
    _≲'_ : Card {ℓ} → Card {ℓ} → hProp ℓ
    _≲'_ = ∥₂-rec2 isSetHProp λ (A , _) (B , _) → ∥ A ↪ B ∥₁ , isPropPropTrunc

  _≲_ : Rel (Card {ℓ}) (Card {ℓ}) ℓ
  A ≲ B = fst (A ≲' B)

  isPreorder≲ : IsPreorder {ℓ-suc ℓ} _≲_
  isPreorder≲ = ispreorder isSetCard
                           (λ A B → prop A B)
                           (λ A → ∥₂-elim (λ A → isProp→isSet (prop A A)) (λ (A , _) → ∣ id↪ A ∣₁) A)
                           λ A B C → ∥₂-elim3 {B = λ x y z → x ≲ y → y ≲ z → x ≲ z} (λ x y z → isSetΠ2 λ _ _ → isProp→isSet (prop x z)) (λ (A , _) (B , _) (C , _) → ∥₁-map2 λ A↪B B↪C → compEmbedding B↪C A↪B) A B C
              where prop : BinaryRelation.isPropValued _≲_
                    prop a b = snd (a ≲' b)

𝟘isLeast : ∀{ℓ} → isLeast _≲_ (λ _ → Unit* {ℓ}) (𝟘 {ℓ} , tt*)
𝟘isLeast {ℓ} (x , _) = ∥₂-elim {B = λ x → 𝟘 ≲ x} (λ x → isProp→isSet (IsPreorder.is-prop-valued isPreorder≲ 𝟘 x)) (λ (a , _) → ∣ ⊥-rec* , (λ ()) ∣₁) x
