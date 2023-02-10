{-

This file contains:

- Properties of cardinality
- Preordering of cardinalities

-}
{-# OPTIONS --safe #-}
module Cubical.Data.Cardinal.Properties where

open import Cubical.HITs.SetTruncation as ∥₂
open import Cubical.Data.Cardinal.Base

open import Cubical.Algebra.CommSemiring
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Preorder.Base
open import Cubical.Relation.Binary.Order.Properties

private
  variable
    ℓ : Level

-- Cardinality is a commutative semiring
module _ where
  private
    +Assoc : (A B C : Card {ℓ}) → A + (B + C) ≡ (A + B) + C
    +Assoc = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                      λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                                  (sym (isoToPath ⊎-assoc-Iso)))

    ·Assoc : (A B C : Card {ℓ}) → A · (B · C) ≡ (A · B) · C
    ·Assoc = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                      λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                                  (sym (isoToPath Σ-assoc-Iso)))

    +Semigroup : IsSemigroup {ℓ-suc ℓ} _+_
    +Semigroup = issemigroup isSetCard
                             +Assoc

    ·Semigroup : IsSemigroup {ℓ-suc ℓ} _·_
    ·Semigroup = issemigroup isSetCard
                             ·Assoc

    +IdR𝟘 : (A : Card {ℓ}) → A + 𝟘 ≡ A
    +IdR𝟘 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                    λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                            (isoToPath ⊎-IdR-⊥*-Iso))

    +IdL𝟘 : (A : Card {ℓ}) → 𝟘 + A ≡ A
    +IdL𝟘 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                    λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                            (isoToPath ⊎-IdL-⊥*-Iso))

    ·IdR𝟙 : (A : Card {ℓ}) → A · 𝟙 ≡ A
    ·IdR𝟙 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                    λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                            (isoToPath rUnit*×Iso))

    ·IdL𝟙 : (A : Card {ℓ}) → 𝟙 · A ≡ A
    ·IdL𝟙 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                    λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                            (isoToPath lUnit*×Iso))

    +Monoid : IsMonoid {ℓ-suc ℓ} 𝟘 _+_
    +Monoid = ismonoid +Semigroup
                       +IdR𝟘
                       +IdL𝟘

    ·Monoid : IsMonoid {ℓ-suc ℓ} 𝟙 _·_
    ·Monoid = ismonoid ·Semigroup
                       ·IdR𝟙
                       ·IdL𝟙

    +Comm : (A B : Card {ℓ}) → (A + B) ≡ (B + A)
    +Comm = ∥₂.elim2 (λ _ _ → isProp→isSet (isSetCard _ _))
                     λ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath ⊎-swap-Iso))

    ·Comm : (A B : Card {ℓ}) → (A · B) ≡ (B · A)
    ·Comm = ∥₂.elim2 (λ _ _ → isProp→isSet (isSetCard _ _))
                     λ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath Σ-swap-Iso))

    +CommMonoid : IsCommMonoid {ℓ-suc ℓ} 𝟘 _+_
    +CommMonoid = iscommmonoid +Monoid
                               +Comm

    ·CommMonoid : IsCommMonoid {ℓ-suc ℓ} 𝟙 _·_
    ·CommMonoid = iscommmonoid ·Monoid
                               ·Comm

    ·LDist+ : (A B C : Card {ℓ}) → A · (B + C) ≡ (A · B) + (A · C)
    ·LDist+ = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                       λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                                   (isoToPath ×DistL⊎Iso))

    AnnihilL : (A : Card {ℓ}) → 𝟘 · A ≡ 𝟘
    AnnihilL = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                       λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath (ΣEmpty*Iso λ _ → _)))

  isCardCommSemiring : IsCommSemiring {ℓ-suc ℓ} 𝟘 𝟙 _+_ _·_
  isCardCommSemiring = iscommsemiring +CommMonoid
                                      ·CommMonoid
                                      ·LDist+
                                      AnnihilL

-- Exponentiation is also well-behaved

^AnnihilR𝟘 : (A : Card {ℓ}) → A ^ 𝟘 ≡ 𝟙
^AnnihilR𝟘 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
             λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                            (isoToPath (iso⊥ _)))
           where iso⊥ : ∀ A → Iso (⊥* → A) Unit*
                 Iso.fun (iso⊥ A) _        = tt*
                 Iso.inv (iso⊥ A) _        ()
                 Iso.rightInv (iso⊥ A) _   = refl
                 Iso.leftInv  (iso⊥ A) _ i ()

^IdR𝟙 : (A : Card {ℓ}) → A ^ 𝟙 ≡ A
^IdR𝟙 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath (iso⊤ _)))
        where iso⊤ : ∀ A → Iso (Unit* → A) A
              Iso.fun (iso⊤ _) f      = f tt*
              Iso.inv (iso⊤ _) a _    = a
              Iso.rightInv (iso⊤ _) _ = refl
              Iso.leftInv  (iso⊤ _) _ = refl

^AnnihilL𝟙 : (A : Card {ℓ}) → 𝟙 ^ A ≡ 𝟙
^AnnihilL𝟙 = ∥₂.elim (λ _ → isProp→isSet (isSetCard _ _))
                     λ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                             (isoToPath (iso⊤ _)))
             where iso⊤ : ∀ A → Iso (A → Unit*) Unit*
                   Iso.fun (iso⊤ _) _      = tt*
                   Iso.inv (iso⊤ _) _ _    = tt*
                   Iso.rightInv (iso⊤ _) _ = refl
                   Iso.leftInv  (iso⊤ _) _ = refl

^LDist+ : (A B C : Card {ℓ}) → A ^ (B + C) ≡ (A ^ B) · (A ^ C)
^LDist+ = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                   λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath Π⊎Iso))

^Assoc· : (A B C : Card {ℓ}) → A ^ (B · C) ≡ (A ^ B) ^ C
^Assoc· = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                   λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath (is _ _ _)))
          where is : ∀ A B C → Iso (B × C → A) (C → B → A)
                is A B C = (B × C → A) Iso⟨ domIso Σ-swap-Iso ⟩
                           (C × B → A) Iso⟨ curryIso ⟩
                           (C → B → A) ∎Iso

^RDist· : (A B C : Card {ℓ}) → (A · B) ^ C ≡ (A ^ C) · (B ^ C)
^RDist· = ∥₂.elim3 (λ _ _ _ → isProp→isSet (isSetCard _ _))
                   λ _ _ _ → cong ∣_∣₂ (Σ≡Prop (λ _ → isPropIsSet)
                                               (isoToPath Σ-Π-Iso))


-- With basic arithmetic done, we can now define an ordering over cardinals
module _ where
  private
    _≲'_ : Card {ℓ} → Card {ℓ} → hProp ℓ
    _≲'_ = ∥₂.rec2 isSetHProp λ (A , _) (B , _) → ∥ A ↪ B ∥₁ , isPropPropTrunc

  _≲_ : Rel (Card {ℓ}) (Card {ℓ}) ℓ
  A ≲ B = ⟨ A ≲' B ⟩

  isPreorder≲ : IsPreorder {ℓ-suc ℓ} _≲_
  isPreorder≲
    = ispreorder isSetCard prop reflexive transitive
                 where prop : BinaryRelation.isPropValued _≲_
                       prop a b = str (a ≲' b)

                       reflexive : BinaryRelation.isRefl _≲_
                       reflexive = ∥₂.elim (λ A → isProp→isSet (prop A A))
                                           (λ (A , _) → ∣ id↪ A ∣₁)

                       transitive : BinaryRelation.isTrans _≲_
                       transitive = ∥₂.elim3 (λ x _ z → isSetΠ2
                                                      λ _ _ → isProp→isSet
                                                              (prop x z))
                                             (λ (A , _) (B , _) (C , _)
                                              → ∥₁.map2 λ A↪B B↪C
                                                        → compEmbedding
                                                          B↪C
                                                          A↪B)

isLeast𝟘 : ∀{ℓ} → isLeast isPreorder≲ (Card {ℓ} , id↪ (Card {ℓ})) (𝟘 {ℓ})
isLeast𝟘 = ∥₂.elim (λ x → isProp→isSet (IsPreorder.is-prop-valued
                                       isPreorder≲ 𝟘 x))
                   (λ _ → ∣ ⊥.rec* , (λ ()) ∣₁)

-- Our arithmetic behaves as expected over our preordering
+Monotone≲ : (A B C D : Card {ℓ}) → A ≲ C → B ≲ D → (A + B) ≲ (C + D)
+Monotone≲
  = ∥₂.elim4 (λ w x y z → isSetΠ2 λ _ _ → isProp→isSet (IsPreorder.is-prop-valued
                                                       isPreorder≲
                                                       (w + x)
                                                       (y + z)))
              λ (A , _) (B , _) (C , _) (D , _)
              → ∥₁.map2 λ A↪C B↪D → ⊎Monotone↪ A↪C B↪D

·Monotone≲ : (A B C D : Card {ℓ}) → A ≲ C → B ≲ D → (A · B) ≲ (C · D)
·Monotone≲
  = ∥₂.elim4 (λ w x y z → isSetΠ2 λ _ _ → isProp→isSet (IsPreorder.is-prop-valued
                                                       isPreorder≲
                                                       (w · x)
                                                       (y · z)))
              λ (A , _) (B , _) (C , _) (D , _)
              → ∥₁.map2 λ A↪C B↪D → ×Monotone↪ A↪C B↪D
