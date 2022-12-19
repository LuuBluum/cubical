{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Preorder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary.Base

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsPreorder {A : Type ℓ} (_≲_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ispreorder

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≲_
    is-refl : isRefl _≲_
    is-trans : isTrans _≲_

unquoteDecl IsPreorderIsoΣ = declareRecordIsoΣ IsPreorderIsoΣ (quote IsPreorder)


record PreorderStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor preorderstr

  field
    _≲_     : A → A → Type ℓ'
    isPreorder : IsPreorder _≲_

  infixl 7 _≲_

  open IsPreorder isPreorder public

Preorder : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Preorder ℓ ℓ' = TypeWithStr ℓ (PreorderStr ℓ')

preorder : (A : Type ℓ) (_≲_ : A → A → Type ℓ') (h : IsPreorder _≲_) → Preorder ℓ ℓ'
preorder A _≲_ h = A , preorderstr _≲_ h

record IsPreorderEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PreorderStr ℓ₀' A) (e : A ≃ B) (N : PreorderStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   ispreorderequiv
  -- Shorter qualified names
  private
    module M = PreorderStr M
    module N = PreorderStr N

  field
    pres≲ : (x y : A) → x M.≲ y ≃ equivFun e x N.≲ equivFun e y


PreorderEquiv : (M : Preorder ℓ₀ ℓ₀') (M : Preorder ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
PreorderEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsPreorderEquiv (M .snd) e (N .snd)

isPropIsPreorder : {A : Type ℓ} (_≲_ : A → A → Type ℓ') → isProp (IsPreorder _≲_)
isPropIsPreorder _≲_ = isOfHLevelRetractFromIso 1 IsPreorderIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≲ → isProp×
                        (isPropΠ (λ _ → isPropValued≲ _ _))
                        (isPropΠ4 λ _ _ _ _ → isPropΠ λ _ → isPropValued≲ _ _))

𝒮ᴰ-Preorder : DUARel (𝒮-Univ ℓ) (PreorderStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Preorder =
  𝒮ᴰ-Record (𝒮-Univ _) IsPreorderEquiv
    (fields:
      data[ _≲_ ∣ autoDUARel _ _ ∣ pres≲ ]
      prop[ isPreorder ∣ (λ _ _ → isPropIsPreorder _) ])
    where
    open PreorderStr
    open IsPreorder
    open IsPreorderEquiv

PreorderPath : (M N : Preorder ℓ ℓ') → PreorderEquiv M N ≃ (M ≡ N)
PreorderPath = ∫ 𝒮ᴰ-Preorder .UARel.ua

-- an easier way of establishing an equivalence of preorders
module _ {P : Preorder ℓ₀ ℓ₀'} {S : Preorder ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = PreorderStr (P .snd)
    module S = PreorderStr (S .snd)

  module _ (isMon : ∀ x y → x P.≲ y → equivFun e x S.≲ equivFun e y)
           (isMonInv : ∀ x y → x S.≲ y → invEq e x P.≲ invEq e y) where
    open IsPreorderEquiv
    open IsPreorder

    makeIsPreorderEquiv : IsPreorderEquiv (P .snd) e (S .snd)
    pres≲ makeIsPreorderEquiv x y = propBiimpl→Equiv (P.isPreorder .is-prop-valued _ _)
                                                  (S.isPreorder .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≲ equivFun e y → x P.≲ y
      isMonInv' x y ex≲ey = transport (λ i → retEq e x i P.≲ retEq e y i) (isMonInv _ _ ex≲ey)


module PreorderReasoning (P' : Preorder ℓ ℓ') where
 private P = fst P'
 open PreorderStr (snd P')
 open IsPreorder

 _≲⟨_⟩_ : (x : P) {y z : P} → x ≲ y → y ≲ z → x ≲ z
 x ≲⟨ p ⟩ q = isPreorder .is-trans x _ _ p q

 _◾ : (x : P) → x ≲ x
 x ◾ = isPreorder .is-refl x

 infixr 0 _≲⟨_⟩_
 infix  1 _◾
