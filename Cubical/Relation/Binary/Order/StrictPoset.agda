{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.StrictPoset where

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
open import Cubical.Relation.Nullary.Properties

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsStrictPoset {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isstrictposet

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_
    is-irrefl : isIrrefl _<_
    is-trans : isTrans _<_
    is-asym : isAsym _<_

unquoteDecl IsStrictPosetIsoΣ = declareRecordIsoΣ IsStrictPosetIsoΣ (quote IsStrictPoset)


record StrictPosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor strictposetstr

  field
    _<_     : A → A → Type ℓ'
    isStrictPoset : IsStrictPoset _<_

  infixl 7 _<_

  open IsStrictPoset isStrictPoset public

StrictPoset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
StrictPoset ℓ ℓ' = TypeWithStr ℓ (StrictPosetStr ℓ')

strictposet : (A : Type ℓ) (_<_ : A → A → Type ℓ') (h : IsStrictPoset _<_) → StrictPoset ℓ ℓ'
strictposet A _<_ h = A , strictposetstr _<_ h

record IsStrictPosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : StrictPosetStr ℓ₀' A) (e : A ≃ B) (N : StrictPosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isstrictposetequiv
  -- Shorter qualified names
  private
    module M = StrictPosetStr M
    module N = StrictPosetStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y


StrictPosetEquiv : (M : StrictPoset ℓ₀ ℓ₀') (M : StrictPoset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
StrictPosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsStrictPosetEquiv (M .snd) e (N .snd)

isPropIsStrictPoset : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsStrictPoset _<_)
isPropIsStrictPoset _<_ = isOfHLevelRetractFromIso 1 IsStrictPosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued< → isProp×2 (isPropΠ (λ x → isProp¬ (x < x)))
                                 (isPropΠ5 (λ _ _ _ _ _ → isPropValued< _ _))
                                 (isPropΠ3 λ x y _ → isProp¬ (y < x)))

𝒮ᴰ-StrictPoset : DUARel (𝒮-Univ ℓ) (StrictPosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-StrictPoset =
  𝒮ᴰ-Record (𝒮-Univ _) IsStrictPosetEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isStrictPoset ∣ (λ _ _ → isPropIsStrictPoset _) ])
    where
    open StrictPosetStr
    open IsStrictPoset
    open IsStrictPosetEquiv

StrictPosetPath : (M N : StrictPoset ℓ ℓ') → StrictPosetEquiv M N ≃ (M ≡ N)
StrictPosetPath = ∫ 𝒮ᴰ-StrictPoset .UARel.ua

-- an easier way of establishing an equivalence of strict posets
module _ {P : StrictPoset ℓ₀ ℓ₀'} {S : StrictPoset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = StrictPosetStr (P .snd)
    module S = StrictPosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsStrictPosetEquiv
    open IsStrictPoset

    makeIsStrictPosetEquiv : IsStrictPosetEquiv (P .snd) e (S .snd)
    pres< makeIsStrictPosetEquiv x y = propBiimpl→Equiv (P.isStrictPoset .is-prop-valued _ _)
                                                  (S.isStrictPoset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex<ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex<ey)
