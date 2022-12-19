{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.StrictLoset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

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

record IsStrictLoset {A : Type ℓ} (_<_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isstrictloset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _<_
    is-irrefl : isIrrefl _<_
    is-trans : isTrans _<_
    is-asym : isAsym _<_
    is-connected : isConnected _<_

unquoteDecl IsStrictLosetIsoΣ = declareRecordIsoΣ IsStrictLosetIsoΣ (quote IsStrictLoset)


record StrictLosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor strictlosetstr

  field
    _<_     : A → A → Type ℓ'
    isStrictLoset : IsStrictLoset _<_

  infixl 7 _<_

  open IsStrictLoset isStrictLoset public

StrictLoset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
StrictLoset ℓ ℓ' = TypeWithStr ℓ (StrictLosetStr ℓ')

strictloset : (A : Type ℓ) (_<_ : A → A → Type ℓ') (h : IsStrictLoset _<_) → StrictLoset ℓ ℓ'
strictloset A _<_ h = A , strictlosetstr _<_ h

record IsStrictLosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : StrictLosetStr ℓ₀' A) (e : A ≃ B) (N : StrictLosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   isstrictlosetequiv
  -- Shorter qualified names
  private
    module M = StrictLosetStr M
    module N = StrictLosetStr N

  field
    pres< : (x y : A) → x M.< y ≃ equivFun e x N.< equivFun e y


StrictLosetEquiv : (M : StrictLoset ℓ₀ ℓ₀') (M : StrictLoset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
StrictLosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsStrictLosetEquiv (M .snd) e (N .snd)

isPropIsStrictLoset : {A : Type ℓ} (_<_ : A → A → Type ℓ') → isProp (IsStrictLoset _<_)
isPropIsStrictLoset _<_ = isOfHLevelRetractFromIso 1 IsStrictLosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued< → isProp×3 (isPropΠ (λ x → isProp¬ (x < x)))
                                 (isPropΠ5 (λ _ _ _ _ _ → isPropValued< _ _))
                                 (isPropΠ3 (λ x y _ → isProp¬ (y < x)))
                                 (isPropΠ3 λ _ _ _ → squash₁))

𝒮ᴰ-StrictLoset : DUARel (𝒮-Univ ℓ) (StrictLosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-StrictLoset =
  𝒮ᴰ-Record (𝒮-Univ _) IsStrictLosetEquiv
    (fields:
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      prop[ isStrictLoset ∣ (λ _ _ → isPropIsStrictLoset _) ])
    where
    open StrictLosetStr
    open IsStrictLoset
    open IsStrictLosetEquiv

StrictLosetPath : (M N : StrictLoset ℓ ℓ') → StrictLosetEquiv M N ≃ (M ≡ N)
StrictLosetPath = ∫ 𝒮ᴰ-StrictLoset .UARel.ua

-- an easier way of establishing an equivalence of strict posets
module _ {P : StrictLoset ℓ₀ ℓ₀'} {S : StrictLoset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = StrictLosetStr (P .snd)
    module S = StrictLosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.< y → equivFun e x S.< equivFun e y)
           (isMonInv : ∀ x y → x S.< y → invEq e x P.< invEq e y) where
    open IsStrictLosetEquiv
    open IsStrictLoset

    makeIsStrictLosetEquiv : IsStrictLosetEquiv (P .snd) e (S .snd)
    pres< makeIsStrictLosetEquiv x y = propBiimpl→Equiv (P.isStrictLoset .is-prop-valued _ _)
                                                  (S.isStrictLoset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.< equivFun e y → x P.< y
      isMonInv' x y ex<ey = transport (λ i → retEq e x i P.< retEq e y i) (isMonInv _ _ ex<ey)
