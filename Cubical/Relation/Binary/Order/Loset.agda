{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Loset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.HITs.PropositionalTruncation

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

record IsLoset {A : Type ℓ} (_≤_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isloset

  field
    is-set : isSet A
    is-prop-valued : isPropValued _≤_
    is-refl : isRefl _≤_
    is-trans : isTrans _≤_
    is-antisym : isAntisym _≤_
    is-strongly-connected : isStronglyConnected _≤_

unquoteDecl IsLosetIsoΣ = declareRecordIsoΣ IsLosetIsoΣ (quote IsLoset)


record LosetStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor losetstr

  field
    _≤_     : A → A → Type ℓ'
    isLoset : IsLoset _≤_

  infixl 7 _≤_

  open IsLoset isLoset public

Loset : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Loset ℓ ℓ' = TypeWithStr ℓ (LosetStr ℓ')

loset : (A : Type ℓ) (_≤_ : A → A → Type ℓ') (h : IsLoset _≤_) → Loset ℓ ℓ'
loset A _≤_ h = A , losetstr _≤_ h

record IsLosetEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : LosetStr ℓ₀' A) (e : A ≃ B) (N : LosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor
   islosetequiv
  -- Shorter qualified names
  private
    module M = LosetStr M
    module N = LosetStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y


LosetEquiv : (M : Loset ℓ₀ ℓ₀') (M : Loset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
LosetEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsLosetEquiv (M .snd) e (N .snd)

isPropIsLoset : {A : Type ℓ} (_≤_ : A → A → Type ℓ') → isProp (IsLoset _≤_)
isPropIsLoset _≤_ = isOfHLevelRetractFromIso 1 IsLosetIsoΣ
  (isPropΣ isPropIsSet
    λ isSetA → isPropΣ (isPropΠ2 (λ _ _ → isPropIsProp))
      λ isPropValued≤ → isProp×3
                         (isPropΠ (λ _ → isPropValued≤ _ _))
                           (isPropΠ5 λ _ _ _ _ _ → isPropValued≤ _ _)
                             (isPropΠ4 λ _ _ _ _ → isSetA _ _)
                               (isPropΠ2 λ _ _ → squash₁))

𝒮ᴰ-Loset : DUARel (𝒮-Univ ℓ) (LosetStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Loset =
  𝒮ᴰ-Record (𝒮-Univ _) IsLosetEquiv
    (fields:
      data[ _≤_ ∣ autoDUARel _ _ ∣ pres≤ ]
      prop[ isLoset ∣ (λ _ _ → isPropIsLoset _) ])
    where
    open LosetStr
    open IsLoset
    open IsLosetEquiv

LosetPath : (M N : Loset ℓ ℓ') → LosetEquiv M N ≃ (M ≡ N)
LosetPath = ∫ 𝒮ᴰ-Loset .UARel.ua

-- an easier way of establishing an equivalence of posets
module _ {P : Loset ℓ₀ ℓ₀'} {S : Loset ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = LosetStr (P .snd)
    module S = LosetStr (S .snd)

  module _ (isMon : ∀ x y → x P.≤ y → equivFun e x S.≤ equivFun e y)
           (isMonInv : ∀ x y → x S.≤ y → invEq e x P.≤ invEq e y) where
    open IsLosetEquiv
    open IsLoset

    makeIsLosetEquiv : IsLosetEquiv (P .snd) e (S .snd)
    pres≤ makeIsLosetEquiv x y = propBiimpl→Equiv (P.isLoset .is-prop-valued _ _)
                                                  (S.isLoset .is-prop-valued _ _)
                                                  (isMon _ _) (isMonInv' _ _)
      where
      isMonInv' : ∀ x y → equivFun e x S.≤ equivFun e y → x P.≤ y
      isMonInv' x y ex≤ey = transport (λ i → retEq e x i P.≤ retEq e y i) (isMonInv _ _ ex≤ey)


module LosetReasoning (P' : Loset ℓ ℓ') where
 private P = fst P'
 open LosetStr (snd P')
 open IsLoset

 _≤⟨_⟩_ : (x : P) {y z : P} → x ≤ y → y ≤ z → x ≤ z
 x ≤⟨ p ⟩ q = isLoset .is-trans x _ _ p q

 _◾ : (x : P) → x ≤ x
 x ◾ = isLoset .is-refl x

 infixr 0 _≤⟨_⟩_
 infix  1 _◾
