{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.MeetSemipseudolattice.Base where

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
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties

open Iso
open BinaryRelation


private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

record IsMeetSemipseudolattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∧l_ : A → A → A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ismeetsemipseudolattice

  field
    is-poset : IsPoset _≤_
    is-meet : ∀ a b x → x ≤ (a ∧l b) ≃ (x ≤ a) × (x ≤ b)

unquoteDecl IsMeetSemipseudolatticeIsoΣ = declareRecordIsoΣ IsMeetSemipseudolatticeIsoΣ (quote IsMeetSemipseudolattice)


record MeetSemipseudolatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor meetsemipseudolatticestr

  field
    _≤_     : A → A → Type ℓ'
    _∧l_    : A → A → A
    isMeetSemipseudolattice : IsMeetSemipseudolattice _≤_ _∧l_

  infixl 7 _≤_
  infixl 8 _∧l_

  open IsMeetSemipseudolattice isMeetSemipseudolattice public

MeetSemipseudolatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (MeetSemipseudolatticeStr ℓ' A) → (PosetStr ℓ' A)
MeetSemipseudolatticeStr→PosetStr meet = posetstr (MeetSemipseudolatticeStr._≤_ meet)
                                                  (IsMeetSemipseudolattice.is-poset
                                                    (MeetSemipseudolatticeStr.isMeetSemipseudolattice meet))

MeetSemipseudolattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
MeetSemipseudolattice ℓ ℓ' = TypeWithStr ℓ (MeetSemipseudolatticeStr ℓ')

meetsemipseudolattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∧l_ : A → A → A) → IsMeetSemipseudolattice _≤_ _∧l_ → MeetSemipseudolattice ℓ ℓ'
meetsemipseudolattice A _≤_ _∧l_ lat = A , (meetsemipseudolatticestr _≤_ _∧l_ lat)


record IsMeetSemipseudolatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : MeetSemipseudolatticeStr ℓ₀' A) (e : A ≃ B) (N : MeetSemipseudolatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   ismeetsemipseudolatticeequiv
  -- Shorter qualified names
  private
    module M = MeetSemipseudolatticeStr M
    module N = MeetSemipseudolatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∧ : (x y : A) → equivFun e (x M.∧l y) ≡ (equivFun e x) N.∧l (equivFun e y)

unquoteDecl IsMeetSemipseudolatticeEquivIsoΣ = declareRecordIsoΣ IsMeetSemipseudolatticeEquivIsoΣ (quote IsMeetSemipseudolatticeEquiv)

MeetSemipseudolatticeEquiv : (M : MeetSemipseudolattice ℓ₀ ℓ₀') (M : MeetSemipseudolattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
MeetSemipseudolatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsMeetSemipseudolatticeEquiv (M .snd) e (N .snd)

isPropIsMeetSemipseudolattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∧l_ : A → A → A) → isProp (IsMeetSemipseudolattice _≤_ _∧l_)
isPropIsMeetSemipseudolattice _≤_ _∧l_ = isOfHLevelRetractFromIso 1 IsMeetSemipseudolatticeIsoΣ
  (isPropΣ (isPropIsPoset _≤_)
    λ pos → isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                             (isProp× (IsPoset.is-prop-valued pos _ _)
                                                      (IsPoset.is-prop-valued pos _ _)))

isPropIsMeetSemipseudolatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : MeetSemipseudolatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : MeetSemipseudolatticeStr ℓ₁' B)
                                   → isProp (IsMeetSemipseudolatticeEquiv M e N)
isPropIsMeetSemipseudolatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsMeetSemipseudolatticeEquivIsoΣ
  (isProp×
    (isPropΠ2 λ _ _ → isOfHLevel≃ 1
                                (IsPoset.is-prop-valued (IsMeetSemipseudolattice.is-poset
                                                        (MeetSemipseudolatticeStr.isMeetSemipseudolattice M)) _ _)
                                (IsPoset.is-prop-valued (IsMeetSemipseudolattice.is-poset
                                                        (MeetSemipseudolatticeStr.isMeetSemipseudolattice N)) _ _))
   (isPropΠ2 λ _ _ → IsPoset.is-set (IsMeetSemipseudolattice.is-poset
                                   (MeetSemipseudolatticeStr.isMeetSemipseudolattice N)) _ _))

𝒮ᴰ-MeetSemipseudolattice : DUARel (𝒮-Univ ℓ) (MeetSemipseudolatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-MeetSemipseudolattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsMeetSemipseudolatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∧l_ ∣ autoDUARel _ _ ∣ pres∧ ]
      prop[ isMeetSemipseudolattice ∣ (λ _ _ → isPropIsMeetSemipseudolattice _ _) ])
    where
    open MeetSemipseudolatticeStr
    open IsMeetSemipseudolattice
    open IsMeetSemipseudolatticeEquiv

MeetSemipseudolatticePath : (M N : MeetSemipseudolattice ℓ ℓ') → MeetSemipseudolatticeEquiv M N ≃ (M ≡ N)
MeetSemipseudolatticePath = ∫ 𝒮ᴰ-MeetSemipseudolattice .UARel.ua

-- an easier way of establishing an equivalence of meet semipseudolattices; poset equivs are lattice equivs
module _ {P : MeetSemipseudolattice ℓ₀ ℓ₀'} {S : MeetSemipseudolattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = MeetSemipseudolatticeStr (P .snd)
    module S = MeetSemipseudolatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = MeetSemipseudolatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = MeetSemipseudolatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open MeetSemipseudolatticeStr
    open IsMeetSemipseudolatticeEquiv
    open IsMeetSemipseudolattice

    makeIsMeetSemipseudolatticeEquiv : IsMeetSemipseudolatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsMeetSemipseudolatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∧ makeIsMeetSemipseudolatticeEquiv x y
      = isMeetUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∧l y))
                     (equivFun e x S.∧l equivFun e y)
                     (equivFun (IsPosetEquivRespectsMeet (e , isPosetEquiv) x y (x P.∧l y))
                               (is-meet (isMeetSemipseudolattice (P .snd)) x y))
                     (is-meet (isMeetSemipseudolattice (S .snd)) (equivFun e x) (equivFun e y))
