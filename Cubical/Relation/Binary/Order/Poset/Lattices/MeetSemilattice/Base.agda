{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.MeetSemilattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Functions.Embedding

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

record IsMeetSemilattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∧l_ : A → A → A) (0l : A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ismeetsemilattice

  field
    is-poset : IsPoset _≤_
    is-meet : ∀ a b x → x ≤ (a ∧l b) ≃ (x ≤ a) × (x ≤ b)
    is-least : ∀ x → 0l ≤ x

unquoteDecl IsMeetSemilatticeIsoΣ = declareRecordIsoΣ IsMeetSemilatticeIsoΣ (quote IsMeetSemilattice)


record MeetSemilatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor meetsemilatticestr

  field
    _≤_     : A → A → Type ℓ'
    _∧l_    : A → A → A
    0l      : A
    isMeetSemilattice : IsMeetSemilattice _≤_ _∧l_ 0l

  infixl 7 _≤_
  infixl 8 _∧l_

  open IsMeetSemilattice isMeetSemilattice public

MeetSemilatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (MeetSemilatticeStr ℓ' A) → (PosetStr ℓ' A)
MeetSemilatticeStr→PosetStr meet = posetstr (MeetSemilatticeStr._≤_ meet)
                                                  (IsMeetSemilattice.is-poset
                                                    (MeetSemilatticeStr.isMeetSemilattice meet))

MeetSemilattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
MeetSemilattice ℓ ℓ' = TypeWithStr ℓ (MeetSemilatticeStr ℓ')

meetsemilattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∧l_ : A → A → A) (0l : A) → IsMeetSemilattice _≤_ _∧l_ 0l → MeetSemilattice ℓ ℓ'
meetsemilattice A _≤_ _∧l_ 0l lat = A , (meetsemilatticestr _≤_ _∧l_ 0l lat)


record IsMeetSemilatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : MeetSemilatticeStr ℓ₀' A) (e : A ≃ B) (N : MeetSemilatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   ismeetsemilatticeequiv
  -- Shorter qualified names
  private
    module M = MeetSemilatticeStr M
    module N = MeetSemilatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∧ : (x y : A) → equivFun e (x M.∧l y) ≡ (equivFun e x) N.∧l (equivFun e y)
    pres0 : equivFun e M.0l ≡ N.0l

  pres≤⁻ : (x y : B) → x N.≤ y ≃ invEq e x M.≤ invEq e y
  pres≤⁻ x y = invEquiv (compEquiv (pres≤ (invEq e x) (invEq e y))
                                    (subst2Equiv N._≤_ (secEq e x) (secEq e y)))

unquoteDecl IsMeetSemilatticeEquivIsoΣ = declareRecordIsoΣ IsMeetSemilatticeEquivIsoΣ (quote IsMeetSemilatticeEquiv)

MeetSemilatticeEquiv : (M : MeetSemilattice ℓ₀ ℓ₀') (M : MeetSemilattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
MeetSemilatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsMeetSemilatticeEquiv (M .snd) e (N .snd)

isPropIsMeetSemilattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∧l_ : A → A → A) (0l : A) → isProp (IsMeetSemilattice _≤_ _∧l_ 0l)
isPropIsMeetSemilattice _≤_ _∧l_ 0l = isOfHLevelRetractFromIso 1 IsMeetSemilatticeIsoΣ
  (isPropΣ (isPropIsPoset _≤_)
    λ pos → isProp× (isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                      (isProp× (IsPoset.is-prop-valued pos _ _)
                                                               (IsPoset.is-prop-valued pos _ _)))
                    (isPropΠ λ _ → IsPoset.is-prop-valued pos _ _))

isPropIsMeetSemilatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : MeetSemilatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : MeetSemilatticeStr ℓ₁' B)
                                   → isProp (IsMeetSemilatticeEquiv M e N)
isPropIsMeetSemilatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsMeetSemilatticeEquivIsoΣ
  (isProp×
    (isPropΠ2 λ _ _ → isOfHLevel≃ 1
                                (IsPoset.is-prop-valued (IsMeetSemilattice.is-poset
                                                        (MeetSemilatticeStr.isMeetSemilattice M)) _ _)
                                (IsPoset.is-prop-valued (IsMeetSemilattice.is-poset
                                                        (MeetSemilatticeStr.isMeetSemilattice N)) _ _))
  (isProp× (isPropΠ2 (λ _ _ → IsPoset.is-set (IsMeetSemilattice.is-poset
                                             (MeetSemilatticeStr.isMeetSemilattice N)) _ _))
                             (IsPoset.is-set (IsMeetSemilattice.is-poset
                                             (MeetSemilatticeStr.isMeetSemilattice N)) _ _)))

𝒮ᴰ-MeetSemilattice : DUARel (𝒮-Univ ℓ) (MeetSemilatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-MeetSemilattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsMeetSemilatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∧l_ ∣ autoDUARel _ _ ∣ pres∧ ]
      data[ 0l   ∣ autoDUARel _ _ ∣ pres0 ]
      prop[ isMeetSemilattice ∣ (λ _ _ → isPropIsMeetSemilattice _ _ _) ])
    where
    open MeetSemilatticeStr
    open IsMeetSemilattice
    open IsMeetSemilatticeEquiv

MeetSemilatticePath : (M N : MeetSemilattice ℓ ℓ') → MeetSemilatticeEquiv M N ≃ (M ≡ N)
MeetSemilatticePath = ∫ 𝒮ᴰ-MeetSemilattice .UARel.ua

-- an easier way of establishing an equivalence of meet semilattices; poset equivs are lattice equivs
module _ {P : MeetSemilattice ℓ₀ ℓ₀'} {S : MeetSemilattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = MeetSemilatticeStr (P .snd)
    module S = MeetSemilatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = MeetSemilatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = MeetSemilatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open MeetSemilatticeStr
    open IsMeetSemilatticeEquiv
    open IsMeetSemilattice

    makeIsMeetSemilatticeEquiv : IsMeetSemilatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsMeetSemilatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∧ makeIsMeetSemilatticeEquiv x y
      = isMeetUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∧l y))
                     (equivFun e x S.∧l equivFun e y)
                     (equivFun (IsPosetEquivRespectsMeet (e , isPosetEquiv) x y (x P.∧l y))
                               (is-meet (isMeetSemilattice (P .snd)) x y))
                     (is-meet (isMeetSemilattice (S .snd)) (equivFun e x) (equivFun e y))
    pres0 makeIsMeetSemilatticeEquiv
      = isLeastUnique (PosetStr.isPoset Spos)
                      {P = ⟨ S ⟩ , id↪ ⟨ S ⟩}
                      (equivFun e P.0l)
                       S.0l
                      (λ x → subst (equivFun e P.0l S.≤_)
                                   (secEq e x)
                                   (equivFun (IsPosetEquiv.pres≤ isPosetEquiv P.0l (invEq e x))
                                             (P.is-least (invEq e x))))
                      (is-least (isMeetSemilattice (S .snd)))
