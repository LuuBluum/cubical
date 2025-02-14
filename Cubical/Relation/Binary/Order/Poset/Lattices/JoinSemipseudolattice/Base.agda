{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.JoinSemipseudolattice.Base where

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

record IsJoinSemipseudolattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ : A → A → A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isjoinsemipseudolattice

  field
    is-poset : IsPoset _≤_
    is-join : ∀ a b x → (a ∨l b) ≤ x ≃ (a ≤ x) × (b ≤ x)

unquoteDecl IsJoinSemipseudolatticeIsoΣ = declareRecordIsoΣ IsJoinSemipseudolatticeIsoΣ (quote IsJoinSemipseudolattice)


record JoinSemipseudolatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor joinsemipseudolatticestr

  field
    _≤_     : A → A → Type ℓ'
    _∨l_    : A → A → A
    isJoinSemipseudolattice : IsJoinSemipseudolattice _≤_ _∨l_

  infixl 7 _≤_
  infixl 8 _∨l_

  open IsJoinSemipseudolattice isJoinSemipseudolattice public

JoinSemipseudolatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (JoinSemipseudolatticeStr ℓ' A) → (PosetStr ℓ' A)
JoinSemipseudolatticeStr→PosetStr join = posetstr (JoinSemipseudolatticeStr._≤_ join)
                                                  (IsJoinSemipseudolattice.is-poset
                                                    (JoinSemipseudolatticeStr.isJoinSemipseudolattice join))

JoinSemipseudolattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
JoinSemipseudolattice ℓ ℓ' = TypeWithStr ℓ (JoinSemipseudolatticeStr ℓ')

joinsemipseudolattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∨l_ : A → A → A) → IsJoinSemipseudolattice _≤_ _∨l_ → JoinSemipseudolattice ℓ ℓ'
joinsemipseudolattice A _≤_ _∨l_ lat = A , (joinsemipseudolatticestr _≤_ _∨l_ lat)


record IsJoinSemipseudolatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : JoinSemipseudolatticeStr ℓ₀' A) (e : A ≃ B) (N : JoinSemipseudolatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   isjoinsemipseudolatticeequiv
  -- Shorter qualified names
  private
    module M = JoinSemipseudolatticeStr M
    module N = JoinSemipseudolatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∨ : (x y : A) → equivFun e (x M.∨l y) ≡ (equivFun e x) N.∨l (equivFun e y)

unquoteDecl IsJoinSemipseudolatticeEquivIsoΣ = declareRecordIsoΣ IsJoinSemipseudolatticeEquivIsoΣ (quote IsJoinSemipseudolatticeEquiv)

JoinSemipseudolatticeEquiv : (M : JoinSemipseudolattice ℓ₀ ℓ₀') (M : JoinSemipseudolattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
JoinSemipseudolatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsJoinSemipseudolatticeEquiv (M .snd) e (N .snd)

isPropIsJoinSemipseudolattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ : A → A → A) → isProp (IsJoinSemipseudolattice _≤_ _∨l_)
isPropIsJoinSemipseudolattice _≤_ _∨l_ = isOfHLevelRetractFromIso 1 IsJoinSemipseudolatticeIsoΣ
  (isPropΣ (isPropIsPoset _≤_)
    λ pos → isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                             (isProp× (IsPoset.is-prop-valued pos _ _)
                                                      (IsPoset.is-prop-valued pos _ _)))

isPropIsJoinSemipseudolatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : JoinSemipseudolatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : JoinSemipseudolatticeStr ℓ₁' B)
                                   → isProp (IsJoinSemipseudolatticeEquiv M e N)
isPropIsJoinSemipseudolatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsJoinSemipseudolatticeEquivIsoΣ
  (isProp×
    (isPropΠ2 λ _ _ → isOfHLevel≃ 1
                                (IsPoset.is-prop-valued (IsJoinSemipseudolattice.is-poset
                                                        (JoinSemipseudolatticeStr.isJoinSemipseudolattice M)) _ _)
                                (IsPoset.is-prop-valued (IsJoinSemipseudolattice.is-poset
                                                        (JoinSemipseudolatticeStr.isJoinSemipseudolattice N)) _ _))
   (isPropΠ2 λ _ _ → IsPoset.is-set (IsJoinSemipseudolattice.is-poset
                                    (JoinSemipseudolatticeStr.isJoinSemipseudolattice N)) _ _))

𝒮ᴰ-JoinSemipseudolattice : DUARel (𝒮-Univ ℓ) (JoinSemipseudolatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-JoinSemipseudolattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsJoinSemipseudolatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∨l_ ∣ autoDUARel _ _ ∣ pres∨ ]
      prop[ isJoinSemipseudolattice ∣ (λ _ _ → isPropIsJoinSemipseudolattice _ _) ])
    where
    open JoinSemipseudolatticeStr
    open IsJoinSemipseudolattice
    open IsJoinSemipseudolatticeEquiv

JoinSemipseudolatticePath : (M N : JoinSemipseudolattice ℓ ℓ') → JoinSemipseudolatticeEquiv M N ≃ (M ≡ N)
JoinSemipseudolatticePath = ∫ 𝒮ᴰ-JoinSemipseudolattice .UARel.ua

-- an easier way of establishing an equivalence of join semipseudolattices; poset equivs are lattice equivs
module _ {P : JoinSemipseudolattice ℓ₀ ℓ₀'} {S : JoinSemipseudolattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = JoinSemipseudolatticeStr (P .snd)
    module S = JoinSemipseudolatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = JoinSemipseudolatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = JoinSemipseudolatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open JoinSemipseudolatticeStr
    open IsJoinSemipseudolatticeEquiv
    open IsJoinSemipseudolattice

    makeIsJoinSemipseudolatticeEquiv : IsJoinSemipseudolatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsJoinSemipseudolatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∨ makeIsJoinSemipseudolatticeEquiv x y
      = isJoinUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∨l y))
                     (equivFun e x S.∨l equivFun e y)
                     (equivFun (IsPosetEquivRespectsJoin (e , isPosetEquiv) x y (x P.∨l y))
                               (is-join (isJoinSemipseudolattice (P .snd)) x y))
                     (is-join (isJoinSemipseudolattice (S .snd)) (equivFun e x) (equivFun e y))
