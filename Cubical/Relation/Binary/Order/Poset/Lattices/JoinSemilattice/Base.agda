{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.JoinSemilattice.Base where

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

record IsJoinSemilattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ : A → A → A) (1l : A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isjoinsemilattice

  field
    is-poset : IsPoset _≤_
    is-join : ∀ a b x → (a ∨l b) ≤ x ≃ (a ≤ x) × (b ≤ x)
    is-greatest : ∀ x → x ≤ 1l

unquoteDecl IsJoinSemilatticeIsoΣ = declareRecordIsoΣ IsJoinSemilatticeIsoΣ (quote IsJoinSemilattice)


record JoinSemilatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor joinsemilatticestr

  field
    _≤_     : A → A → Type ℓ'
    _∨l_    : A → A → A
    1l      : A
    isJoinSemilattice : IsJoinSemilattice _≤_ _∨l_ 1l

  infixl 7 _≤_
  infixl 8 _∨l_

  open IsJoinSemilattice isJoinSemilattice public

JoinSemilatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (JoinSemilatticeStr ℓ' A) → (PosetStr ℓ' A)
JoinSemilatticeStr→PosetStr join = posetstr (JoinSemilatticeStr._≤_ join)
                                                  (IsJoinSemilattice.is-poset
                                                    (JoinSemilatticeStr.isJoinSemilattice join))

JoinSemilattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
JoinSemilattice ℓ ℓ' = TypeWithStr ℓ (JoinSemilatticeStr ℓ')

joinsemilattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∨l_ : A → A → A) (1l : A) → IsJoinSemilattice _≤_ _∨l_ 1l → JoinSemilattice ℓ ℓ'
joinsemilattice A _≤_ _∨l_ 1l lat = A , (joinsemilatticestr _≤_ _∨l_ 1l lat)


record IsJoinSemilatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : JoinSemilatticeStr ℓ₀' A) (e : A ≃ B) (N : JoinSemilatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   isjoinsemilatticeequiv
  -- Shorter qualified names
  private
    module M = JoinSemilatticeStr M
    module N = JoinSemilatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∨ : (x y : A) → equivFun e (x M.∨l y) ≡ (equivFun e x) N.∨l (equivFun e y)
    pres1 : equivFun e M.1l ≡ N.1l

unquoteDecl IsJoinSemilatticeEquivIsoΣ = declareRecordIsoΣ IsJoinSemilatticeEquivIsoΣ (quote IsJoinSemilatticeEquiv)

JoinSemilatticeEquiv : (M : JoinSemilattice ℓ₀ ℓ₀') (M : JoinSemilattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
JoinSemilatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsJoinSemilatticeEquiv (M .snd) e (N .snd)

isPropIsJoinSemilattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ : A → A → A) (1l : A) → isProp (IsJoinSemilattice _≤_ _∨l_ 1l)
isPropIsJoinSemilattice _≤_ _∨l_ 1l = isOfHLevelRetractFromIso 1 IsJoinSemilatticeIsoΣ
  (isPropΣ (isPropIsPoset _≤_)
    λ pos → isProp× (isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                       (isProp× (IsPoset.is-prop-valued pos _ _)
                                                                (IsPoset.is-prop-valued pos _ _)))
                    (isPropΠ λ _ → IsPoset.is-prop-valued pos _ _))

isPropIsJoinSemilatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : JoinSemilatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : JoinSemilatticeStr ℓ₁' B)
                                   → isProp (IsJoinSemilatticeEquiv M e N)
isPropIsJoinSemilatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsJoinSemilatticeEquivIsoΣ
  (isProp×
    (isPropΠ2 λ _ _ → isOfHLevel≃ 1
                                (IsPoset.is-prop-valued (IsJoinSemilattice.is-poset
                                                        (JoinSemilatticeStr.isJoinSemilattice M)) _ _)
                                (IsPoset.is-prop-valued (IsJoinSemilattice.is-poset
                                                        (JoinSemilatticeStr.isJoinSemilattice N)) _ _))
  (isProp× (isPropΠ2 (λ _ _ → IsPoset.is-set (IsJoinSemilattice.is-poset
                                             (JoinSemilatticeStr.isJoinSemilattice N)) _ _))
                             (IsPoset.is-set (IsJoinSemilattice.is-poset
                                             (JoinSemilatticeStr.isJoinSemilattice N)) _ _)))

𝒮ᴰ-JoinSemilattice : DUARel (𝒮-Univ ℓ) (JoinSemilatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-JoinSemilattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsJoinSemilatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∨l_ ∣ autoDUARel _ _ ∣ pres∨ ]
      data[ 1l   ∣ autoDUARel _ _ ∣ pres1 ]
      prop[ isJoinSemilattice ∣ (λ _ _ → isPropIsJoinSemilattice _ _ _) ])
    where
    open JoinSemilatticeStr
    open IsJoinSemilattice
    open IsJoinSemilatticeEquiv

JoinSemilatticePath : (M N : JoinSemilattice ℓ ℓ') → JoinSemilatticeEquiv M N ≃ (M ≡ N)
JoinSemilatticePath = ∫ 𝒮ᴰ-JoinSemilattice .UARel.ua

-- an easier way of establishing an equivalence of join semilattices; poset equivs are lattice equivs
module _ {P : JoinSemilattice ℓ₀ ℓ₀'} {S : JoinSemilattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = JoinSemilatticeStr (P .snd)
    module S = JoinSemilatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = JoinSemilatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = JoinSemilatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open JoinSemilatticeStr
    open IsJoinSemilatticeEquiv
    open IsJoinSemilattice

    makeIsJoinSemilatticeEquiv : IsJoinSemilatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsJoinSemilatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∨ makeIsJoinSemilatticeEquiv x y
      = isJoinUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∨l y))
                     (equivFun e x S.∨l equivFun e y)
                     (equivFun (IsPosetEquivRespectsJoin (e , isPosetEquiv) x y (x P.∨l y))
                               (is-join (isJoinSemilattice (P .snd)) x y))
                     (is-join (isJoinSemilattice (S .snd)) (equivFun e x) (equivFun e y))
    pres1 makeIsJoinSemilatticeEquiv
      = isGreatestUnique (PosetStr.isPoset Spos)
                         {P = ⟨ S ⟩ , id↪ ⟨ S ⟩}
                         (equivFun e P.1l)
                          S.1l
                         (λ x → subst (S._≤ equivFun e P.1l)
                                      (secEq e x)
                                      (equivFun (IsPosetEquiv.pres≤ isPosetEquiv (invEq e x) P.1l)
                                                (P.is-greatest (invEq e x))))
                         (is-greatest (isJoinSemilattice (S .snd)))
