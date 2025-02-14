{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.Pseudolattice.Base where

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

record IsPseudolattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ _∧l_ : A → A → A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor ispseudolattice

  field
    is-poset : IsPoset _≤_
    is-join : ∀ a b x → (a ∨l b) ≤ x ≃ (a ≤ x) × (b ≤ x)
    is-meet : ∀ a b x → x ≤ (a ∧l b) ≃ (x ≤ a) × (x ≤ b)

unquoteDecl IsPseudolatticeIsoΣ = declareRecordIsoΣ IsPseudolatticeIsoΣ (quote IsPseudolattice)


record PseudolatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor pseudolatticestr

  field
    _≤_     : A → A → Type ℓ'
    _∨l_    : A → A → A
    _∧l_    : A → A → A
    isPseudolattice : IsPseudolattice _≤_ _∨l_ _∧l_

  infixl 7 _≤_
  infixl 8 _∨l_
  infixl 8 _∧l_

  open IsPseudolattice isPseudolattice public

PseudolatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (PseudolatticeStr ℓ' A) → (PosetStr ℓ' A)
PseudolatticeStr→PosetStr lat = posetstr (PseudolatticeStr._≤_ lat)
                                         (IsPseudolattice.is-poset
                                         (PseudolatticeStr.isPseudolattice lat))

Pseudolattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Pseudolattice ℓ ℓ' = TypeWithStr ℓ (PseudolatticeStr ℓ')

pseudolattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∨l_ _∧l_ : A → A → A) → IsPseudolattice _≤_ _∨l_ _∧l_ → Pseudolattice ℓ ℓ'
pseudolattice A _≤_ _∨l_ _∧l_ lat = A , (pseudolatticestr _≤_ _∨l_ _∧l_ lat)


record IsPseudolatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : PseudolatticeStr ℓ₀' A) (e : A ≃ B) (N : PseudolatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   ispseudolatticeequiv
  -- Shorter qualified names
  private
    module M = PseudolatticeStr M
    module N = PseudolatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∨ : (x y : A) → equivFun e (x M.∨l y) ≡ (equivFun e x) N.∨l (equivFun e y)
    pres∧ : (x y : A) → equivFun e (x M.∧l y) ≡ (equivFun e x) N.∧l (equivFun e y)

unquoteDecl IsPseudolatticeEquivIsoΣ = declareRecordIsoΣ IsPseudolatticeEquivIsoΣ (quote IsPseudolatticeEquiv)

PseudolatticeEquiv : (M : Pseudolattice ℓ₀ ℓ₀') (M : Pseudolattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
PseudolatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsPseudolatticeEquiv (M .snd) e (N .snd)

isPropIsPseudolattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ _∧l_ : A → A → A) → isProp (IsPseudolattice _≤_ _∨l_ _∧l_)
isPropIsPseudolattice _≤_ _∨l_ _∧l_ = isOfHLevelRetractFromIso 1 IsPseudolatticeIsoΣ
  (isPropΣ (isPropIsPoset _)
    λ pos → isProp× (isPropΠ3 (λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                        (isProp× (IsPoset.is-prop-valued pos _ _)
                                                                 (IsPoset.is-prop-valued pos _ _))))
                    (isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                       (isProp× (IsPoset.is-prop-valued pos _ _)
                                                                (IsPoset.is-prop-valued pos _ _))))

isPropIsPseudolatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : PseudolatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : PseudolatticeStr ℓ₁' B)
                                   → isProp (IsPseudolatticeEquiv M e N)
isPropIsPseudolatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsPseudolatticeEquivIsoΣ
  (isProp× (isPropΠ2
              (λ _ _ →
                 isOfHLevel≃ 1 (IsPoset.is-prop-valued (IsPseudolattice.is-poset
                                                       (PseudolatticeStr.isPseudolattice M)) _ _)
                               (IsPoset.is-prop-valued (IsPseudolattice.is-poset
                                                       (PseudolatticeStr.isPseudolattice N)) _ _)))
           (isProp× (isPropΠ2 λ _ _ → IsPoset.is-set (IsPseudolattice.is-poset
                                                     (PseudolatticeStr.isPseudolattice N)) _ _)
                    (isPropΠ2 λ _ _ → IsPoset.is-set (IsPseudolattice.is-poset
                                                     (PseudolatticeStr.isPseudolattice N)) _ _)))

𝒮ᴰ-Pseudolattice : DUARel (𝒮-Univ ℓ) (PseudolatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Pseudolattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsPseudolatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∨l_ ∣ autoDUARel _ _ ∣ pres∨ ]
      data[ _∧l_ ∣ autoDUARel _ _ ∣ pres∧ ]
      prop[ isPseudolattice ∣ (λ _ _ → isPropIsPseudolattice _ _ _) ])
    where
    open PseudolatticeStr
    open IsPseudolattice
    open IsPseudolatticeEquiv

PseudolatticePath : (M N : Pseudolattice ℓ ℓ') → PseudolatticeEquiv M N ≃ (M ≡ N)
PseudolatticePath = ∫ 𝒮ᴰ-Pseudolattice .UARel.ua

-- an easier way of establishing an equivalence of pseudolattices; poset equivs are lattice equivs
module _ {P : Pseudolattice ℓ₀ ℓ₀'} {S : Pseudolattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = PseudolatticeStr (P .snd)
    module S = PseudolatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = PseudolatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = PseudolatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open PseudolatticeStr
    open IsPseudolatticeEquiv
    open IsPseudolattice

    makeIsPseudolatticeEquiv : IsPseudolatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsPseudolatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∨ makeIsPseudolatticeEquiv x y
      = isJoinUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∨l y))
                     (equivFun e x S.∨l equivFun e y)
                     (equivFun (IsPosetEquivRespectsJoin (e , isPosetEquiv) x y (x P.∨l y))
                               (is-join (isPseudolattice (P .snd)) x y))
                     (is-join (isPseudolattice (S .snd)) (equivFun e x) (equivFun e y))
    pres∧ makeIsPseudolatticeEquiv x y
      = isMeetUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∧l y))
                     (equivFun e x S.∧l equivFun e y)
                     (equivFun (IsPosetEquivRespectsMeet (e , isPosetEquiv) x y (x P.∧l y))
                               (is-meet (isPseudolattice (P .snd)) x y))
                     (is-meet (isPseudolattice (S .snd)) (equivFun e x) (equivFun e y))
