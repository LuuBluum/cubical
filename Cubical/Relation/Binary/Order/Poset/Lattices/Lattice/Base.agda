{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.Lattice.Base where

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

record IsLattice {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ _∧l_ : A → A → A) (0l 1l : A) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor islattice

  field
    is-poset : IsPoset _≤_
    is-join : ∀ a b x → (a ∨l b) ≤ x ≃ (a ≤ x) × (b ≤ x)
    is-meet : ∀ a b x → x ≤ (a ∧l b) ≃ (x ≤ a) × (x ≤ b)
    is-least : ∀ x → 0l ≤ x
    is-greatest : ∀ x → x ≤ 1l

unquoteDecl IsLatticeIsoΣ = declareRecordIsoΣ IsLatticeIsoΣ (quote IsLattice)


record LatticeStr (ℓ' : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where

  constructor latticestr

  field
    _≤_     : A → A → Type ℓ'
    _∨l_    : A → A → A
    _∧l_    : A → A → A
    0l      : A
    1l      : A
    isLattice : IsLattice _≤_ _∨l_ _∧l_ 0l 1l

  infixl 7 _≤_
  infixl 8 _∨l_
  infixl 8 _∧l_

  open IsLattice isLattice public

LatticeStr→PosetStr : ∀{ℓ'} → {A : Type ℓ} → (LatticeStr ℓ' A) → (PosetStr ℓ' A)
LatticeStr→PosetStr lat = posetstr (LatticeStr._≤_ lat)
                                         (IsLattice.is-poset
                                         (LatticeStr.isLattice lat))

Lattice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Lattice ℓ ℓ' = TypeWithStr ℓ (LatticeStr ℓ')

lattice : (A : Type ℓ) → (_≤_ : Rel A A ℓ') → (_∨l_ _∧l_ : A → A → A) (0l 1l : A) → IsLattice _≤_ _∨l_ _∧l_ 0l 1l → Lattice ℓ ℓ'
lattice A _≤_ _∨l_ _∧l_ 0l 1l lat = A , (latticestr _≤_ _∨l_ _∧l_ 0l 1l lat)


record IsLatticeEquiv {A : Type ℓ₀} {B : Type ℓ₁}
  (M : LatticeStr ℓ₀' A) (e : A ≃ B) (N : LatticeStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₁) (ℓ-max ℓ₀' ℓ₁'))
  where
  constructor
   islatticeequiv
  -- Shorter qualified names
  private
    module M = LatticeStr M
    module N = LatticeStr N

  field
    pres≤ : (x y : A) → x M.≤ y ≃ equivFun e x N.≤ equivFun e y
    pres∨ : (x y : A) → equivFun e (x M.∨l y) ≡ (equivFun e x) N.∨l (equivFun e y)
    pres∧ : (x y : A) → equivFun e (x M.∧l y) ≡ (equivFun e x) N.∧l (equivFun e y)
    pres0 : equivFun e (M.0l) ≡ N.0l
    pres1 : equivFun e (M.1l) ≡ N.1l

unquoteDecl IsLatticeEquivIsoΣ = declareRecordIsoΣ IsLatticeEquivIsoΣ (quote IsLatticeEquiv)

LatticeEquiv : (M : Lattice ℓ₀ ℓ₀') (M : Lattice ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
LatticeEquiv M N = Σ[ e ∈ ⟨ M ⟩ ≃ ⟨ N ⟩ ] IsLatticeEquiv (M .snd) e (N .snd)

isPropIsLattice : {A : Type ℓ} (_≤_ : A → A → Type ℓ') (_∨l_ _∧l_ : A → A → A) (0l 1l : A) → isProp (IsLattice _≤_ _∨l_ _∧l_ 0l 1l)
isPropIsLattice _≤_ _∨l_ _∧l_ 0l 1l = isOfHLevelRetractFromIso 1 IsLatticeIsoΣ
  (isPropΣ (isPropIsPoset _)
    λ pos → isProp× (isPropΠ3 (λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                        (isProp× (IsPoset.is-prop-valued pos _ _)
                                                                 (IsPoset.is-prop-valued pos _ _))))
           (isProp× (isPropΠ3 λ _ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued pos _ _)
                                                       (isProp× (IsPoset.is-prop-valued pos _ _)
                                                                (IsPoset.is-prop-valued pos _ _)))
           (isProp× (isPropΠ (λ _ → IsPoset.is-prop-valued pos _ _))
                    (isPropΠ λ _ → IsPoset.is-prop-valued pos _ _))))

isPropIsLatticeEquiv : {A : Type ℓ₀} {B : Type ℓ₁}
                                     (M : LatticeStr ℓ₀' A)
                                     (e : A ≃ B)
                                     (N : LatticeStr ℓ₁' B)
                                   → isProp (IsLatticeEquiv M e N)
isPropIsLatticeEquiv M e N = isOfHLevelRetractFromIso 1 IsLatticeEquivIsoΣ
  (isProp× (isPropΠ2 (λ _ _ → isOfHLevel≃ 1 (IsPoset.is-prop-valued (IsLattice.is-poset (LatticeStr.isLattice M)) _ _)
                                             (IsPoset.is-prop-valued (IsLattice.is-poset (LatticeStr.isLattice N)) _ _)))
  (isProp× (isPropΠ2 (λ _ _ → IsPoset.is-set (IsLattice.is-poset (LatticeStr.isLattice N)) _ _))
  (isProp× (isPropΠ2 (λ _ _ → IsPoset.is-set (IsLattice.is-poset (LatticeStr.isLattice N)) _ _))
  (isProp× (IsPoset.is-set (IsLattice.is-poset (LatticeStr.isLattice N)) _ _)
           (IsPoset.is-set (IsLattice.is-poset (LatticeStr.isLattice N)) _ _)))))

𝒮ᴰ-Lattice : DUARel (𝒮-Univ ℓ) (LatticeStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-Lattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsLatticeEquiv
    (fields:
      data[ _≤_  ∣ autoDUARel _ _ ∣ pres≤ ]
      data[ _∨l_ ∣ autoDUARel _ _ ∣ pres∨ ]
      data[ _∧l_ ∣ autoDUARel _ _ ∣ pres∧ ]
      data[ 0l   ∣ autoDUARel _ _ ∣ pres0 ]
      data[ 1l   ∣ autoDUARel _ _ ∣ pres1 ]
      prop[ isLattice ∣ (λ _ _ → isPropIsLattice _ _ _ _ _) ])
    where
    open LatticeStr
    open IsLattice
    open IsLatticeEquiv

LatticePath : (M N : Lattice ℓ ℓ') → LatticeEquiv M N ≃ (M ≡ N)
LatticePath = ∫ 𝒮ᴰ-Lattice .UARel.ua

-- an easier way of establishing an equivalence of lattices; poset equivs are lattice equivs
module _ {P : Lattice ℓ₀ ℓ₀'} {S : Lattice ℓ₁ ℓ₁'} (e : ⟨ P ⟩ ≃ ⟨ S ⟩) where
  private
    module P = LatticeStr (P .snd)
    module S = LatticeStr (S .snd)

    Ppos : PosetStr ℓ₀' ⟨ P ⟩
    Ppos = LatticeStr→PosetStr (P .snd)

    Spos : PosetStr ℓ₁' ⟨ S ⟩
    Spos = LatticeStr→PosetStr (S .snd)

  module _ (isPosetEquiv : IsPosetEquiv Ppos e Spos) where
    open LatticeStr
    open IsLatticeEquiv
    open IsLattice

    makeIsLatticeEquiv : IsLatticeEquiv (P .snd) e (S .snd)
    pres≤ makeIsLatticeEquiv = IsPosetEquiv.pres≤ isPosetEquiv
    pres∨ makeIsLatticeEquiv x y
      = isJoinUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∨l y))
                     (equivFun e x S.∨l equivFun e y)
                     (equivFun (IsPosetEquivRespectsJoin (e , isPosetEquiv) x y (x P.∨l y))
                               (is-join (isLattice (P .snd)) x y))
                     (is-join (isLattice (S .snd)) (equivFun e x) (equivFun e y))
    pres∧ makeIsLatticeEquiv x y
      = isMeetUnique (PosetStr.isPoset Spos)
                     (equivFun e x)
                     (equivFun e y)
                     (equivFun e (x P.∧l y))
                     (equivFun e x S.∧l equivFun e y)
                     (equivFun (IsPosetEquivRespectsMeet (e , isPosetEquiv) x y (x P.∧l y))
                               (is-meet (isLattice (P .snd)) x y))
                     (is-meet (isLattice (S .snd)) (equivFun e x) (equivFun e y))
    pres0 makeIsLatticeEquiv
      = isLeastUnique (PosetStr.isPoset Spos)
                      {P = ⟨ S ⟩ , id↪ ⟨ S ⟩}
                      (equivFun e P.0l)
                       S.0l
                      (λ x → subst (equivFun e P.0l S.≤_)
                                   (secEq e x)
                                   (equivFun (IsPosetEquiv.pres≤ isPosetEquiv P.0l (invEq e x))
                                             (P.is-least (invEq e x))))
                      (is-least (isLattice (S .snd)))
    pres1 makeIsLatticeEquiv
      = isGreatestUnique (PosetStr.isPoset Spos)
                         {P = ⟨ S ⟩ , id↪ ⟨ S ⟩}
                         (equivFun e P.1l)
                          S.1l
                         (λ x → subst (S._≤ equivFun e P.1l)
                                      (secEq e x)
                                      (equivFun (IsPosetEquiv.pres≤ isPosetEquiv (invEq e x) P.1l)
                                                (P.is-greatest (invEq e x))))
                         (is-greatest (isLattice (S .snd)))
