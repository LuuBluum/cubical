{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.MeetSemipseudolattice.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Poset.Mappings
open import Cubical.Relation.Binary.Order.Poset.Subset
open import Cubical.Relation.Binary.Order.Poset.Lattices.MeetSemipseudolattice.Base
open import Cubical.Relation.Binary.Order.Proset.Properties

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

module _
  (P : Poset ℓ ℓ)
  where
    open PosetDownset P
    private
      isP = PosetStr.isPoset (snd P)
      _≤_ = PosetStr._≤_ (snd P)
      prop = IsPoset.is-prop-valued isP
      trans = IsPoset.is-trans isP

    canonicalEmbeddingPrincipalDownsetIsResiduated : Type _
    canonicalEmbeddingPrincipalDownsetIsResiduated = ∀ x → isResiduated (x ↓ᴾ) P ((x ↓) .snd .fst)

    canonicalEmbeddingPrincipalDownsetIsResiduated→isPrincipalDownset∩ : canonicalEmbeddingPrincipalDownsetIsResiduated
                                                                       → ∀ x y → isPrincipalDownset P ((x ↓) ∩ₑ (y ↓))
    canonicalEmbeddingPrincipalDownsetIsResiduated→isPrincipalDownset∩ res x y
      = a ,
        isAntisym⊆ₑ ((x ↓) ∩ₑ (y ↓)) (a ↓)
          (λ z z∈∩ → equivFun (principalDownsetMembership P z a)
                              (grtst ((z , (invEq (principalDownsetMembership P z x)
                                                  (equivFun (∈ₑDist∩ₑ (x ↓) (y ↓) z) z∈∩ .fst))) ,
                                    ∣ (z , (invEq (principalDownsetMembership P z y)
                                                  (equivFun (∈ₑDist∩ₑ (x ↓) (y ↓) z) z∈∩ .snd))) , refl ∣₁)))
           λ z z∈a↓ → invEq (∈ₑDist∩ₑ (x ↓) (y ↓) z)
                            (equivFun (principalDownsetMembership P z x)
                                      (trans z a x (invEq (principalDownsetMembership P z a) z∈a↓) a≤x) ,
                             ∥₁.rec (isProp∈ₑ z (y ↓))
                                    (λ ((b , b≤y) , fib) → equivFun (principalDownsetMembership P z y)
                                                                    (trans z a y (invEq (principalDownsetMembership P z a) z∈a↓)
                                                                                 (subst (_≤ y) fib b≤y))) pre)
      where grt = isResiduated→hasDownsetGreatest (x ↓ᴾ) P ((x ↓) .snd .fst) (res x) y

            a = grt .fst .fst .fst
            a≤x = grt .fst .fst .snd

            pre = grt .fst .snd

            grtst = grt .snd

    isPrincipalDownset∩→canonicalEmbeddingPrincipalDownsetIsResiduated : (∀ x y → isPrincipalDownset P ((x ↓) ∩ₑ (y ↓)))
                                                                       → canonicalEmbeddingPrincipalDownsetIsResiduated
    isPrincipalDownset∩→canonicalEmbeddingPrincipalDownsetIsResiduated prin x
      = hasDownsetGreatest→IsIsotone→isResiduated (x ↓ᴾ) P ((x ↓) .snd .fst) grt is

      where is : IsIsotone ((x ↓ᴾ) .snd) ((x ↓) .snd .fst) (P .snd)
            IsIsotone.pres≤ is x y x≤y = x≤y

            grt : hasDownsetGreatest (x ↓ᴾ) P ((x ↓) .snd .fst)
            grt y = ((a , invEq (principalDownsetMembership P a x) a∈x↓) ,
                   ∣ (a , invEq (principalDownsetMembership P a y) a∈y↓) , refl ∣₁) ,
                     λ ((z , z≤x) , pre)
                     → ∥₁.rec (prop _ _)
                              (λ ((c , c≤y) , fib)
                               → grtst (z , equivFun (principalDownsetMembership P z x) z≤x ,
                                            equivFun (principalDownsetMembership P z y) (subst (_≤ y) fib c≤y))) pre
              where hasgrt = isPrincipalDownset→hasGreatest P ((x ↓) ∩ₑ (y ↓)) (prin x y)

                    a = hasgrt .fst .fst
                    a∈x↓ = hasgrt .fst .snd .fst
                    a∈y↓ = hasgrt .fst .snd .snd

                    grtst = hasgrt .snd

module _
  (P : Poset ℓ ℓ')
  where
    open PosetDownset P
    private
      isP = PosetStr.isPoset (snd P)
      _≤_ = PosetStr._≤_ (snd P)
      prop = IsPoset.is-prop-valued isP
      rfl = IsPoset.is-refl isP
      trans = IsPoset.is-trans isP

    isPrincipalDownset∩→IsMeetSemipseudolattice : (meet : (∀ x y → isPrincipalDownset P ((x ↓) ∩ₑ (y ↓))))
                                                → IsMeetSemipseudolattice _≤_ (λ x y → meet x y .fst)
    IsMeetSemipseudolattice.is-poset (isPrincipalDownset∩→IsMeetSemipseudolattice meet) = isP
    IsMeetSemipseudolattice.is-meet (isPrincipalDownset∩→IsMeetSemipseudolattice meet) x y z
      = propBiimpl→Equiv (prop _ _)
                         (isProp× (prop _ _) (prop _ _))
                         (λ z≤x∧y → trans z x∧y x z≤x∧y (invEq (principalDownsetMembership P x∧y x)
                                                                 (x∧y↓⊆x↓ x∧y (equivFun (principalDownsetMembership P x∧y x∧y)
                                                                                         (rfl x∧y)))) ,
                                     trans z x∧y y z≤x∧y (invEq (principalDownsetMembership P x∧y y)
                                                                 (x∧y↓⊆y↓ x∧y (equivFun (principalDownsetMembership P x∧y x∧y)
                                                                                         (rfl x∧y)))))
                          λ (z≤x , z≤y) → invEq (principalDownsetMembership P z x∧y)
                                                 (x↓∩y↓⊆x∧y↓ z (invEq (∈ₑDist∩ₑ (x ↓) (y ↓) z)
                                                                       (equivFun (principalDownsetMembership P z x) z≤x ,
                                                                        equivFun (principalDownsetMembership P z y) z≤y)))
      where x∧y = meet x y .fst

            x↓∩y↓⊆x∧y↓ = ≡→⊆ₑ ((x ↓) ∩ₑ (y ↓)) (x∧y ↓) (meet x y .snd) .fst
            x∧y↓⊆x↓∩y↓ = ≡→⊆ₑ ((x ↓) ∩ₑ (y ↓)) (x∧y ↓) (meet x y .snd) .snd
            x∧y↓⊆x↓ = equivFun (⊆ₑDist∩ₑ (x ↓) (y ↓) (x∧y ↓)) x∧y↓⊆x↓∩y↓ .fst
            x∧y↓⊆y↓ = equivFun (⊆ₑDist∩ₑ (x ↓) (y ↓) (x∧y ↓)) x∧y↓⊆x↓∩y↓ .snd

module _
  (L : MeetSemipseudolattice ℓ ℓ')
  where
    private
      P = MeetSemipseudolattice→Poset L
      _≤_ = MeetSemipseudolatticeStr._≤_ (snd L)
      _∧l_ = MeetSemipseudolatticeStr._∧l_ (snd L)

      isL = MeetSemipseudolatticeStr.isMeetSemipseudolattice (snd L)
      isP = PosetStr.isPoset (snd P)

      meet = IsMeetSemipseudolattice.is-meet isL
      rfl = IsPoset.is-refl isP
    open PosetDownset P

    MeetSemipseudolattice→isPrincipalDownset∩ : ∀ x y → isPrincipalDownset P ((x ↓) ∩ₑ (y ↓))
    MeetSemipseudolattice→isPrincipalDownset∩ x y
      = (x ∧l y) ,
        (isAntisym⊆ₑ ((x ↓) ∩ₑ (y ↓))
                     ((x ∧l y) ↓)
                     (λ z z∈x↓∩y↓ → equivFun (principalDownsetMembership P z (x ∧l y))
                                             (invEq (meet x y z)
                                                    ((invEq (principalDownsetMembership P z x)
                                                            (equivFun (∈ₑDist∩ₑ (x ↓) (y ↓) z) z∈x↓∩y↓ .fst)) ,
                                                     (invEq (principalDownsetMembership P z y)
                                                            (equivFun (∈ₑDist∩ₑ (x ↓) (y ↓) z) z∈x↓∩y↓ .snd)))))
                     (invEq (⊆ₑDist∩ₑ (x ↓) (y ↓) ((x ∧l y) ↓))
                            ((principalDownsetInclusion P (x ∧l y) x
                                                        (equivFun (meet x y (x ∧l y))
                                                                  (rfl (x ∧l y)) .fst)) ,
                             (principalDownsetInclusion P (x ∧l y) y
                                                        (equivFun (meet x y (x ∧l y))
                                                                  (rfl (x ∧l y)) .snd)))))
