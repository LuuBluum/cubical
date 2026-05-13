{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Lattices.JoinSemipseudolattice.Properties where

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
open import Cubical.Relation.Binary.Order.Poset.Lattices.JoinSemipseudolattice.Base
open import Cubical.Relation.Binary.Order.Proset.Properties

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

module _
  (P : Poset ℓ ℓ)
  where
    open PosetUpset P
    private
      isP = PosetStr.isPoset (snd P)
      _≤_ = PosetStr._≤_ (snd P)
      prop = IsPoset.is-prop-valued isP
      trans = IsPoset.is-trans isP

    canonicalEmbeddingPrincipalUpsetIsDualResiduated : Type _
    canonicalEmbeddingPrincipalUpsetIsDualResiduated = ∀ x → isDualResiduated (x ↑ᴾ) P ((x ↑) .snd .fst)

    canonicalEmbeddingPrincipalUpsetIsDualResiduated→isPrincipalUpset∩ : canonicalEmbeddingPrincipalUpsetIsDualResiduated
                                                                       → ∀ x y → isPrincipalUpset P ((x ↑) ∩ₑ (y ↑))
    canonicalEmbeddingPrincipalUpsetIsDualResiduated→isPrincipalUpset∩ res x y
      = a ,
        isAntisym⊆ₑ ((x ↑) ∩ₑ (y ↑)) (a ↑)
          (λ z z∈∩ → equivFun (principalUpsetMembership P a z)
                              (least ((z , (invEq (principalUpsetMembership P x z)
                                                  (equivFun (∈ₑDist∩ₑ (x ↑) (y ↑) z) z∈∩ .fst))) ,
                                           ∣ (z , (invEq (principalUpsetMembership P y z)
                                                         (equivFun (∈ₑDist∩ₑ (x ↑) (y ↑) z) z∈∩ .snd))) ,
                                             refl ∣₁)))
           λ z z∈a↑ → invEq (∈ₑDist∩ₑ (x ↑) (y ↑) z)
                            ((equivFun (principalUpsetMembership P x z)
                                       (trans x a z x≤a (invEq (principalUpsetMembership P a z) z∈a↑))) ,
                            (∥₁.rec (isProp∈ₑ z (y ↑)) (λ ((b , y≤b) , fib)
                                    → equivFun (principalUpsetMembership P y z)
                                               (trans y a z (subst (y ≤_) fib y≤b)
                                                            (invEq (principalUpsetMembership P a z) z∈a↑))) pre))
      where lst = isDualResiduated→hasUpsetLeast (x ↑ᴾ) P ((x ↑) .snd .fst) (res x) y

            a = lst .fst .fst .fst
            x≤a = lst .fst .fst .snd

            pre = lst .fst .snd

            least = lst .snd

    isPrincipalUpset∩→canonicalEmbeddingPrincipalUpsetIsDualResiduated : (∀ x y → isPrincipalUpset P ((x ↑) ∩ₑ (y ↑)))
                                                                       → canonicalEmbeddingPrincipalUpsetIsDualResiduated
    isPrincipalUpset∩→canonicalEmbeddingPrincipalUpsetIsDualResiduated prin x
      = hasUpsetLeast→IsIsotone→isDualResiduated (x ↑ᴾ) P ((x ↑) .snd .fst) lst is

      where is : IsIsotone ((x ↑ᴾ) .snd) ((x ↑) .snd .fst) (P .snd)
            IsIsotone.pres≤ is x y x≤y = x≤y

            lst : hasUpsetLeast (x ↑ᴾ) P ((x ↑) .snd .fst)
            lst y = ((a , invEq (principalUpsetMembership P x a) a∈x↑) ,
                    ∣ (a , invEq (principalUpsetMembership P y a) a∈y↑) , refl ∣₁) ,
                    (λ ((z , x≤z) , pre) → ∥₁.rec (prop _ _)
                                           (λ ((b , y≤b) , fib) → least (z , equivFun (principalUpsetMembership P x z) x≤z ,
                                                                             equivFun (principalUpsetMembership P y z)
                                                                                      (subst (y ≤_) fib y≤b))) pre)
              where haslst = isPrincipalUpset→hasLeast P ((x ↑) ∩ₑ (y ↑)) (prin x y)

                    a = haslst .fst .fst
                    a∈x↑ = haslst .fst .snd .fst
                    a∈y↑ = haslst .fst .snd .snd

                    least = haslst .snd

module _
  (P : Poset ℓ ℓ')
  where
    open PosetUpset P
    private
      isP = PosetStr.isPoset (snd P)
      _≤_ = PosetStr._≤_ (snd P)
      prop = IsPoset.is-prop-valued isP
      rfl = IsPoset.is-refl isP
      trans = IsPoset.is-trans isP

    isPrincipalUpset∩→IsJoinSemipseudolattice : (join : (∀ x y → isPrincipalUpset P ((x ↑) ∩ₑ (y ↑))))
                                                → IsJoinSemipseudolattice _≤_ (λ x y → join x y .fst)
    IsJoinSemipseudolattice.is-poset (isPrincipalUpset∩→IsJoinSemipseudolattice join) = isP
    IsJoinSemipseudolattice.is-join (isPrincipalUpset∩→IsJoinSemipseudolattice join) x y z
      = propBiimpl→Equiv (prop _ _)
                         (isProp× (prop _ _) (prop _ _))
                          (λ x∨y≤z → (invEq (principalUpsetMembership P x z)
                                             (x∨y↑⊆x↑ z (equivFun (principalUpsetMembership P x∨y z) x∨y≤z))) ,
                                      (invEq (principalUpsetMembership P y z)
                                             (x∨y↑⊆y↑ z (equivFun (principalUpsetMembership P x∨y z) x∨y≤z))))
                          λ (x≤z , y≤z) → invEq (principalUpsetMembership P x∨y z)
                                                 (x↑∩y↑⊆x∨y↑ z (invEq (∈ₑDist∩ₑ (x ↑) (y ↑) z)
                                                                       (equivFun (principalUpsetMembership P x z) x≤z ,
                                                                        equivFun (principalUpsetMembership P y z) y≤z)))
      where x∨y = join x y .fst

            x↑∩y↑⊆x∨y↑ = ≡→⊆ₑ ((x ↑) ∩ₑ (y ↑)) (x∨y ↑) (join x y .snd) .fst
            x∨y↑⊆x↑∩y↑ = ≡→⊆ₑ ((x ↑) ∩ₑ (y ↑)) (x∨y ↑) (join x y .snd) .snd
            x∨y↑⊆x↑ = equivFun (⊆ₑDist∩ₑ (x ↑) (y ↑) (x∨y ↑)) x∨y↑⊆x↑∩y↑ .fst
            x∨y↑⊆y↑ = equivFun (⊆ₑDist∩ₑ (x ↑) (y ↑) (x∨y ↑)) x∨y↑⊆x↑∩y↑ .snd

module _
  (L : JoinSemipseudolattice ℓ ℓ')
  where
    private
      P = JoinSemipseudolattice→Poset L
      _≤_ = JoinSemipseudolatticeStr._≤_ (snd L)
      _∨l_ = JoinSemipseudolatticeStr._∨l_ (snd L)

      isL = JoinSemipseudolatticeStr.isJoinSemipseudolattice (snd L)
      isP = PosetStr.isPoset (snd P)

      join = IsJoinSemipseudolattice.is-join isL
      rfl = IsPoset.is-refl isP
    open PosetUpset P

    JoinSemipseudolattice→isPrincipalUpset∩ : ∀ x y → isPrincipalUpset P ((x ↑) ∩ₑ (y ↑))
    JoinSemipseudolattice→isPrincipalUpset∩ x y
      = (x ∨l y) ,
        (isAntisym⊆ₑ ((x ↑) ∩ₑ (y ↑))
                     ((x ∨l y) ↑)
                     (λ z z∈x↑∩y↑ → equivFun (principalUpsetMembership P (x ∨l y) z)
                                             (invEq (join x y z)
                                                    (invEq (principalUpsetMembership P x z)
                                                           (equivFun (∈ₑDist∩ₑ (x ↑) (y ↑) z) z∈x↑∩y↑ .fst) ,
                                                     invEq (principalUpsetMembership P y z)
                                                           (equivFun (∈ₑDist∩ₑ (x ↑) (y ↑) z) z∈x↑∩y↑ .snd))))
                     (invEq (⊆ₑDist∩ₑ (x ↑) (y ↑) ((x ∨l y) ↑)) ((principalUpsetInclusion P x (x ∨l y) x≤x∨y) ,
                                                                  (principalUpsetInclusion P y (x ∨l y) y≤x∨y))))
      where x≤x∨y : x ≤ (x ∨l y)
            x≤x∨y = equivFun (join x y (x ∨l y)) (rfl (x ∨l y)) .fst

            y≤x∨y : y ≤ (x ∨l y)
            y≤x∨y = equivFun (join x y (x ∨l y)) (rfl (x ∨l y)) .snd
