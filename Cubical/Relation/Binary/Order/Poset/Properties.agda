{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Poset.Properties where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Proset
open import Cubical.Relation.Binary.Order.Quoset.Base

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' ℓ₀ ℓ₀' ℓ₁ ℓ₁' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→isProset : IsPoset R → IsProset R
  isPoset→isProset poset = isproset
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  isPosetDecidable→Discrete : IsPoset R → isDecidable R → Discrete A
  isPosetDecidable→Discrete pos dec a b with dec a b
  ... | no ¬Rab = no (λ a≡b → ¬Rab (subst (R a) a≡b (IsPoset.is-refl pos a)))
  ... | yes Rab with dec b a
  ...       | no ¬Rba = no (λ a≡b → ¬Rba (subst (λ x → R x a) a≡b
                                         (IsPoset.is-refl pos a)))
  ...       | yes Rba = yes (IsPoset.is-antisym pos a b Rab Rba)

  private
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

  isPoset→isQuosetIrreflKernel : IsPoset R → IsQuoset (IrreflKernel R)
  isPoset→isQuosetIrreflKernel poset
    = isquoset (IsPoset.is-set poset)
                    (λ a b → isProp× (IsPoset.is-prop-valued poset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsPoset.is-trans poset)
                                 (IsPoset.is-antisym poset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsPoset.is-trans poset)
                                                           (IsPoset.is-antisym poset)))

  isPosetDecidable→isQuosetDecidable : IsPoset R → isDecidable R → isDecidable (IrreflKernel R)
  isPosetDecidable→isQuosetDecidable pos dec a b with dec a b
  ... | no ¬Rab = no λ { (Rab , _) → ¬Rab Rab }
  ... | yes Rab with (isPosetDecidable→Discrete pos dec) a b
  ...       | yes a≡b = no λ { (_ , ¬a≡b) → ¬a≡b a≡b }
  ...       | no a≢b = yes (Rab , a≢b)

  isPosetInduced : IsPoset R → (B : Type ℓ'') → (f : B ↪ A) → IsPoset (InducedRelation R (B , f))
  isPosetInduced pos B (f , emb)
    = isposet (Embedding-into-isSet→isSet (f , emb) (IsPoset.is-set pos))
              (λ a b → IsPoset.is-prop-valued pos (f a) (f b))
              (λ a → IsPoset.is-refl pos (f a))
              (λ a b c → IsPoset.is-trans pos (f a) (f b) (f c))
              λ a b a≤b b≤a → isEmbedding→Inj emb a b
                (IsPoset.is-antisym pos (f a) (f b) a≤b b≤a)

  isPosetDual : IsPoset R → IsPoset (Dual R)
  isPosetDual pos
    = isposet (IsPoset.is-set pos)
              (λ a b → IsPoset.is-prop-valued pos b a)
              (IsPoset.is-refl pos)
              (λ a b c Rab Rbc → IsPoset.is-trans pos c b a Rbc Rab)
              (λ a b Rab Rba → IsPoset.is-antisym pos a b Rba Rab)

Poset→Proset : Poset ℓ ℓ' → Proset ℓ ℓ'
Poset→Proset (_ , pos)
  = proset _ (PosetStr._≤_ pos)
             (isPoset→isProset (PosetStr.isPoset pos))

Poset→Quoset : Poset ℓ ℓ' → Quoset ℓ (ℓ-max ℓ ℓ')
Poset→Quoset (_ , pos)
  = quoset _ (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
             (isPoset→isQuosetIrreflKernel (PosetStr.isPoset pos))

DualPoset : Poset ℓ ℓ' → Poset ℓ ℓ'
DualPoset (_ , pos)
  = poset _ (BinaryRelation.Dual (PosetStr._≤_ pos))
            (isPosetDual (PosetStr.isPoset pos))

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (pos : IsPoset _≤_)
  where

  private
      pre = isPoset→isProset pos

      set = IsPoset.is-set pos

      prop = IsPoset.is-prop-valued pos

      rfl = IsPoset.is-refl pos

      anti = IsPoset.is-antisym pos

      trans = IsPoset.is-trans pos

  module _
    {P : Embedding A ℓ''}
    where

    private
      toA = fst (snd P)

      emb = snd (snd P)

    isLeast→ContrMinimal : ∀ n → isLeast pre P n  → ∀ m → isMinimal pre P m → n ≡ m
    isLeast→ContrMinimal n isln m ismm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isln m) (ismm n (isln m)))

    isGreatest→ContrMaximal : ∀ n → isGreatest pre P n → ∀ m → isMaximal pre P m → n ≡ m
    isGreatest→ContrMaximal n isgn m ismm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (ismm n (isgn m)) (isgn m))

    isLeastUnique : ∀ n m → isLeast pre P n → isLeast pre P m → n ≡ m
    isLeastUnique n m isln islm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isln m) (islm n))

    isGreatestUnique : ∀ n m → isGreatest pre P n → isGreatest pre P m → n ≡ m
    isGreatestUnique n m isgn isgm
      = isEmbedding→Inj emb n m (anti (toA n) (toA m) (isgm n) (isgn m))

    LeastUnique : (n m : Least pre P) → n ≡ m
    LeastUnique (n , ln) (m , lm) = Σ≡Prop (λ _ → isPropIsLeast pre P _) (isLeastUnique n m ln lm)

    GreatestUnique : (n m : Greatest pre P) → n ≡ m
    GreatestUnique (n , gn) (m , gm) = Σ≡Prop (λ _ → isPropIsGreatest pre P _) (isGreatestUnique n m gn gm)

  module _
    {B : Type ℓ''}
    {P : B → A}
    where

    isInfimum→ContrMaximalLowerBound : ∀ n → isInfimum pre P n
                                     → ∀ m → isMaximalLowerBound pre P m
                                     → n ≡ m
    isInfimum→ContrMaximalLowerBound n (isln , isglbn) m (islm , ismlbm)
      = anti n m (ismlbm (n , isln) (isglbn (m , islm))) (isglbn (m , islm))

    isSupremum→ContrMinimalUpperBound : ∀ n → isSupremum pre P n
                                      → ∀ m → isMinimalUpperBound pre P m
                                      → n ≡ m
    isSupremum→ContrMinimalUpperBound n (isun , islubn) m (isum , ismubm)
      = anti n m (islubn (m , isum)) (ismubm (n , isun) (islubn (m , isum)))

    isInfimumUnique : ∀ n m → isInfimum pre P n → isInfimum pre P m → n ≡ m
    isInfimumUnique n m (isln , infn) (islm , infm)
      = anti n m (infm (n , isln)) (infn (m , islm))

    isSupremumUnique : ∀ n m → isSupremum pre P n → isSupremum pre P m → n ≡ m
    isSupremumUnique n m (isun , supn) (isum , supm)
      = anti n m (supn (m , isum)) (supm (n , isun))

    InfimumUnique : (n m : Infimum pre P) → n ≡ m
    InfimumUnique (n , infn) (m , infm) = Σ≡Prop (λ _ → isPropIsInfimum pre P _)
                                                  (isInfimumUnique n m infn infm)

    SupremumUnique : (n m : Supremum pre P) → n ≡ m
    SupremumUnique (n , supn) (m , supm) = Σ≡Prop (λ _ → isPropIsSupremum pre P _)
                                                   (isSupremumUnique n m supn supm)

  isMeetUnique : ∀ a b x y → isMeet pre a b x → isMeet pre a b y → x ≡ y
  isMeetUnique a b x y infx infy = anti x y x≤y y≤x
    where x≤y : x ≤ y
          x≤y = invEq (infy x) (infx x .fst (rfl x))

          y≤x : y ≤ x
          y≤x = invEq (infx y) (infy y .fst (rfl y))

  isJoinUnique : ∀ a b x y → isJoin pre a b x → isJoin pre a b y → x ≡ y
  isJoinUnique a b x y supx supy = anti x y x≤y y≤x
          where x≤y : x ≤ y
                x≤y = invEq (supx y) (supy y .fst (rfl y))

                y≤x : y ≤ x
                y≤x = invEq (supy x) (supx x .fst (rfl x))

  MeetUnique : ∀ a b → (x y : Meet pre a b) → x ≡ y
  MeetUnique a b (x , mx) (y , my) = Σ≡Prop (isPropIsMeet pre a b)
                                            (isMeetUnique a b x y mx my)

  JoinUnique : ∀ a b → (x y : Join pre a b) → x ≡ y
  JoinUnique a b (x , jx) (y , jy) = Σ≡Prop (isPropIsJoin pre a b)
                                            (isJoinUnique a b x y jx jy)

  order≃meet : ∀ a b a∧b
             → isMeet pre a b a∧b
             → (a ≤ b) ≃ (a ≡ a∧b)
  order≃meet a b a∧b funa∧b
    = propBiimpl→Equiv (prop a b)
                       (set a a∧b)
                       (λ a≤b → anti a a∧b (invEq (funa∧b a) (rfl a , a≤b))
                                            (funa∧b a∧b .fst (rfl a∧b) .fst))
                        λ a≡a∧b → subst (_≤ b) (sym a≡a∧b)
                                         (funa∧b a∧b .fst (rfl a∧b) .snd)

  order≃join : ∀ a b a∨b
             → isJoin pre a b a∨b
             → (a ≤ b) ≃ (b ≡ a∨b)
  order≃join a b a∨b funa∨b
    = propBiimpl→Equiv (prop a b)
                       (set b a∨b)
                       (λ a≤b → anti b a∨b (funa∨b a∨b .fst (rfl a∨b) .snd)
                                            (invEq (funa∨b b) (a≤b , rfl b)))
                        λ b≡a∨b → subst (a ≤_) (sym b≡a∨b)
                                        (funa∨b a∨b .fst (rfl a∨b) .fst)

-- Equivalences of posets respect meets and joins
IsPosetEquivRespectsMeet : {P : Poset ℓ₀ ℓ₀'} {S : Poset ℓ₁ ℓ₁'} (e : PosetEquiv P S)
                        → ∀ a b a∧b
                        → isMeet (isPoset→isProset (PosetStr.isPoset (P .snd))) a b a∧b
                        ≃ isMeet (isPoset→isProset (PosetStr.isPoset (S .snd)))
                                 (equivFun (e .fst) a)
                                 (equivFun (e .fst) b)
                                 (equivFun (e .fst) a∧b)
IsPosetEquivRespectsMeet {P = P} {S = S} (e , posEq) a b a∧b
  = propBiimpl→Equiv (isPropIsMeet proP a b a∧b)
                     (isPropIsMeet proS (equivFun e a) (equivFun e b) (equivFun e a∧b))
                     (λ meet x
                       → IsPosetEquiv.pres≤⁻ posEq x (equivFun e a∧b) ∙ₑ
                         substEquiv (invEq e x ≤P_) (retEq e a∧b) ∙ₑ
                         meet (invEq e x) ∙ₑ
                         ≃-× (IsPosetEquiv.pres≤ posEq (invEq e x) a ∙ₑ
                              substEquiv (_≤S equivFun e a) (secEq e x))
                             (IsPosetEquiv.pres≤ posEq (invEq e x) b ∙ₑ
                              substEquiv (_≤S equivFun e b) (secEq e x)))
                      λ meet x
                       → IsPosetEquiv.pres≤ posEq x a∧b ∙ₑ
                         meet (equivFun e x) ∙ₑ
                         ≃-× (IsPosetEquiv.pres≤⁻ posEq (equivFun e x) (equivFun e a) ∙ₑ
                               subst2Equiv _≤P_ (retEq e x) (retEq e a))
                             (IsPosetEquiv.pres≤⁻ posEq (equivFun e x) (equivFun e b) ∙ₑ
                               subst2Equiv _≤P_ (retEq e x) (retEq e b))
  where _≤P_ = PosetStr._≤_ (P .snd)
        _≤S_ = PosetStr._≤_ (S .snd)

        posP = PosetStr.isPoset (P .snd)
        posS = PosetStr.isPoset (S .snd)

        proP = isPoset→isProset posP
        proS = isPoset→isProset posS

IsPosetEquivRespectsJoin : {P : Poset ℓ₀ ℓ₀'} {S : Poset ℓ₁ ℓ₁'} (e : PosetEquiv P S)
                        → ∀ a b a∨b
                        → isJoin (isPoset→isProset (PosetStr.isPoset (P .snd))) a b a∨b
                        ≃ isJoin (isPoset→isProset (PosetStr.isPoset (S .snd)))
                                 (equivFun (e .fst) a)
                                 (equivFun (e .fst) b)
                                 (equivFun (e .fst) a∨b)

IsPosetEquivRespectsJoin {P = P} {S = S} (e , posEq) a b a∨b
  = propBiimpl→Equiv (isPropIsJoin proP a b a∨b)
                     (isPropIsJoin proS (equivFun e a) (equivFun e b) (equivFun e a∨b))
                     (λ join x
                       → IsPosetEquiv.pres≤⁻ posEq (equivFun e a∨b) x ∙ₑ
                         substEquiv (_≤P invEq e x) (retEq e a∨b) ∙ₑ
                         join (invEq e x) ∙ₑ
                         ≃-× (IsPosetEquiv.pres≤ posEq a (invEq e x) ∙ₑ
                               substEquiv (equivFun e a ≤S_) (secEq e x))
                              (IsPosetEquiv.pres≤ posEq b (invEq e x) ∙ₑ
                               substEquiv (equivFun e b ≤S_) (secEq e x)))
                      λ join x
                       → IsPosetEquiv.pres≤ posEq a∨b x ∙ₑ
                         join (equivFun e x) ∙ₑ
                         ≃-× (IsPosetEquiv.pres≤⁻ posEq (equivFun e a) (equivFun e x) ∙ₑ
                               subst2Equiv _≤P_ (retEq e a) (retEq e x))
                              (IsPosetEquiv.pres≤⁻ posEq (equivFun e b) (equivFun e x) ∙ₑ
                               subst2Equiv _≤P_ (retEq e b) (retEq e x))
  where _≤P_ = PosetStr._≤_ (P .snd)
        _≤S_ = PosetStr._≤_ (S .snd)

        posP = PosetStr.isPoset (P .snd)
        posS = PosetStr.isPoset (S .snd)

        proP = isPoset→isProset posP
        proS = isPoset→isProset posS
