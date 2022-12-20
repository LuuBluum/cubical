{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Order.Properties where

open import Cubical.Data.Sum renaming (rec to ⊎-rec ; map to ⊎-map)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty.Base renaming (rec to ⊥-rec)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation renaming (map to ∥₁-map ; rec to ∥₁-rec)

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Apartness
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Loset
open import Cubical.Relation.Binary.Order.Preorder
open import Cubical.Relation.Binary.Order.StrictPoset
open import Cubical.Relation.Binary.Order.StrictLoset

open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level

module _
  {A : Type ℓ}
  {R : Rel A A ℓ'}
  where

  open BinaryRelation

  isPoset→isPreorder : IsPoset R → IsPreorder R
  isPoset→isPreorder poset = ispreorder
                             (IsPoset.is-set poset)
                             (IsPoset.is-prop-valued poset)
                             (IsPoset.is-refl poset)
                             (IsPoset.is-trans poset)

  isLoset→isPoset : IsLoset R → IsPoset R
  isLoset→isPoset loset = isposet
                          (IsLoset.is-set loset)
                          (IsLoset.is-prop-valued loset)
                          (IsLoset.is-refl loset)
                          (IsLoset.is-trans loset)
                          (IsLoset.is-antisym loset)

  isStrictLoset→isStrictPoset : IsStrictLoset R → IsStrictPoset R
  isStrictLoset→isStrictPoset sloset = isstrictposet
                                       (IsStrictLoset.is-set sloset)
                                       (IsStrictLoset.is-prop-valued sloset)
                                       (IsStrictLoset.is-irrefl sloset)
                                       (IsStrictLoset.is-trans sloset)
                                       (IsStrictLoset.is-asym sloset)

  private
    -- Some lemmas that otherwise repeat several times
    transirrefl : isTrans R → isAntisym R → isTrans (IrreflKernel R)
    transirrefl trans anti a b c (Rab , ¬a≡b) (Rbc , ¬b≡c)
      = trans a b c Rab Rbc
      , λ a≡c → ¬a≡b (anti a b Rab (subst (R b) (sym a≡c) Rbc))

    transrefl : isTrans R → isTrans (ReflClosure R)
    transrefl trans a b c (inl Rab) (inl Rbc) = inl (trans a b c Rab Rbc)
    transrefl trans a b c (inl Rab) (inr b≡c) = inl (subst (R a) b≡c Rab)
    transrefl trans a b c (inr a≡b) (inl Rbc) = inl (subst (λ z → R z c) (sym a≡b) Rbc)
    transrefl trans a b c (inr a≡b) (inr b≡c) = inr (a≡b ∙ b≡c)

    antisym : isIrrefl R → isTrans R → isAntisym (ReflClosure R)
    antisym irr trans a b (inl Rab) (inl Rba) = ⊥-rec (irr a (trans a b a Rab Rba))
    antisym irr trans a b (inl _) (inr b≡a) = sym b≡a
    antisym irr trans a b (inr a≡b) _ = a≡b

  isPoset→isStrictPosetIrreflKernel : IsPoset R → IsStrictPoset (IrreflKernel R)
  isPoset→isStrictPosetIrreflKernel poset
    = isstrictposet (IsPoset.is-set poset)
                    (λ a b → isProp× (IsPoset.is-prop-valued poset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsPoset.is-trans poset)
                                 (IsPoset.is-antisym poset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsPoset.is-trans poset)
                                                           (IsPoset.is-antisym poset)))

  isLoset→isStrictLosetIrreflKernel : IsLoset R → IsStrictLoset (IrreflKernel R)
  isLoset→isStrictLosetIrreflKernel loset
    = isstrictloset (IsLoset.is-set loset)
                    (λ a b → isProp× (IsLoset.is-prop-valued loset a b)
                                     (isProp¬ (a ≡ b)))
                    (isIrreflIrreflKernel R)
                    (transirrefl (IsLoset.is-trans loset)
                                 (IsLoset.is-antisym loset))
                    (isIrrefl×isTrans→isAsym (IrreflKernel R)
                                             (isIrreflIrreflKernel R
                                             , transirrefl (IsLoset.is-trans loset)
                                                           (IsLoset.is-antisym loset)))
                    (isConnectedStronglyConnectedIrreflKernel R
                      (IsLoset.is-strongly-connected loset))

  isStrictPoset→isPosetReflClosure : IsStrictPoset R → IsPoset (ReflClosure R)
  isStrictPoset→isPosetReflClosure strictposet
    = isposet (IsStrictPoset.is-set strictposet)
              (λ a b → isProp⊎ (IsStrictPoset.is-prop-valued strictposet a b)
                               (IsStrictPoset.is-set strictposet a b)
                                 λ Rab a≡b
                                   → IsStrictPoset.is-irrefl strictposet a (subst (R a)
                                                                           (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsStrictPoset.is-trans strictposet))
              (antisym (IsStrictPoset.is-irrefl strictposet)
                       (IsStrictPoset.is-trans strictposet))

  isStrictLoset→isLosetReflClosure : Discrete A → IsStrictLoset R → IsLoset (ReflClosure R)
  isStrictLoset→isLosetReflClosure disc strictloset
    = isloset (IsStrictLoset.is-set strictloset)
              (λ a b → isProp⊎ (IsStrictLoset.is-prop-valued strictloset a b)
                               (IsStrictLoset.is-set strictloset a b)
                               λ Rab a≡b
                                 → IsStrictLoset.is-irrefl strictloset a (subst (R a)
                                                                         (sym a≡b) Rab))
              (isReflReflClosure R)
              (transrefl (IsStrictLoset.is-trans strictloset))
              (antisym (IsStrictLoset.is-irrefl strictloset)
                       (IsStrictLoset.is-trans strictloset))
              λ a b → decRec (λ a≡b → ∣ inl (inr a≡b) ∣₁)
                             (λ ¬a≡b → ∥₁-map (⊎-map (λ Rab → inl Rab) λ Rba → inl Rba)
                             (IsStrictLoset.is-connected strictloset a b ¬a≡b)) (disc a b)

  isPreorder→isEquivRelSymKernel : IsPreorder R → isEquivRel (SymKernel R)
  isPreorder→isEquivRelSymKernel preorder
    = equivRel (λ a → (IsPreorder.is-refl preorder a)
                    , (IsPreorder.is-refl preorder a))
               (isSymSymKernel R)
               (λ a b c (Rab , Rba) (Rbc , Rcb)
                 → IsPreorder.is-trans preorder a b c Rab Rbc
                 , IsPreorder.is-trans preorder c b a Rcb Rba)

  isPreorder→isStrictPosetAsymKernel : IsPreorder R → IsStrictPoset (AsymKernel R)
  isPreorder→isStrictPosetAsymKernel preorder
    = isstrictposet (IsPreorder.is-set preorder)
                    (λ a b → isProp× (IsPreorder.is-prop-valued preorder a b) (isProp¬ (R b a)))
                    (λ a (Raa , ¬Raa) → ¬Raa (IsPreorder.is-refl preorder a))
                    (λ a b c (Rab , ¬Rba) (Rbc , ¬Rcb)
                      → IsPreorder.is-trans preorder a b c Rab Rbc
                      , λ Rca → ¬Rcb (IsPreorder.is-trans preorder c a b Rca Rab))
                    (isAsymAsymKernel R)

  isStrictPoset→isApartnessSymClosure : IsStrictPoset R → isWeaklyLinear R → IsApartness (SymClosure R)
  isStrictPoset→isApartnessSymClosure strictposet weak
    = isapartness (IsStrictPoset.is-set strictposet)
                  (λ a b → isProp⊎ (IsStrictPoset.is-prop-valued strictposet a b)
                                   (IsStrictPoset.is-prop-valued strictposet b a)
                                   (IsStrictPoset.is-asym strictposet a b))
                  (λ a x → ⊎-rec (IsStrictPoset.is-irrefl strictposet a)
                                 (IsStrictPoset.is-irrefl strictposet a) x)
                  (λ a b c x → ⊎-rec (λ Rab → ∥₁-map (⊎-map (λ Rac → inl Rac)
                                                             (λ Rcb → inr Rcb))
                                                      (weak a b c Rab))
                                     (λ Rba → ∥₁-rec squash₁ (λ y → ∣ ⊎-rec (λ Rbc → inr (inl Rbc))
                                                                            (λ Rca → inl (inr Rca)) y ∣₁)
                                                                     (weak b a c Rba)) x)
                  (isSymSymClosure R)

Poset→Preorder : Poset ℓ ℓ' → Preorder ℓ ℓ'
Poset→Preorder (_ , pos) = _ , preorderstr (PosetStr._≤_ pos)
                                           (isPoset→isPreorder (PosetStr.isPoset pos))

Loset→Poset : Loset ℓ ℓ' → Poset ℓ ℓ'
Loset→Poset (_ , los) = _ , posetstr (LosetStr._≤_ los)
                                     (isLoset→isPoset (LosetStr.isLoset los))

StrictLoset→StrictPoset : StrictLoset ℓ ℓ' → StrictPoset ℓ ℓ'
StrictLoset→StrictPoset (_ , strictlos)
  = _ , strictposetstr (StrictLosetStr._<_ strictlos)
                       (isStrictLoset→isStrictPoset (StrictLosetStr.isStrictLoset strictlos))

Poset→StrictPoset : Poset ℓ ℓ' → StrictPoset ℓ (ℓ-max ℓ ℓ')
Poset→StrictPoset (_ , pos)
  = _ , strictposetstr (BinaryRelation.IrreflKernel (PosetStr._≤_ pos))
                       (isPoset→isStrictPosetIrreflKernel (PosetStr.isPoset pos))

Loset→StrictLoset : Loset ℓ ℓ' → StrictLoset ℓ (ℓ-max ℓ ℓ')
Loset→StrictLoset (_ , los)
  = _ , strictlosetstr (BinaryRelation.IrreflKernel (LosetStr._≤_ los))
                       (isLoset→isStrictLosetIrreflKernel (LosetStr.isLoset los))

StrictPoset→Poset : StrictPoset ℓ ℓ' → Poset ℓ (ℓ-max ℓ ℓ')
StrictPoset→Poset (_ , strictpos)
  = _ , posetstr (BinaryRelation.ReflClosure (StrictPosetStr._<_ strictpos))
                 (isStrictPoset→isPosetReflClosure (StrictPosetStr.isStrictPoset strictpos))

StrictLoset→Loset : (strictlos : StrictLoset ℓ ℓ')
                  → Discrete (fst strictlos)
                  → Loset ℓ (ℓ-max ℓ ℓ')
StrictLoset→Loset (_ , strictlos) disc
  = _ , losetstr (BinaryRelation.ReflClosure (StrictLosetStr._<_ strictlos))
                 (isStrictLoset→isLosetReflClosure disc
                                                   (StrictLosetStr.isStrictLoset strictlos))

Preorder→StrictPoset : Preorder ℓ ℓ' → StrictPoset ℓ ℓ'
Preorder→StrictPoset (_ , pre)
  = _ , strictposetstr (BinaryRelation.AsymKernel (PreorderStr._≲_ pre))
                       (isPreorder→isStrictPosetAsymKernel (PreorderStr.isPreorder pre))

StrictPoset→Apartness : (R : StrictPoset ℓ ℓ')
                      → BinaryRelation.isWeaklyLinear (StrictPosetStr._<_ (snd R))
                      → Apartness ℓ ℓ'
StrictPoset→Apartness (_ , strictpos) weak
  = _ , apartnessstr (BinaryRelation.SymClosure (StrictPosetStr._<_ strictpos))
                     (isStrictPoset→isApartnessSymClosure
                       (StrictPosetStr.isStrictPoset strictpos) weak)

module _
  {A : Type ℓ}
  (_≲_ : Rel A A ℓ')
  where

  module _
    (P : A → Type ℓ'')
    where

    private
      induced : Type (ℓ-max ℓ ℓ'')
      induced = Σ[ x ∈ A ] P x

    isMinimal : (n : induced) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMinimal (n , _) = ((x : induced) → ((fst x) ≲ n → n ≲ (fst x)))

    Minimal : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Minimal = Σ[ n ∈ induced ] isMinimal n

    isMaximal : (n : induced) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMaximal (n , _) = ((x : induced) → (n ≲ (fst x) → (fst x) ≲ n))

    Maximal : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    Maximal = Σ[ n ∈ induced ] isMaximal n

    isLeast : (n : induced) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isLeast (n , _) = ((x : induced) → n ≲ (fst x))

    isGreatest : (n : induced) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isGreatest (n , _) = ((x : induced) → (fst x) ≲ n)

    isLowerBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isLowerBound n = (x : induced) → n ≲ (fst x)

    isUpperBound : (n : A) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isUpperBound n = (x : induced) → (fst x) ≲ n

    isLeast→isMinimal : ∀{n} → isLeast n → isMinimal n
    isLeast→isMinimal isl x _ = isl x

    isGreatest→isMaximal : ∀{n} → isGreatest n → isMaximal n
    isGreatest→isMaximal isg x _ = isg x

    isLeast→isLowerBound : ∀{n} → isLeast n → isLowerBound (fst n)
    isLeast→isLowerBound isl = isl

    isGreatest→isUpperBound : ∀{n} → isGreatest n → isUpperBound (fst n)
    isGreatest→isUpperBound isg = isg

  module _
    (P : A → Type ℓ'')
    (n : A)
    where

    private
      induced : Type (ℓ-max ℓ ℓ'')
      induced = Σ[ x ∈ A ] P x

    isMaximalLowerBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMaximalLowerBound
      = Σ (isLowerBound P n) λ islb → isMaximal (λ x → isLowerBound P x) (n , islb)

    isMinimalUpperBound : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isMinimalUpperBound
      = Σ (isUpperBound P n) λ isub → isMinimal (λ x → isUpperBound P x) (n , isub)

    isInfimum : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isInfimum
      = Σ (isLowerBound P n) λ islb → isGreatest (λ x → isLowerBound P x) (n , islb)

    isSupremum : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isSupremum
      = Σ (isUpperBound P n) λ isub → isLeast (λ x → isUpperBound P x) (n , isub)

module _
  {A : Type ℓ}
  {P : A → Type ℓ''}
  {_≲_ : Rel A A ℓ'}
  (prop : BinaryRelation.isPropValued _≲_)
  where

  private
    induced : Type (ℓ-max ℓ ℓ'')
    induced = Σ[ x ∈ A ] P x

  isPropIsMinimal : {n : induced} → isProp (isMinimal _≲_ P n)
  isPropIsMinimal {n , _} = isPropΠ2 λ (x , _) _ → prop n x

  isPropIsMaximal : {n : induced} → isProp (isMaximal _≲_ P n)
  isPropIsMaximal {n , _} = isPropΠ2 λ (x , _) _ → prop x n

  isPropIsLeast : {n : induced} → isProp (isLeast _≲_ P n)
  isPropIsLeast {n , _} = isPropΠ λ (x , _) → prop n x

  isPropIsGreatest : {n : induced} → isProp (isGreatest _≲_ P n)
  isPropIsGreatest {n , _} = isPropΠ λ (x , _) → prop x n

  isPropIsLowerBound : {n : A} → isProp (isLowerBound _≲_ P n)
  isPropIsLowerBound {n} = isPropΠ λ (x , _) → prop n x

  isPropIsUpperBound : {n : A} → isProp (isUpperBound _≲_ P n)
  isPropIsUpperBound {n} = isPropΠ λ (x , _) → prop x n

  isPropIsMaximalLowerBound : {n : A} → isProp (isMaximalLowerBound _≲_ P n)
  isPropIsMaximalLowerBound {n} = isPropΣ isPropIsLowerBound λ _ → isPropΠ2 λ (x , _) _ → prop x n

  isPropIsMinimalUpperBound : {n : A} → isProp (isMinimalUpperBound _≲_ P n)
  isPropIsMinimalUpperBound {n} = isPropΣ isPropIsUpperBound λ _ → isPropΠ2 λ (x , _) _ → prop n x

  isPropIsInfimum : {n : A} → isProp (isInfimum _≲_ P n)
  isPropIsInfimum {n} = isPropΣ isPropIsLowerBound λ _ → isPropΠ λ (x , _) → prop x n

  isPropIsSupremum : {n : A} → isProp (isSupremum _≲_ P n)
  isPropIsSupremum {n} = isPropΣ isPropIsUpperBound λ _ → isPropΠ λ (x , _) → prop n x

module _
  {A : Type ℓ}
  {_≤_ : Rel A A ℓ'}
  (anti : BinaryRelation.isAntisym _≤_)
  where

  module _
    {P : A → Type ℓ''}
    where

    private
      induced : Type (ℓ-max ℓ ℓ'')
      induced = Σ[ x ∈ A ] P x

    isLeast→ContrMinimal : ∀ n → isLeast _≤_ P n  → ∀ m → isMinimal _≤_ P m → (fst n) ≡ (fst m)
    isLeast→ContrMinimal (n , Pn) isln (m , Pm) ismm
      = anti n m (isln (m , Pm)) (ismm (n , Pn) (isln (m , Pm)))

    isGreatest→ContrMaximal : ∀ n → isGreatest _≤_ P n → ∀ m → isMaximal _≤_ P m → (fst n) ≡ (fst m)
    isGreatest→ContrMaximal (n , Pn) isgn (m , Pm) ismm
      = anti n m (ismm (n , Pn) (isgn (m , Pm))) (isgn (m , Pm))

    isLeastUnique : ∀ n m → isLeast _≤_ P n → isLeast _≤_ P m → (fst n) ≡ (fst m)
    isLeastUnique (n , p) (m , q) isln islm
      = anti n m (isln (m , q)) (islm (n , p))

    isGreatestUnique : ∀ n m → isGreatest _≤_ P n → isGreatest _≤_ P m → (fst n) ≡ (fst m)
    isGreatestUnique (n , p) (m , q) isgn isgm
      = anti n m (isgm (n , p)) (isgn (m , q))

  module _
    {P : A → Type ℓ''}
    where

    private
      induced : Type (ℓ-max ℓ ℓ'')
      induced = Σ[ x ∈ A ] P x

    isInfimumUnique : ∀{n m} → isInfimum _≤_ P n → isInfimum _≤_ P m → n ≡ m
    isInfimumUnique {n} {m} (isln , infn) (islm , infm)
      = isGreatestUnique (n , isln) (m , islm) infn infm

    isSupremumUnique : ∀{n m} → isSupremum _≤_ P n → isSupremum _≤_ P m → n ≡ m
    isSupremumUnique {n} {m} (isun , supn) (isum , supm)
      = isLeastUnique (n , isun) (m , isum) supn supm

module _
  {A : Type ℓ}
  {P : A → Type ℓ''}
  {_≤_ : Rel A A ℓ'}
  (prop : BinaryRelation.isPropValued _≤_)
  (conn : BinaryRelation.isStronglyConnected _≤_)
  where

  private
    induced : Type (ℓ-max ℓ ℓ'')
    induced = Σ[ x ∈ A ] P x

  isMinimal→isLeast : ∀ n → isMinimal _≤_ P n → isLeast _≤_ P n
  isMinimal→isLeast (n , p) ism (m , q)
    = ∥₁-rec (prop n m) (⊎-rec (λ n≤m → n≤m) (λ m≤n → ism (m , q) m≤n)) (conn n m)

  isMaximal→isGreatest : ∀ n → isMaximal _≤_ P n → isGreatest _≤_ P n
  isMaximal→isGreatest (n , p) ism (m , q)
    = ∥₁-rec (prop m n) (⊎-rec (λ m≤n → m≤n) (λ n≤m → ism (m , q) n≤m)) (conn m n)
