{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎-rec)
open import Cubical.Relation.Nullary.Base
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥₁-rec ; map to ∥₁-map)

private
  variable
    ℓA ℓ≅A ℓA' ℓ≅A' : Level

Rel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
Rel A B ℓ' = A → B → Type ℓ'

PropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

idPropRel : ∀ {ℓ} (A : Type ℓ) → PropRel A A ℓ
idPropRel A .fst a a' = ∥ a ≡ a' ∥₁
idPropRel A .snd _ _ = squash₁

invPropRel : ∀ {ℓ ℓ'} {A B : Type ℓ}
  → PropRel A B ℓ' → PropRel B A ℓ'
invPropRel R .fst b a = R .fst a b
invPropRel R .snd b a = R .snd a b

compPropRel : ∀ {ℓ ℓ' ℓ''} {A B C : Type ℓ}
  → PropRel A B ℓ' → PropRel B C ℓ'' → PropRel A C (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
compPropRel R S .fst a c = ∥ Σ[ b ∈ _ ] (R .fst a b × S .fst b c) ∥₁
compPropRel R S .snd _ _ = squash₁

graphRel : ∀ {ℓ} {A B : Type ℓ} → (A → B) → Rel A B ℓ
graphRel f a b = f a ≡ b

module HeterogenousRelation {ℓ ℓ' : Level} {A B : Type ℓ} (R : Rel A B ℓ') where
  isUniversalRel : Type (ℓ-max ℓ ℓ')
  isUniversalRel = (a : A) (b : B) → R a b

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → R a a

  isIrrefl : Type (ℓ-max ℓ ℓ')
  isIrrefl = (a : A) → ¬ R a a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → R a b → R b a

  isAntisym : Type (ℓ-max ℓ ℓ')
  isAntisym = (a b : A) → R a b → R b a → a ≡ b

  isAsym : Type (ℓ-max ℓ ℓ')
  isAsym = (a b : A) → R a b → ¬ R b a

  isAsym→isIrrefl : isAsym → isIrrefl
  isAsym→isIrrefl asym a Raa = asym a a Raa Raa

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A) → R a b → R b c → R a c

  -- Sum types don't play nicely with props, so we truncate
  isCotrans : Type (ℓ-max ℓ ℓ')
  isCotrans = (a b c : A) → R a b → ∥ (R a c ⊎ R b c) ∥₁

  isWeaklyLinear : Type (ℓ-max ℓ ℓ')
  isWeaklyLinear = (a b c : A) → R a b → ∥ (R a c ⊎ R c b) ∥₁

  isConnected : Type (ℓ-max ℓ ℓ')
  isConnected = (a b : A) → ¬ (a ≡ b) → ∥ (R a b ⊎ R b a) ∥₁

  isStronglyConnected : Type (ℓ-max ℓ ℓ')
  isStronglyConnected = (a b : A) → ∥ (R a b ⊎ R b a) ∥₁

  isStronglyConnected→isConnected : isStronglyConnected → isConnected
  isStronglyConnected→isConnected strong a b _ = strong a b

  isIrrefl×isTrans→isAsym : isIrrefl × isTrans → isAsym
  isIrrefl×isTrans→isAsym (irrefl , trans) a₀ a₁ Ra₀a₁ Ra₁a₀ = irrefl a₀ (trans a₀ a₁ a₀ Ra₀a₁ Ra₁a₀)

  IrreflKernel : Rel A A (ℓ-max ℓ ℓ')
  IrreflKernel a b = R a b × (¬ a ≡ b)

  ReflClosure : Rel A A (ℓ-max ℓ ℓ')
  ReflClosure a b = R a b ⊎ (a ≡ b)

  SymKernel : Rel A A ℓ'
  SymKernel a b = R a b × R b a

  SymClosure : Rel A A ℓ'
  SymClosure a b = R a b ⊎ R b a

  AsymKernel : Rel A A ℓ'
  AsymKernel a b = R a b × (¬ R b a)

  module _
    {ℓ'' : Level}
    (P : A → Type ℓ'')

    where

    private
      induced : Type (ℓ-max ℓ ℓ'')
      induced = Σ[ x ∈ A ] P x

    InducedRelation : Rel induced induced ℓ'
    InducedRelation (a , _) (b , _) = R a b

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor equivRel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isUniversalRel→isEquivRel : HeterogenousRelation.isUniversalRel R → isEquivRel
  isUniversalRel→isEquivRel u .isEquivRel.reflexive a = u a a
  isUniversalRel→isEquivRel u .isEquivRel.symmetric a b _ = u b a
  isUniversalRel→isEquivRel u .isEquivRel.transitive a _ c _ _ = u a c

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (R a b)

  isStronglyConnected×isPropValued→isRefl : isStronglyConnected × isPropValued → isRefl
  isStronglyConnected×isPropValued→isRefl (strong , prop) a = ∥₁-rec (prop a a) (λ x → ⊎-rec (λ z → z) (λ z → z) x) (strong a a)

  isSetValued : Type (ℓ-max ℓ ℓ')
  isSetValued = (a b : A) → isSet (R a b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective =
    (a b : A) → isEquiv (eq/ {R = R} a b)

  impliesIdentity : Type _
  impliesIdentity = {a a' : A} → (R a a') → (a ≡ a')

  isSym×isAntisym→impliesIdentity : isSym × isAntisym → impliesIdentity
  isSym×isAntisym→impliesIdentity (sym , antisym) {a} {b} Rab = antisym a b Rab (sym a b Rab)

  -- the total space corresponding to the binary relation w.r.t. a
  relSinglAt : (a : A) → Type (ℓ-max ℓ ℓ')
  relSinglAt a = Σ[ a' ∈ A ] (R a a')

  -- the statement that the total space is contractible at any a
  contrRelSingl : Type (ℓ-max ℓ ℓ')
  contrRelSingl = (a : A) → isContr (relSinglAt a)

  isUnivalent : Type (ℓ-max ℓ ℓ')
  isUnivalent = (a a' : A) → (R a a') ≃ (a ≡ a')

  contrRelSingl→isUnivalent : isRefl → contrRelSingl → isUnivalent
  contrRelSingl→isUnivalent ρ c a a' = isoToEquiv i
    where
      h : isProp (relSinglAt a)
      h = isContr→isProp (c a)
      aρa : relSinglAt a
      aρa = a , ρ a
      Q : (y : A) → a ≡ y → _
      Q y _ = R a y
      i : Iso (R a a') (a ≡ a')
      Iso.fun i r = cong fst (h aρa (a' , r))
      Iso.inv i = J Q (ρ a)
      Iso.rightInv i = J (λ y p → cong fst (h aρa (y , J Q (ρ a) p)) ≡ p)
                         (J (λ q _ → cong fst (h aρa (a , q)) ≡ refl)
                           (J (λ α _ → cong fst α ≡ refl) refl
                             (isProp→isSet h _ _ refl (h _ _)))
                           (sym (JRefl Q (ρ a))))
      Iso.leftInv i r = J (λ w β → J Q (ρ a) (cong fst β) ≡ snd w)
                          (JRefl Q (ρ a)) (h aρa (a' , r))

  isUnivalent→contrRelSingl : isUnivalent → contrRelSingl
  isUnivalent→contrRelSingl u a = q
    where
      abstract
        f : (x : A) → a ≡ x → R a x
        f x p = invEq (u a x) p

        t : singl a → relSinglAt a
        t (x , p) = x , f x p

        q : isContr (relSinglAt a)
        q = isOfHLevelRespectEquiv 0 (t , totalEquiv _ _ f λ x → invEquiv (u a x) .snd)
                                   (isContrSingl a)

EquivRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivRel A ℓ' = Σ[ R ∈ Rel A A ℓ' ] BinaryRelation.isEquivRel R

EquivPropRel : ∀ {ℓ} (A : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
EquivPropRel A ℓ' = Σ[ R ∈ PropRel A A ℓ' ] BinaryRelation.isEquivRel (R .fst)

record RelIso {A : Type ℓA} (_≅_ : Rel A A ℓ≅A)
              {A' : Type ℓA'} (_≅'_ : Rel A' A' ℓ≅A') : Type (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≅A ℓ≅A')) where
  constructor reliso
  field
    fun : A → A'
    inv : A' → A
    rightInv : (a' : A') → fun (inv a') ≅' a'
    leftInv : (a : A) → inv (fun a) ≅ a

open BinaryRelation

RelIso→Iso : {A : Type ℓA} {A' : Type ℓA'}
             (_≅_ : Rel A A ℓ≅A) (_≅'_ : Rel A' A' ℓ≅A')
             (uni : impliesIdentity _≅_) (uni' : impliesIdentity _≅'_)
             (f : RelIso _≅_ _≅'_)
             → Iso A A'
Iso.fun (RelIso→Iso _ _ _ _ f) = RelIso.fun f
Iso.inv (RelIso→Iso _ _ _ _ f) = RelIso.inv f
Iso.rightInv (RelIso→Iso _ _ uni uni' f) a'
  = uni' (RelIso.rightInv f a')
Iso.leftInv (RelIso→Iso _ _ uni uni' f) a
  = uni (RelIso.leftInv f a)

isIrreflIrreflKernel : ∀{ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isIrrefl (IrreflKernel R)
isIrreflIrreflKernel _ _ (_ , ¬a≡a) = ¬a≡a refl

isReflReflClosure : ∀{ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isRefl (ReflClosure R)
isReflReflClosure _ _ = inr refl

isConnectedStronglyConnectedIrreflKernel : ∀{ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isStronglyConnected R → isConnected (IrreflKernel R)
isConnectedStronglyConnectedIrreflKernel R strong a b ¬a≡b = ∥₁-map (λ x → ⊎-rec (λ Rab → inl (Rab , ¬a≡b)) (λ Rba → inr (Rba , (λ b≡a → ¬a≡b (sym b≡a)))) x) (strong a b)

isSymSymKernel : ∀{ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isSym (SymKernel R)
isSymSymKernel _ _ _ (Rab , Rba) = Rba , Rab

isSymSymClosure : ∀{ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isSym (SymClosure R)
isSymSymClosure _ _ _ (inl Rab) = inr Rab
isSymSymClosure _ _ _ (inr Rba) = inl Rba

isAsymAsymKernel : ∀ {ℓ ℓ'} {A : Type ℓ} (R : Rel A A ℓ') → isAsym (AsymKernel R)
isAsymAsymKernel _ _ _ (Rab , _) (_ , ¬Rab) = ¬Rab Rab
