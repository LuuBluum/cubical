{-
 following Johnstone's book "Stone Spaces" we define semilattices
 to be commutative monoids such that every element is idempotent.
 In particular, we take every semilattice to have a neutral element
 that is either the maximal or minimal element depending on whether
 we have a join or meet semilattice.
-}

{-# OPTIONS --safe #-}
module Cubical.Algebra.Semilattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.FinData

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.BigOp
open import Cubical.Algebra.CommMonoid

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Reflection.RecordEquiv

open Iso

private
  variable
    ℓ ℓ' : Level

record IsSemilattice {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor issemilattice

  field
   isCommMonoid : IsCommMonoid ε _·_
   idem : (x : A) → x · x ≡ x

  open IsCommMonoid isCommMonoid public

unquoteDecl IsSemilatticeIsoΣ = declareRecordIsoΣ IsSemilatticeIsoΣ (quote IsSemilattice)

record SemilatticeStr (A : Type ℓ) : Type ℓ where
  constructor semilatticestr

  field
    ε        : A
    _·_      : A → A → A
    isSemilattice : IsSemilattice ε _·_

  infixl 7 _·_

  open IsSemilattice isSemilattice public

Semilattice : ∀ ℓ → Type (ℓ-suc ℓ)
Semilattice ℓ = TypeWithStr ℓ SemilatticeStr

semilattice : (A : Type ℓ) (ε : A) (_·_ : A → A → A) (h : IsSemilattice ε _·_) → Semilattice ℓ
semilattice A ε _·_ h = A , semilatticestr ε _·_ h

-- Easier to use constructors
makeIsSemilattice : {L : Type ℓ} {ε : L} {_·_ : L → L → L}
               (is-setL : isSet L)
               (assoc : (x y z : L) → x · (y · z) ≡ (x · y) · z)
               (rid : (x : L) → x · ε ≡ x)
               (comm : (x y : L) → x · y ≡ y · x)
               (idem : (x : L) → x · x ≡ x)
             → IsSemilattice ε _·_
IsSemilattice.isCommMonoid (makeIsSemilattice is-setL assoc rid comm idem) =
                                        makeIsCommMonoid is-setL assoc rid comm
IsSemilattice.idem (makeIsSemilattice is-setL assoc rid comm idem) = idem

makeSemilattice : {L : Type ℓ} (ε : L) (_·_ : L → L → L)
             (is-setL : isSet L)
             (assoc : (x y z : L) → x · (y · z) ≡ (x · y) · z)
             (rid : (x : L) → x · ε ≡ x)
             (comm : (x y : L) → x · y ≡ y · x)
             (idem : (x : L) → x · x ≡ x)
             → Semilattice ℓ
makeSemilattice ε _·_ is-setL assoc rid comm idem =
  semilattice _ ε _·_ (makeIsSemilattice is-setL assoc rid comm idem)


SemilatticeStr→MonoidStr : {A : Type ℓ} → SemilatticeStr A → MonoidStr A
SemilatticeStr→MonoidStr (semilatticestr _ _ H) =
                          monoidstr _ _ (H .IsSemilattice.isCommMonoid .IsCommMonoid.isMonoid)

Semilattice→Monoid : Semilattice ℓ → Monoid ℓ
Semilattice→Monoid (_ , semilatticestr _ _ H) =
                    _ , monoidstr _ _ (H .IsSemilattice.isCommMonoid .IsCommMonoid.isMonoid)

Semilattice→CommMonoid : Semilattice ℓ → CommMonoid ℓ
Semilattice→CommMonoid (_ , semilatticestr _ _ H) =
                        _ , commmonoidstr _ _ (H .IsSemilattice.isCommMonoid)

SemilatticeHom : (L : Semilattice ℓ) (M : Semilattice ℓ') → Type (ℓ-max ℓ ℓ')
SemilatticeHom L M = MonoidHom (Semilattice→Monoid L) (Semilattice→Monoid M)

IsSemilatticeEquiv : {A : Type ℓ} {B : Type ℓ'}
  (M : SemilatticeStr A) (e : A ≃ B) (N : SemilatticeStr B) → Type (ℓ-max ℓ ℓ')
IsSemilatticeEquiv M e N =
                   IsMonoidHom (SemilatticeStr→MonoidStr M) (e .fst) (SemilatticeStr→MonoidStr N)

SemilatticeEquiv : (M : Semilattice ℓ) (N : Semilattice ℓ') → Type (ℓ-max ℓ ℓ')
SemilatticeEquiv M N = Σ[ e ∈ (M .fst ≃ N .fst) ] IsSemilatticeEquiv (M .snd) e (N .snd)

isPropIsSemilattice : {L : Type ℓ} (ε : L) (_·_ : L → L → L)
             → isProp (IsSemilattice ε _·_)
isPropIsSemilattice ε _·_ (issemilattice LL LC) (issemilattice SL SC) =
  λ i → issemilattice (isPropIsCommMonoid _ _ LL SL i) (isPropIdem LC SC i)
  where
  isSetL : isSet _
  isSetL = LL .IsCommMonoid.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

  isPropIdem : isProp ((x : _) → x · x ≡ x)
  isPropIdem = isPropΠ λ _ → isSetL _ _

𝒮ᴰ-Semilattice : DUARel (𝒮-Univ ℓ) SemilatticeStr ℓ
𝒮ᴰ-Semilattice =
  𝒮ᴰ-Record (𝒮-Univ _) IsSemilatticeEquiv
    (fields:
      data[ ε ∣ autoDUARel _ _ ∣ presε ]
      data[ _·_ ∣ autoDUARel _ _ ∣ pres· ]
      prop[ isSemilattice ∣ (λ _ _ → isPropIsSemilattice _ _) ])
  where
  open SemilatticeStr
  open IsMonoidHom

SemilatticePath : (L K : Semilattice ℓ) → SemilatticeEquiv L K ≃ (L ≡ K)
SemilatticePath = ∫ 𝒮ᴰ-Semilattice .UARel.ua


-- TODO: decide if that's the right approach
module JoinSemilattice (L' : Semilattice ℓ) where
 private L = fst L'
 open SemilatticeStr (snd L') renaming (_·_ to _∨l_ ; ε to 0l)
 open CommMonoidTheory (Semilattice→CommMonoid L')
 open MonoidBigOp (Semilattice→Monoid L')

 _≤_ : L → L → Type ℓ
 x ≤ y = x ∨l y ≡ y

 infix 4 _≤_

 IndPoset : Poset ℓ ℓ
 fst IndPoset = L
 PosetStr._≤_ (snd IndPoset) = _≤_
 IsPoset.is-set (PosetStr.isPoset (snd IndPoset)) = is-set
 IsPoset.is-prop-valued (PosetStr.isPoset (snd IndPoset)) = λ _ _ → is-set _ _
 IsPoset.is-refl (PosetStr.isPoset (snd IndPoset)) = idem
 IsPoset.is-trans (PosetStr.isPoset (snd IndPoset)) = path
  where
  path : (a b c : L) → a ∨l b ≡ b → b ∨l c ≡ c → a ∨l c ≡ c
  path a b c a∨b≡b b∨c≡c = a ∨l c ≡⟨ cong (a ∨l_) (sym b∨c≡c) ⟩
                            a ∨l (b ∨l c) ≡⟨ ·Assoc _ _ _ ⟩
                            (a ∨l b) ∨l c ≡⟨ cong (_∨l c) a∨b≡b ⟩
                            b ∨l c ≡⟨ b∨c≡c ⟩
                            c ∎
 IsPoset.is-antisym (PosetStr.isPoset (snd IndPoset)) =
   λ _ _ a∨b≡b b∨a≡a → sym b∨a≡a ∙∙ ·Comm _ _ ∙∙ a∨b≡b

 ∨lIsMax : ∀ x y z → x ≤ z → y ≤ z → x ∨l y ≤ z
 ∨lIsMax x y z x≤z y≤z = cong ((x ∨l y) ∨l_) (sym (idem z)) ∙ commAssocSwap x y z z
                                                            ∙ cong₂ (_∨l_) x≤z y≤z
                                                            ∙ idem z

 ∨≤LCancel : ∀ x y → y ≤ x ∨l y
 ∨≤LCancel x y = commAssocl y x y ∙ cong (x ∨l_) (idem y)

 ∨≤RCancel : ∀ x y → x ≤ x ∨l y
 ∨≤RCancel x y = ·Assoc _ _ _ ∙ cong (_∨l y) (idem x)

 ≤-∨Pres : ∀ x y u w → x ≤ y → u ≤ w → x ∨l u ≤ y ∨l w
 ≤-∨Pres x y u w x≤y u≤w = commAssocSwap x u y w ∙ cong₂ (_∨l_) x≤y u≤w

 ≤-∨LPres : ∀ x y z → x ≤ y → z ∨l x ≤ z ∨l y
 ≤-∨LPres x y z x≤y = ≤-∨Pres _ _ _ _ (idem z) x≤y

 ≤-∨RPres : ∀ x y z → x ≤ y → x ∨l z ≤ y ∨l z
 ≤-∨RPres x y z x≤y = ≤-∨Pres _ _ _ _ x≤y (idem z)

 -- inequalities of bigOps
 open IsPoset (PosetStr.isPoset (snd IndPoset))
 open PosetReasoning IndPoset


 ind≤bigOp : {n : ℕ} (U : FinVec L n) (i : Fin n) → U i ≤ bigOp U
 ind≤bigOp {n = suc n} U zero = ∨≤RCancel _ _
 ind≤bigOp {n = suc n} U (suc i) = is-trans _ (bigOp (U ∘ suc)) _ (ind≤bigOp (U ∘ suc) i)
                                                                  (∨≤LCancel _ _)

 bigOpIsMax : {n : ℕ} (U : FinVec L n) (x : L) → (∀ i → U i ≤ x) → bigOp U ≤ x
 bigOpIsMax {n = zero} _ _ _ = ·IdL _
 bigOpIsMax {n = suc n} U x U≤x =
   bigOp U                   ≤⟨ is-refl _ ⟩
   U zero ∨l bigOp (U ∘ suc) ≤⟨ ≤-∨LPres _ _ _ (bigOpIsMax _ _ (U≤x ∘ suc)) ⟩
   U zero ∨l x               ≤⟨ ∨lIsMax _ _ _ (U≤x zero) (is-refl x) ⟩
   x ◾

 ≤-bigOpExt : {n : ℕ} (U W : FinVec L n) → (∀ i → U i ≤ W i) → bigOp U ≤ bigOp W
 ≤-bigOpExt {n = zero} U W U≤W = is-refl 0l
 ≤-bigOpExt {n = suc n} U W U≤W = ≤-∨Pres _ _ _ _ (U≤W zero) (≤-bigOpExt _ _ (U≤W ∘ suc))

module MeetSemilattice (L' : Semilattice ℓ) where
 private L = fst L'
 open SemilatticeStr (snd L') renaming (_·_ to _∧l_ ; ε to 1l)
 open CommMonoidTheory (Semilattice→CommMonoid L')

 _≤_ : L → L → Type ℓ
 x ≤ y = x ∧l y ≡ x

 infix 4 _≤_

 IndPoset : Poset ℓ ℓ
 fst IndPoset = L
 PosetStr._≤_ (snd IndPoset) = _≤_
 IsPoset.is-set (PosetStr.isPoset (snd IndPoset)) = is-set
 IsPoset.is-prop-valued (PosetStr.isPoset (snd IndPoset)) = λ _ _ → is-set _ _
 IsPoset.is-refl (PosetStr.isPoset (snd IndPoset)) = idem
 IsPoset.is-trans (PosetStr.isPoset (snd IndPoset)) = path
  where
  path : (a b c : L) → a ∧l b ≡ a → b ∧l c ≡ b → a ∧l c ≡ a
  path a b c a∧b≡a b∧c≡b = a ∧l c ≡⟨ cong (_∧l c) (sym a∧b≡a) ⟩
                            (a ∧l b) ∧l c ≡⟨ sym (·Assoc _ _ _) ⟩
                            a ∧l (b ∧l c) ≡⟨ cong (a ∧l_) b∧c≡b ⟩
                            a ∧l b ≡⟨ a∧b≡a ⟩
                            a ∎
 IsPoset.is-antisym (PosetStr.isPoset (snd IndPoset)) =
   λ _ _ a∧b≡a b∧a≡b → sym a∧b≡a ∙∙ ·Comm _ _ ∙∙ b∧a≡b

 ≤-∧LPres : ∀ x y z → x ≤ y → z ∧l x ≤ z ∧l y
 ≤-∧LPres x y z x≤y = commAssocSwap z x z y ∙∙ cong (_∧l (x ∧l y)) (idem z) ∙∙ cong (z ∧l_) x≤y

 ≤-∧RPres : ∀ x y z → x ≤ y → x ∧l z ≤ y ∧l z
 ≤-∧RPres x y z x≤y = commAssocSwap x z y z ∙∙ cong (x ∧l y ∧l_) (idem z) ∙∙ cong (_∧l z) x≤y

 ≤-∧Pres : ∀ x y z w → x ≤ y → z ≤ w → x ∧l z ≤ y ∧l w
 ≤-∧Pres x y z w x≤y z≤w = commAssocSwap x z y w ∙ cong₂ _∧l_ x≤y z≤w

 ∧≤LCancel : ∀ x y → x ∧l y ≤ y
 ∧≤LCancel x y = sym (·Assoc _ _ _) ∙ cong (x ∧l_) (idem y)

 ∧≤RCancel : ∀ x y → x ∧l y ≤ x
 ∧≤RCancel x y = commAssocr x y x ∙ cong (_∧l y) (idem x)

 ∧lIsMin : ∀ x y z → z ≤ x → z ≤ y → z ≤ x ∧l y
 ∧lIsMin x y z z≤x z≤y = cong (_∧l (x ∧l y)) (sym (idem z)) ∙ commAssocSwap z z x y
                                                            ∙ cong₂ (_∧l_) z≤x z≤y
                                                            ∙ idem z
