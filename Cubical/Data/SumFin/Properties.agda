{-# OPTIONS --safe #-}

module Cubical.Data.SumFin.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
import Cubical.Data.Fin as Fin
import Cubical.Data.Fin.LehmerCode as LehmerCode
open import Cubical.Data.SumFin.Base as SumFin
open import Cubical.Data.Sum renaming (map to map-⊎; ⊎-IdR-⊥-≃ to ⊎-⊥-≃)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    k : ℕ

SumFin→Fin : Fin k → Fin.Fin k
SumFin→Fin = SumFin.elim (λ {k} _ → Fin.Fin k) Fin.fzero Fin.fsuc

Fin→SumFin : Fin.Fin k → Fin k
Fin→SumFin = Fin.elim (λ {k} _ → Fin k) fzero fsuc

Fin→SumFin-fsuc : (fk : Fin.Fin k) → Fin→SumFin (Fin.fsuc fk) ≡ fsuc (Fin→SumFin fk)
Fin→SumFin-fsuc = Fin.elim-fsuc (λ {k} _ → Fin k) fzero fsuc

SumFin→Fin→SumFin : (fk : Fin k) → Fin→SumFin (SumFin→Fin fk) ≡ fk
SumFin→Fin→SumFin = SumFin.elim (λ fk → Fin→SumFin (SumFin→Fin fk) ≡ fk)
                                refl λ {k} {fk} eq →
  Fin→SumFin (Fin.fsuc (SumFin→Fin fk)) ≡⟨ Fin→SumFin-fsuc (SumFin→Fin fk) ⟩
  fsuc (Fin→SumFin (SumFin→Fin fk))     ≡⟨ cong fsuc eq ⟩
  fsuc fk                               ∎

Fin→SumFin→Fin : (fk : Fin.Fin k) → SumFin→Fin (Fin→SumFin fk) ≡ fk
Fin→SumFin→Fin = Fin.elim (λ fk → SumFin→Fin (Fin→SumFin fk) ≡ fk)
                          refl λ {k} {fk} eq →
  SumFin→Fin (Fin→SumFin (Fin.fsuc fk)) ≡⟨ cong SumFin→Fin (Fin→SumFin-fsuc fk) ⟩
  Fin.fsuc (SumFin→Fin (Fin→SumFin fk)) ≡⟨ cong Fin.fsuc eq ⟩
  Fin.fsuc fk                           ∎

SumFin≃Fin : ∀ k → Fin k ≃ Fin.Fin k
SumFin≃Fin _ =
  isoToEquiv (iso SumFin→Fin Fin→SumFin Fin→SumFin→Fin SumFin→Fin→SumFin)

SumFin≡Fin : ∀ k → Fin k ≡ Fin.Fin k
SumFin≡Fin k = ua (SumFin≃Fin k)

enum : (n : ℕ)(p : n < k) → Fin k
enum n p = Fin→SumFin (n , p)

enumElim : (P : Fin k → Type ℓ) → ((n : ℕ)(p : n < k) → P (enum _ p)) → (i : Fin k) → P i
enumElim P f i = subst P (SumFin→Fin→SumFin i) (f (SumFin→Fin i .fst) (SumFin→Fin i .snd))

-- Closure properties of SumFin under type constructors

SumFin⊎≃ : (m n : ℕ) → (Fin m ⊎ Fin n) ≃ (Fin (m + n))
SumFin⊎≃ 0 n = ⊎-swap-≃ ⋆ ⊎-⊥-≃
SumFin⊎≃ (suc m) n = ⊎-assoc-≃ ⋆ ⊎-equiv (idEquiv ⊤) (SumFin⊎≃ m n)

SumFinΣ≃ : (n : ℕ)(f : Fin n → ℕ) → (Σ (Fin n) (λ x → Fin (f x))) ≃ (Fin (totalSum f))
SumFinΣ≃ 0 f = ΣEmpty _
SumFinΣ≃ (suc n) f =
    Σ⊎≃
  ⋆ ⊎-equiv (ΣUnit (λ tt → Fin (f (inl tt)))) (SumFinΣ≃ n (λ x → f (inr x)))
  ⋆ SumFin⊎≃ (f (inl tt)) (totalSum (λ x → f (inr x)))

SumFin×≃ : (m n : ℕ) → (Fin m × Fin n) ≃ (Fin (m · n))
SumFin×≃ m n = SumFinΣ≃ m (λ _ → n) ⋆ pathToEquiv (λ i → Fin (totalSumConst {m = m} n i))

SumFinΠ≃ : (n : ℕ)(f : Fin n → ℕ) → ((x : Fin n) → Fin (f x)) ≃ (Fin (totalProd f))
SumFinΠ≃ 0 _ = isContr→≃Unit (isContrΠ⊥) ⋆ invEquiv (⊎-⊥-≃)
SumFinΠ≃ (suc n) f =
    Π⊎≃
  ⋆ Σ-cong-equiv (ΠUnit (λ tt → Fin (f (inl tt)))) (λ _ → SumFinΠ≃ n (λ x → f (inr x)))
  ⋆ SumFin×≃ (f (inl tt)) (totalProd (λ x → f (inr x)))

isNotZero : ℕ → ℕ
isNotZero 0 = 0
isNotZero (suc n) = 1

SumFin∥∥≃ : (n : ℕ) → ∥ Fin n ∥₁ ≃ Fin (isNotZero n)
SumFin∥∥≃ 0 = propTruncIdempotent≃ (isProp⊥)
SumFin∥∥≃ (suc n) =
    isContr→≃Unit (inhProp→isContr ∣ inl tt ∣₁ isPropPropTrunc)
  ⋆ isContr→≃Unit (isContrUnit) ⋆ invEquiv (⊎-⊥-≃)

ℕ→Bool : ℕ → Bool
ℕ→Bool 0 = false
ℕ→Bool (suc n) = true

SumFin∥∥DecProp : (n : ℕ) → ∥ Fin n ∥₁ ≃ Bool→Type (ℕ→Bool n)
SumFin∥∥DecProp 0 = uninhabEquiv (Prop.rec isProp⊥ ⊥.rec) ⊥.rec
SumFin∥∥DecProp (suc n) = isContr→≃Unit (inhProp→isContr ∣ inl tt ∣₁ isPropPropTrunc)

-- negation of SumFin

SumFin¬ : (n : ℕ) → (¬ Fin n) ≃ Bool→Type (isZero n)
SumFin¬ 0 = isContr→≃Unit isContr⊥→A
SumFin¬ (suc n) = uninhabEquiv (λ f → f fzero) ⊥.rec

-- SumFin 1 is equivalent to unit

Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = ⊎-⊥-≃

isContrSumFin1 : isContr (Fin 1)
isContrSumFin1 = isOfHLevelRespectEquiv 0 (invEquiv Fin1≃Unit) isContrUnit

-- SumFin 2 is equivalent to Bool

SumFin2≃Bool : Fin 2 ≃ Bool
SumFin2≃Bool = ⊎-equiv (idEquiv _) ⊎-⊥-≃ ⋆ isoToEquiv Iso-⊤⊎⊤-Bool

-- decidable predicate over SumFin

SumFinℙ≃ : (n : ℕ) → (Fin n → Bool) ≃ Fin (2 ^ n)
SumFinℙ≃ 0 = isContr→≃Unit (isContrΠ⊥) ⋆ invEquiv (⊎-⊥-≃)
SumFinℙ≃ (suc n) =
    Π⊎≃
  ⋆ Σ-cong-equiv (UnitToType≃ Bool ⋆ invEquiv SumFin2≃Bool) (λ _ → SumFinℙ≃ n)
  ⋆ SumFin×≃ 2 (2 ^ n)

-- decidable subsets of SumFin

Bool→ℕ : Bool → ℕ
Bool→ℕ true = 1
Bool→ℕ false = 0

trueCount : {n : ℕ}(f : Fin n → Bool) → ℕ
trueCount {n = 0} _ = 0
trueCount {n = suc n} f = Bool→ℕ (f (inl tt)) + (trueCount (f ∘ inr))

SumFinDec⊎≃ : (n : ℕ)(t : Bool) → (Bool→Type t ⊎ Fin n) ≃ (Fin (Bool→ℕ t + n))
SumFinDec⊎≃ _ true = idEquiv _
SumFinDec⊎≃ _ false = ⊎-swap-≃ ⋆ ⊎-⊥-≃

SumFinSub≃ : (n : ℕ)(f : Fin n → Bool) → Σ _ (Bool→Type ∘ f) ≃ Fin (trueCount f)
SumFinSub≃ 0 _ = ΣEmpty _
SumFinSub≃ (suc n) f =
    Σ⊎≃
  ⋆ ⊎-equiv (ΣUnit (Bool→Type ∘ f ∘ inl)) (SumFinSub≃ n (f ∘ inr))
  ⋆ SumFinDec⊎≃ _ (f (inl tt))

-- decidable quantifier

trueForSome : (n : ℕ)(f : Fin n → Bool) → Bool
trueForSome 0 _ = false
trueForSome (suc n) f = f (inl tt) or trueForSome n (f ∘ inr)

trueForAll : (n : ℕ)(f : Fin n → Bool) → Bool
trueForAll 0 _ = true
trueForAll (suc n) f = f (inl tt) and trueForAll n (f ∘ inr)

SumFin∃→ : (n : ℕ)(f : Fin n → Bool) → Σ _ (Bool→Type ∘ f) → Bool→Type (trueForSome n f)
SumFin∃→ 0 _ = ΣEmpty _ .fst
SumFin∃→ (suc n) f =
    Bool→Type⊎' _ _
  ∘ map-⊎ (ΣUnit (Bool→Type ∘ f ∘ inl) .fst) (SumFin∃→ n (f ∘ inr))
  ∘ Σ⊎≃ .fst

SumFin∃← : (n : ℕ)(f : Fin n → Bool) → Bool→Type (trueForSome n f) → Σ _ (Bool→Type ∘ f)
SumFin∃← 0 _ = ⊥.rec
SumFin∃← (suc n) f =
    invEq Σ⊎≃
  ∘ map-⊎ (invEq (ΣUnit (Bool→Type ∘ f ∘ inl))) (SumFin∃← n (f ∘ inr))
  ∘ Bool→Type⊎ _ _

SumFin∃≃ : (n : ℕ)(f : Fin n → Bool) → ∥ Σ (Fin n) (Bool→Type ∘ f) ∥₁ ≃ Bool→Type (trueForSome n f)
SumFin∃≃ n f =
  propBiimpl→Equiv isPropPropTrunc isPropBool→Type
    (Prop.rec isPropBool→Type (SumFin∃→ n f))
    (∣_∣₁ ∘ SumFin∃← n f)

SumFin∀≃ : (n : ℕ)(f : Fin n → Bool) → ((x : Fin n) → Bool→Type (f x)) ≃ Bool→Type (trueForAll n f)
SumFin∀≃ 0 _ = isContr→≃Unit (isContrΠ⊥)
SumFin∀≃ (suc n) f =
    Π⊎≃
  ⋆ Σ-cong-equiv (ΠUnit (Bool→Type ∘ f ∘ inl)) (λ _ → SumFin∀≃ n (f ∘ inr))
  ⋆ Bool→Type×≃ _ _

-- internal equality

SumFin≡ : (n : ℕ) → (a b : Fin n) → Bool
SumFin≡ 0 _ _ = true
SumFin≡ (suc n) (inl tt) (inl tt) = true
SumFin≡ (suc n) (inl tt) (inr y) = false
SumFin≡ (suc n) (inr x) (inl tt) = false
SumFin≡ (suc n) (inr x) (inr y) = SumFin≡ n x y

isSetSumFin : (n : ℕ)→ isSet (Fin n)
isSetSumFin 0 = isProp→isSet isProp⊥
isSetSumFin (suc n) = isSet⊎ (isProp→isSet isPropUnit) (isSetSumFin n)

SumFin≡≃ : (n : ℕ) → (a b : Fin n) → (a ≡ b) ≃ Bool→Type (SumFin≡ n a b)
SumFin≡≃ 0 _ _ = isContr→≃Unit (isProp→isContrPath isProp⊥ _ _)
SumFin≡≃ (suc n) (inl tt) (inl tt) = isContr→≃Unit (inhProp→isContr refl (isSetSumFin _ _ _))
SumFin≡≃ (suc n) (inl tt) (inr y) = invEquiv (⊎Path.Cover≃Path _ _) ⋆ uninhabEquiv ⊥.rec* ⊥.rec
SumFin≡≃ (suc n) (inr x) (inl tt) = invEquiv (⊎Path.Cover≃Path _ _) ⋆ uninhabEquiv ⊥.rec* ⊥.rec
SumFin≡≃ (suc n) (inr x) (inr y) = invEquiv (_ , isEmbedding-inr x y) ⋆ SumFin≡≃ n x y

-- propositional truncation of Fin

-- decidability of Fin

DecFin : (n : ℕ) → Dec (Fin n)
DecFin 0 = no (idfun _)
DecFin (suc n) = yes fzero

-- propositional truncation of Fin

Dec∥Fin∥ : (n : ℕ) → Dec ∥ Fin n ∥₁
Dec∥Fin∥ n = Dec∥∥ (DecFin n)

-- some properties about cardinality

fzero≠fone : {n : ℕ} → ¬ (fzero ≡ fsuc fzero)
fzero≠fone {n = n} = SumFin≡≃ (suc (suc n)) fzero (fsuc fzero) .fst

Fin>0→isInhab : (n : ℕ) → 0 < n → Fin n
Fin>0→isInhab 0 p = ⊥.rec (¬-<-zero p)
Fin>0→isInhab (suc n) p = fzero

Fin>1→hasNonEqualTerm : (n : ℕ) → 1 < n → Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] ¬ i ≡ j
Fin>1→hasNonEqualTerm 0 p = ⊥.rec (snotz (≤0→≡0 p))
Fin>1→hasNonEqualTerm 1 p = ⊥.rec (snotz (≤0→≡0 (pred-≤-pred p)))
Fin>1→hasNonEqualTerm (suc (suc n)) _ = fzero , fsuc fzero , fzero≠fone

isEmpty→Fin≡0 : (n : ℕ) → ¬ Fin n → 0 ≡ n
isEmpty→Fin≡0 0 _ = refl
isEmpty→Fin≡0 (suc n) p = ⊥.rec (p fzero)

isInhab→Fin>0 : (n : ℕ) → Fin n → 0 < n
isInhab→Fin>0 0 i = ⊥.rec i
isInhab→Fin>0 (suc n) _ = suc-≤-suc zero-≤

hasNonEqualTerm→Fin>1 : (n : ℕ) → (i j : Fin n) → ¬ i ≡ j → 1 < n
hasNonEqualTerm→Fin>1 0 i _ _ = ⊥.rec i
hasNonEqualTerm→Fin>1 1 i j p = ⊥.rec (p (isContr→isProp isContrSumFin1 i j))
hasNonEqualTerm→Fin>1 (suc (suc n)) _ _ _ = suc-≤-suc (suc-≤-suc zero-≤)

Fin≤1→isProp : (n : ℕ) → n ≤ 1 → isProp (Fin n)
Fin≤1→isProp 0 _ = isProp⊥
Fin≤1→isProp 1 _ = isContr→isProp isContrSumFin1
Fin≤1→isProp (suc (suc n)) p = ⊥.rec (¬-<-zero (pred-≤-pred p))

isProp→Fin≤1 : (n : ℕ) → isProp (Fin n) → n ≤ 1
isProp→Fin≤1 0 _ = ≤-solver 0 1
isProp→Fin≤1 1 _ = ≤-solver 1 1
isProp→Fin≤1 (suc (suc n)) p = ⊥.rec (fzero≠fone (p fzero (fsuc fzero)))

-- automorphisms of SumFin

SumFin≃≃ : (n : ℕ) → (Fin n ≃ Fin n) ≃ Fin (LehmerCode.factorial n)
SumFin≃≃ _ =
    equivComp (SumFin≃Fin _) (SumFin≃Fin _)
  ⋆ LehmerCode.lehmerEquiv
  ⋆ LehmerCode.lehmerFinEquiv
  ⋆ invEquiv (SumFin≃Fin _)
