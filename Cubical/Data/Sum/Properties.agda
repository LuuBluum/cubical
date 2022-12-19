{-# OPTIONS --safe #-}
module Cubical.Data.Sum.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.Data.Sum.Base

open Iso


private
  variable
    ℓa ℓb ℓc ℓd ℓe : Level
    A : Type ℓa
    B : Type ℓb
    C : Type ℓc
    D : Type ℓd
    E : A ⊎ B → Type ℓe


-- Path space of sum type
module ⊎Path {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  Cover : A ⊎ B → A ⊎ B → Type (ℓ-max ℓ ℓ')
  Cover (inl a) (inl a') = Lift {j = ℓ-max ℓ ℓ'} (a ≡ a')
  Cover (inl _) (inr _) = Lift ⊥
  Cover (inr _) (inl _) = Lift ⊥
  Cover (inr b) (inr b') = Lift {j = ℓ-max ℓ ℓ'} (b ≡ b')

  reflCode : (c : A ⊎ B) → Cover c c
  reflCode (inl a) = lift refl
  reflCode (inr b) = lift refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode (inl a) (inl a') (lift p) = cong inl p
  decode (inl a) (inr b') ()
  decode (inr b) (inl a') ()
  decode (inr b) (inr b') (lift q) = cong inr q

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl (inl a) = refl
  decodeRefl (inr b) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode (inl a) (inl _) (lift d) =
    J (λ a' p → encode (inl a) (inl a') (cong inl p) ≡ lift p) (encodeRefl (inl a)) d
  encodeDecode (inr a) (inr _) (lift d) =
    J (λ a' p → encode (inr a) (inr a') (cong inr p) ≡ lift p) (encodeRefl (inr a)) d

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' =
    isoToEquiv (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → isOfHLevel (suc (suc n)) B
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p q (inl a) (inl a') = isOfHLevelLift (suc n) (p a a')
  isOfHLevelCover n p q (inl a) (inr b') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inl a') =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p q (inr b) (inr b') = isOfHLevelLift (suc n) (q b b')

isEmbedding-inl : isEmbedding (inl {A = A} {B = B})
isEmbedding-inl w z = snd (compEquiv LiftEquiv (⊎Path.Cover≃Path (inl w) (inl z)))

isEmbedding-inr : isEmbedding (inr {A = A} {B = B})
isEmbedding-inr w z = snd (compEquiv LiftEquiv (⊎Path.Cover≃Path (inr w) (inr z)))

isOfHLevel⊎ : (n : HLevel)
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) B
  → isOfHLevel (suc (suc n)) (A ⊎ B)
isOfHLevel⊎ n lA lB c c' =
  isOfHLevelRetract (suc n)
    (⊎Path.encode c c')
    (⊎Path.decode c c')
    (⊎Path.decodeEncode c c')
    (⊎Path.isOfHLevelCover n lA lB c c')

isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ propA _ _ (inl x) (inl y) i = inl (propA x y i)
isProp⊎ _ _ AB⊥ (inl x) (inr y) = ⊥-rec (AB⊥ x y)
isProp⊎ _ _ AB⊥ (inr x) (inl y) = ⊥-rec (AB⊥ y x)
isProp⊎ _ propB _ (inr x) (inr y) i = inr (propB x y i)

isSet⊎ : isSet A → isSet B → isSet (A ⊎ B)
isSet⊎ = isOfHLevel⊎ 0

isGroupoid⊎ : isGroupoid A → isGroupoid B → isGroupoid (A ⊎ B)
isGroupoid⊎ = isOfHLevel⊎ 1

is2Groupoid⊎ : is2Groupoid A → is2Groupoid B → is2Groupoid (A ⊎ B)
is2Groupoid⊎ = isOfHLevel⊎ 2

discrete⊎ : Discrete A → Discrete B → Discrete (A ⊎ B)
discrete⊎ decA decB (inl a) (inl a') =
  mapDec (cong inl) (λ p q → p (isEmbedding→Inj isEmbedding-inl _ _ q)) (decA a a')
discrete⊎ decA decB (inl a) (inr b') = no (λ p → lower (⊎Path.encode (inl a) (inr b') p))
discrete⊎ decA decB (inr b) (inl a') = no ((λ p → lower (⊎Path.encode (inr b) (inl a') p)))
discrete⊎ decA decB (inr b) (inr b') =
  mapDec (cong inr) (λ p q → p (isEmbedding→Inj isEmbedding-inr _ _ q)) (decB b b')

⊎Iso : Iso A C → Iso B D → Iso (A ⊎ B) (C ⊎ D)
fun (⊎Iso iac ibd) (inl x) = inl (iac .fun x)
fun (⊎Iso iac ibd) (inr x) = inr (ibd .fun x)
inv (⊎Iso iac ibd) (inl x) = inl (iac .inv x)
inv (⊎Iso iac ibd) (inr x) = inr (ibd .inv x)
rightInv (⊎Iso iac ibd) (inl x) = cong inl (iac .rightInv x)
rightInv (⊎Iso iac ibd) (inr x) = cong inr (ibd .rightInv x)
leftInv (⊎Iso iac ibd) (inl x)  = cong inl (iac .leftInv x)
leftInv (⊎Iso iac ibd) (inr x)  = cong inr (ibd .leftInv x)

⊎-equiv : A ≃ C → B ≃ D → (A ⊎ B) ≃ (C ⊎ D)
⊎-equiv p q = isoToEquiv (⊎Iso (equivToIso p) (equivToIso q))

⊎-swap-Iso : Iso (A ⊎ B) (B ⊎ A)
fun ⊎-swap-Iso (inl x) = inr x
fun ⊎-swap-Iso (inr x) = inl x
inv ⊎-swap-Iso (inl x) = inr x
inv ⊎-swap-Iso (inr x) = inl x
rightInv ⊎-swap-Iso (inl _) = refl
rightInv ⊎-swap-Iso (inr _) = refl
leftInv ⊎-swap-Iso (inl _)  = refl
leftInv ⊎-swap-Iso (inr _)  = refl

⊎-swap-≃ : A ⊎ B ≃ B ⊎ A
⊎-swap-≃ = isoToEquiv ⊎-swap-Iso

⊎-assoc-Iso : Iso ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
fun ⊎-assoc-Iso (inl (inl x)) = inl x
fun ⊎-assoc-Iso (inl (inr x)) = inr (inl x)
fun ⊎-assoc-Iso (inr x)       = inr (inr x)
inv ⊎-assoc-Iso (inl x)       = inl (inl x)
inv ⊎-assoc-Iso (inr (inl x)) = inl (inr x)
inv ⊎-assoc-Iso (inr (inr x)) = inr x
rightInv ⊎-assoc-Iso (inl _)       = refl
rightInv ⊎-assoc-Iso (inr (inl _)) = refl
rightInv ⊎-assoc-Iso (inr (inr _)) = refl
leftInv ⊎-assoc-Iso (inl (inl _))  = refl
leftInv ⊎-assoc-Iso (inl (inr _))  = refl
leftInv ⊎-assoc-Iso (inr _)        = refl

⊎-assoc-≃ : (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc-≃ = isoToEquiv ⊎-assoc-Iso

⊎-IdR-⊥-Iso : Iso (A ⊎ ⊥) A
fun ⊎-IdR-⊥-Iso (inl x) = x
inv ⊎-IdR-⊥-Iso x       = inl x
rightInv ⊎-IdR-⊥-Iso _      = refl
leftInv ⊎-IdR-⊥-Iso (inl _) = refl

⊎-IdL-⊥-Iso : Iso (⊥ ⊎ A) A
fun ⊎-IdL-⊥-Iso (inr x) = x
inv ⊎-IdL-⊥-Iso x       = inr x
rightInv ⊎-IdL-⊥-Iso _      = refl
leftInv ⊎-IdL-⊥-Iso (inr _) = refl

⊎-IdL-⊥*-Iso : ∀{ℓ} → Iso (⊥* {ℓ} ⊎ A) A
fun ⊎-IdL-⊥*-Iso (inr x) = x
inv ⊎-IdL-⊥*-Iso x       = inr x
rightInv ⊎-IdL-⊥*-Iso _      = refl
leftInv ⊎-IdL-⊥*-Iso (inr _) = refl

⊎-IdR-⊥*-Iso : ∀{ℓ} → Iso (A ⊎ ⊥* {ℓ}) A
fun ⊎-IdR-⊥*-Iso (inl x) = x
inv ⊎-IdR-⊥*-Iso x       = inl x
rightInv ⊎-IdR-⊥*-Iso _      = refl
leftInv ⊎-IdR-⊥*-Iso (inl _) = refl

⊎-IdR-⊥-≃ : A ⊎ ⊥ ≃ A
⊎-IdR-⊥-≃ = isoToEquiv ⊎-IdR-⊥-Iso

⊎-IdL-⊥-≃ : ⊥ ⊎ A ≃ A
⊎-IdL-⊥-≃ = isoToEquiv ⊎-IdL-⊥-Iso

⊎-IdR-⊥*-≃ : ∀{ℓ} → A ⊎ ⊥* {ℓ} ≃ A
⊎-IdR-⊥*-≃ = isoToEquiv ⊎-IdR-⊥*-Iso

⊎-IdL-⊥*-≃ : ∀{ℓ} → ⊥* {ℓ} ⊎ A ≃ A
⊎-IdL-⊥*-≃ = isoToEquiv ⊎-IdL-⊥*-Iso

Π⊎Iso : Iso ((x : A ⊎ B) → E x) (((a : A) → E (inl a)) × ((b : B) → E (inr b)))
fun Π⊎Iso f .fst a = f (inl a)
fun Π⊎Iso f .snd b = f (inr b)
inv Π⊎Iso (g1 , g2) (inl a) = g1 a
inv Π⊎Iso (g1 , g2) (inr b) = g2 b
rightInv Π⊎Iso (g1 , g2) i .fst a = g1 a
rightInv Π⊎Iso (g1 , g2) i .snd b = g2 b
leftInv Π⊎Iso f i (inl a) = f (inl a)
leftInv Π⊎Iso f i (inr b) = f (inr b)

Σ⊎Iso : Iso (Σ (A ⊎ B) E) ((Σ A (λ a → E (inl a))) ⊎ (Σ B (λ b → E (inr b))))
fun Σ⊎Iso (inl a , ea) = inl (a , ea)
fun Σ⊎Iso (inr b , eb) = inr (b , eb)
inv Σ⊎Iso (inl (a , ea)) = (inl a , ea)
inv Σ⊎Iso (inr (b , eb)) = (inr b , eb)
rightInv Σ⊎Iso (inl (a , ea)) = refl
rightInv Σ⊎Iso (inr (b , eb)) = refl
leftInv Σ⊎Iso (inl a , ea) = refl
leftInv Σ⊎Iso (inr b , eb) = refl

×DistL⊎Iso : Iso (A × (B ⊎ C)) ((A × B) ⊎ (A × C))
fun ×DistL⊎Iso (a , inl b) = inl (a , b)
fun ×DistL⊎Iso (a , inr c) = inr (a , c)
inv ×DistL⊎Iso (inl (a , b)) = a , inl b
inv ×DistL⊎Iso (inr (a , c)) = a , inr c
rightInv ×DistL⊎Iso (inl (a , b)) = refl
rightInv ×DistL⊎Iso (inr (a , c)) = refl
leftInv ×DistL⊎Iso (a , inl b) = refl
leftInv ×DistL⊎Iso (a , inr c) = refl

Π⊎≃ : ((x : A ⊎ B) → E x) ≃ ((a : A) → E (inl a)) × ((b : B) → E (inr b))
Π⊎≃ = isoToEquiv Π⊎Iso

Σ⊎≃ : (Σ (A ⊎ B) E) ≃ ((Σ A (λ a → E (inl a))) ⊎ (Σ B (λ b → E (inr b))))
Σ⊎≃ = isoToEquiv Σ⊎Iso
