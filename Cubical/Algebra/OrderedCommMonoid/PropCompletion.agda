{-# OPTIONS --safe --postfix-projections #-}
module Cubical.Algebra.OrderedCommMonoid.PropCompletion where
{-
  The completion of an ordered monoid, viewed as monoidal prop-enriched category.
  This is used in the construction of the upper naturals, which is an idea of David
  Jaz Myers presented here

  https://felix-cherubini.de/myers-slides-II.pdf

  It should be straight forward, but tedious,
  to generalize this to enriched monoidal categories.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Logic
open import Cubical.Functions.Embedding

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation renaming (rec to propTruncRec; rec2 to propTruncRec2)

open import Cubical.Algebra.CommMonoid.Base
open import Cubical.Algebra.OrderedCommMonoid

open import Cubical.Relation.Binary.Order.Poset

private
  variable
    ℓ : Level

module PropCompletion (ℓ : Level) (M : OrderedCommMonoid ℓ ℓ) where
  open OrderedCommMonoidStr (snd M)
  _≤p_ : fst M → fst M → hProp ℓ
  n ≤p m = (n ≤ m) , (is-prop-valued _ _)

  isUpwardClosed : (s : fst M → hProp ℓ) → Type _
  isUpwardClosed s = (n m : fst M) → n ≤ m → fst (s n) → fst (s m)

  isPropUpwardClosed : (N : fst M → hProp ℓ) → isProp (isUpwardClosed N)
  isPropUpwardClosed N =
    isPropΠ4 (λ _ m _ _ → snd (N m))

  isSetM→Prop : isSet (fst M → hProp ℓ)
  isSetM→Prop = isOfHLevelΠ 2 λ _ → isSetHProp

  M↑ : Type _
  M↑ = Σ[ s ∈ (fst M → hProp ℓ)] isUpwardClosed s

  isSetM↑ : isSet M↑
  isSetM↑ = isOfHLevelΣ 2 isSetM→Prop λ s → isOfHLevelSuc 1 (isPropUpwardClosed s)

  _isUpperBoundOf_ : fst M → M↑ → Type ℓ
  n isUpperBoundOf s = fst (fst s n)

  isBounded : (s : M↑) → Type _
  isBounded s = ∃[ m ∈ (fst M) ] (m isUpperBoundOf s)

  isPropIsBounded : (s : M↑) → isProp (isBounded s)
  isPropIsBounded s = isPropPropTrunc

  _^↑ : fst M → M↑
  n ^↑ = n ≤p_ , isUpwardClosed≤
    where
      isUpwardClosed≤ : {m : fst M} → isUpwardClosed (m ≤p_)
      isUpwardClosed≤ = λ {_ _ n≤k m≤n → is-trans _ _ _ m≤n n≤k}

  isBounded^ : (m : fst M) → isBounded (m ^↑)
  isBounded^ m = ∣ (m , (is-refl m)) ∣₁

  1↑ : M↑
  1↑ = ε ^↑

  _·↑_ : M↑ → M↑ → M↑
  s ·↑ l = seq , seqIsUpwardClosed
         where
           seq : fst M → hProp ℓ
           seq n = (∃[ (a , b) ∈ (fst M) × (fst M) ] fst ((fst s a) ⊓ (fst l b) ⊓ ((a · b) ≤p n) )) ,
                   isPropPropTrunc
           seqIsUpwardClosed : isUpwardClosed seq
           seqIsUpwardClosed n m n≤m =
             propTruncRec
               isPropPropTrunc
               λ {((a , b) , wa , (wb , a·b≤n)) → ∣ (a , b) , wa , (wb , is-trans _ _ _ a·b≤n n≤m) ∣₁}

  ·presBounded : (s l : M↑) (bs : isBounded s) (bl : isBounded l) → isBounded (s ·↑ l)
  ·presBounded s l =
    propTruncRec2
      isPropPropTrunc
      λ {(m , s≤m) (k , l≤k)
          → ∣ (m · k) , ∣ (m , k) , (s≤m , (l≤k , (is-refl (m · k)))) ∣₁ ∣₁
        }

  {- convenience functions for the proof that ·↑ is the multiplication of a monoid -}
  typeAt : fst M → M↑ → Type _
  typeAt n s = fst (fst s n)

  M↑Path : {s l : M↑} → ((n : fst M) → typeAt n s ≡ typeAt n l) → s ≡ l
  M↑Path {s = s} {l = l} pwPath = path
     where
       seqPath : fst s ≡ fst l
       seqPath i n =
         Σ≡Prop (λ _ → isPropIsProp) {u = fst s n} {v = fst l n} (pwPath n) i

       path : s ≡ l
       path = Σ≡Prop isPropUpwardClosed seqPath

  pathFromImplications : (s l : M↑)
           → ((n : fst M) → typeAt n s → typeAt n l)
           → ((n : fst M) → typeAt n l → typeAt n s)
           → s ≡ l
  pathFromImplications s l s→l l→s =
      M↑Path λ n → cong fst (propPath n)
            where propPath : (n : fst M) → fst s n ≡ fst l n
                  propPath n = ⇒∶ s→l n
                               ⇐∶ l→s n


  ^↑Pres· : (x y : fst M) → (x · y) ^↑ ≡ (x ^↑) ·↑ (y ^↑)
  ^↑Pres· x y = pathFromImplications ((x · y) ^↑) ((x ^↑) ·↑ (y ^↑)) (⇐) ⇒
    where
      ⇐ : (n : fst M) → typeAt n ((x · y) ^↑) → typeAt n ((x ^↑) ·↑ (y ^↑))
      ⇐ n x·y≤n = ∣ (x , y) , ((is-refl _) , ((is-refl _) , x·y≤n)) ∣₁

      ⇒ : (n : fst M) → typeAt n ((x ^↑) ·↑ (y ^↑)) → typeAt n ((x · y) ^↑)
      ⇒ n = propTruncRec
              (snd (fst ((x · y) ^↑) n))
              λ {((m , l) , x≤m , (y≤l , m·l≤n))
                  → is-trans _ _ _
                             (is-trans _ _ _ (MonotoneR x≤m)
                                             (MonotoneL y≤l))
                             m·l≤n
                }

  ·↑Comm : (s l : M↑) → s ·↑ l ≡ l ·↑ s
  ·↑Comm s l = M↑Path λ n → cong fst (propPath n)
    where implication : (s l : M↑) (n : fst M) → fst (fst (s ·↑ l) n) → fst (fst (l ·↑ s) n)
          implication s l n = propTruncRec
                             isPropPropTrunc
                             (λ {((a , b) , wa , (wb , a·b≤n))
                               → ∣ (b , a) , wb , (wa , subst (λ k → fst (k ≤p n)) (·Comm a b) a·b≤n) ∣₁ })
          propPath : (n : fst M) → fst (s ·↑ l) n ≡ fst (l ·↑ s) n
          propPath n = ⇒∶ implication s l n
                       ⇐∶ implication l s n

  ·↑Rid : (s : M↑) → s ·↑ 1↑ ≡ s
  ·↑Rid s = pathFromImplications (s ·↑ 1↑) s (⇒) ⇐
    where ⇒ : (n : fst M) → typeAt n (s ·↑ 1↑) → typeAt n s
          ⇒ n = propTruncRec
                  (snd (fst s n))
                  (λ {((a , b) , sa , (1b , a·b≤n))
                     → (snd s) a n ( subst (_≤ n) (·IdR a) (is-trans _ _ _ (MonotoneL 1b) a·b≤n)) sa })
          ⇐ : (n : fst M) → typeAt n s → typeAt n (s ·↑ 1↑)
          ⇐ n = λ sn → ∣ (n , ε) , (sn , (is-refl _ , subst (_≤ n) (sym (·IdR n)) (is-refl _))) ∣₁

  ·↑Assoc : (s l k : M↑) → s ·↑ (l ·↑ k) ≡ (s ·↑ l) ·↑ k
  ·↑Assoc s l k = pathFromImplications (s ·↑ (l ·↑ k)) ((s ·↑ l) ·↑ k) (⇒) ⇐
    where ⇒ : (n : fst M) → typeAt n (s ·↑ (l ·↑ k)) → typeAt n ((s ·↑ l) ·↑ k)
          ⇒ n = propTruncRec
                isPropPropTrunc
                λ {((a , b) , sa , (l·kb , a·b≤n))
                     → propTruncRec
                         isPropPropTrunc
                         (λ {((a' , b') , la' , (kb' , a'·b'≤b))
                         → ∣ ((a · a') , b') , ∣ (a , a') , (sa , (la' , is-refl _)) ∣₁ , kb' ,
                             (let a·⟨a'·b'⟩≤n = (is-trans _ _ _ (MonotoneL a'·b'≤b) a·b≤n)
                              in subst (_≤ n) (·Assoc a a' b') a·⟨a'·b'⟩≤n) ∣₁
                            }) l·kb
                   }
          ⇐ : _
          ⇐ n = propTruncRec
                isPropPropTrunc
                λ {((a , b) , s·l≤a , (k≤b , a·b≤n))
                     → propTruncRec
                         isPropPropTrunc
                         (λ {((a' , b') , s≤a' , (l≤b' , a'·b'≤a))
                         → ∣ (a' , b' · b) , s≤a' , ( ∣ (b' , b) , l≤b' , (k≤b , is-refl _) ∣₁ ,
                             (let ⟨a'·b'⟩·b≤n = (is-trans _ _ _ (MonotoneR a'·b'≤a) a·b≤n)
                              in subst (_≤ n) (sym (·Assoc a' b' b)) ⟨a'·b'⟩·b≤n) ) ∣₁
                            }) s·l≤a
                   }

  asCommMonoid : CommMonoid (ℓ-suc ℓ)
  asCommMonoid = makeCommMonoid 1↑ _·↑_ isSetM↑ ·↑Assoc ·↑Rid ·↑Comm

  {-
    Poset structure on M↑
  -}
  _≤↑_ : (s l : M↑) → Type _
  s ≤↑ l = (m : fst M) → fst ((fst l) m) → fst ((fst s) m)

  isBounded→≤↑ : (s : M↑) → isBounded s → ∃[ m ∈ fst M ] (s ≤↑ (m ^↑))
  isBounded→≤↑ s =
    propTruncRec
      isPropPropTrunc
      λ {(m , mIsBound)
           → ∣ m , (λ n m≤n → snd s m n m≤n mIsBound) ∣₁
        }

  ≤↑IsProp : (s l : M↑) → isProp (s ≤↑ l)
  ≤↑IsProp s l = isPropΠ2 (λ x p → snd (fst s x))

  ≤↑IsRefl : (s : M↑) → s ≤↑ s
  ≤↑IsRefl s = λ m x → x

  ≤↑IsTrans : (s l t : M↑) → s ≤↑ l → l ≤↑ t → s ≤↑ t
  ≤↑IsTrans s l t p q x = (p x) ∘ (q x)

  ≤↑IsAntisym : (s l : M↑) → s ≤↑ l → l ≤↑ s → s ≡ l
  ≤↑IsAntisym s l p q = pathFromImplications _ _ q p

  {-
    Compatability with the monoid structure
  -}
  ·↑IsRMonotone : (l t s : M↑) → l ≤↑ t → (l ·↑ s) ≤↑ (t ·↑ s)
  ·↑IsRMonotone l t s p x =
    propTruncRec
      isPropPropTrunc
      λ { ((a , b) , l≤a , (s≤b , a·b≤x)) → ∣ (a , b) , p a l≤a , s≤b , a·b≤x ∣₁}

  ·↑IsLMonotone : (l t s : M↑) → l ≤↑ t → (s ·↑ l) ≤↑ (s ·↑ t)
  ·↑IsLMonotone l t s p x =
    propTruncRec
      isPropPropTrunc
      λ {((a , b) , s≤a , (l≤b , a·b≤x)) → ∣ (a , b) , s≤a , p b l≤b , a·b≤x ∣₁}

  asOrderedCommMonoid : OrderedCommMonoid (ℓ-suc ℓ) ℓ
  asOrderedCommMonoid .fst = _
  asOrderedCommMonoid .snd .OrderedCommMonoidStr._≤_ = _≤↑_
  asOrderedCommMonoid .snd .OrderedCommMonoidStr._·_ = _·↑_
  asOrderedCommMonoid .snd .OrderedCommMonoidStr.ε = 1↑
  asOrderedCommMonoid .snd .OrderedCommMonoidStr.isOrderedCommMonoid =
    IsOrderedCommMonoidFromIsCommMonoid
          (CommMonoidStr.isCommMonoid (snd asCommMonoid))
          ≤↑IsProp ≤↑IsRefl ≤↑IsTrans ≤↑IsAntisym ·↑IsRMonotone ·↑IsLMonotone

  boundedSubstructure : OrderedCommMonoid (ℓ-suc ℓ) ℓ
  boundedSubstructure =
    makeOrderedSubmonoid
      asOrderedCommMonoid
      (λ s → (isBounded s , isPropIsBounded s))
      ·presBounded
      (isBounded^ ε)

PropCompletion :
    OrderedCommMonoid ℓ ℓ
  → OrderedCommMonoid (ℓ-suc ℓ) ℓ
PropCompletion M = PropCompletion.asOrderedCommMonoid _ M

BoundedPropCompletion :
     OrderedCommMonoid ℓ ℓ
  → OrderedCommMonoid (ℓ-suc ℓ) ℓ
BoundedPropCompletion M = PropCompletion.boundedSubstructure _ M

isSetBoundedPropCompletion :
     (M : OrderedCommMonoid ℓ ℓ)
   → isSet (⟨ BoundedPropCompletion M ⟩)
isSetBoundedPropCompletion M =
  isSetΣSndProp (isSetOrderedCommMonoid (PropCompletion M))
                λ x → PropCompletion.isPropIsBounded _ M x
