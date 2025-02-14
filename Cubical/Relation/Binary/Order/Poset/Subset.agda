module Cubical.Relation.Binary.Order.Poset.Subset where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Functions.Embedding
open import Cubical.Functions.Fibration
open import Cubical.Functions.Preimage

open import Cubical.HITs.PropositionalTruncation as ∥₁

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Properties

open import Cubical.Relation.Binary.Order.Proset.Properties


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ₀ ℓ₁ : Level

module _
  (P : Poset ℓ ℓ')
  where
    private
      _≤_ = PosetStr._≤_ (snd P)

      is = PosetStr.isPoset (snd P)
      prop = IsPoset.is-prop-valued is

      rfl = IsPoset.is-refl is
      anti = IsPoset.is-antisym is
      trans = IsPoset.is-trans is

    module _
      (S : Embedding ⟨ P ⟩ ℓ'')
      where
        private
          f = S .snd .fst
        isDownset : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
        isDownset = ∀ x → ∀ y → y ≤ f x → y ∈ₑ S

        isPropIsDownset : isProp isDownset
        isPropIsDownset = isPropΠ3 λ _ y _ → isProp∈ₑ y S

        isUpset : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
        isUpset = ∀ x → ∀ y → f x ≤ y → y ∈ₑ S

        isPropIsUpset : isProp isUpset
        isPropIsUpset = isPropΠ3 λ _ y _ → isProp∈ₑ y S

    module _
      (A : Embedding ⟨ P ⟩ ℓ₀)
      (B : Embedding ⟨ P ⟩ ℓ₁)
      where
        module _
          (downA : isDownset A)
          (downB : isDownset B)
          where
            isDownset∩ : isDownset (A ∩ₑ B)
            isDownset∩ (x , (a , a≡x) , (b , b≡x)) y y≤x
              = (y , (downA a y (subst (y ≤_) (sym a≡x) y≤x) ,
                      downB b y (subst (y ≤_) (sym b≡x) y≤x))) , refl

            isDownset∪ : isDownset (A ∪ₑ B)
            isDownset∪ (x , A⊎B) y y≤x
              = ∥₁.rec (isProp∈ₑ y (A ∪ₑ B))
                       (⊎.rec (λ { (a , a≡x) →
                              (y , ∣ inl (downA a y (subst (y ≤_)
                                                           (sym a≡x) y≤x)) ∣₁) , refl })
                              (λ { (b , b≡x) →
                              (y , ∣ inr (downB b y (subst (y ≤_)
                                                           (sym b≡x) y≤x)) ∣₁) , refl })) A⊎B

        module _
          (upA : isUpset A)
          (upB : isUpset B)
          where
            isUpset∩ : isUpset (A ∩ₑ B)
            isUpset∩ (x , (a , a≡x) , (b , b≡x)) y x≤y
              = (y , (upA a y (subst (_≤ y) (sym a≡x) x≤y) ,
                      upB b y (subst (_≤ y) (sym b≡x) x≤y))) , refl

            isUpset∪ : isUpset (A ∪ₑ B)
            isUpset∪ (x , A⊎B) y x≤y
              = ∥₁.rec (isProp∈ₑ y (A ∪ₑ B))
                       (⊎.rec (λ { (a , a≡x) →
                              (y , ∣ inl (upA a y (subst (_≤ y)
                                                         (sym a≡x) x≤y)) ∣₁) , refl })
                              (λ { (b , b≡x) →
                              (y , ∣ inr (upB b y (subst (_≤ y)
                                                         (sym b≡x) x≤y)) ∣₁) , refl })) A⊎B

    module _
      {I : Type ℓ''}
      (S : I → Embedding ⟨ P ⟩ ℓ''')
      where
        module _
          (downS : ∀ i → isDownset (S i))
          where
            isDownset⋂ : isDownset (⋂ₑ S)
            isDownset⋂ (x , ∀x) y y≤x
              = (y , λ i → downS i (∀x i .fst) y (subst (y ≤_) (sym (∀x i .snd)) y≤x)) , refl

            isDownset⋃ : isDownset (⋃ₑ S)
            isDownset⋃ (x , ∃i) y y≤x
              = (y , (∥₁.map (λ { (i , a , a≡x) → i , downS i a y (subst (y ≤_) (sym a≡x) y≤x) }) ∃i)) , refl

        module _
          (upS : ∀ i → isUpset (S i))
          where
            isUpset⋂ : isUpset (⋂ₑ S)
            isUpset⋂ (x , ∀x) y x≤y
              = (y , λ i → upS i (∀x i .fst) y (subst (_≤ y) (sym (∀x i .snd)) x≤y)) , refl

            isUpset⋃ : isUpset (⋃ₑ S)
            isUpset⋃ (x , ∃i) y x≤y
              = (y , (∥₁.map (λ { (i , a , a≡x) → i , upS i a y (subst (_≤ y) (sym a≡x) x≤y)  }) ∃i)) , refl


    module _
      (x : ⟨ P ⟩)
      where
        principalDownset : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ')
        principalDownset = (Σ[ y ∈ ⟨ P ⟩ ] y ≤ x) , EmbeddingΣProp λ _ → prop _ x

        principalUpset : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ')
        principalUpset = (Σ[ y ∈ ⟨ P ⟩ ] x ≤ y) , EmbeddingΣProp λ _ → prop x _

    isDownsetPrincipalDownset : ∀ x → isDownset (principalDownset x)
    isDownsetPrincipalDownset x (y , y≤x) z z≤y = (z , (trans z y x z≤y y≤x)) , refl

    isUpsetPrincipalUpset : ∀ x → isUpset (principalUpset x)
    isUpsetPrincipalUpset x (y , x≤y) z y≤z = (z , (trans x y z x≤y y≤z)) , refl

    principalDownsetMembership : ∀ x y → x ≤ y
                               ≃ x ∈ₑ principalDownset y
    principalDownsetMembership x y = invEquiv (fiberEquiv _ _)

    principalUpsetMembership : ∀ x y → x ≤ y
                             ≃ y ∈ₑ principalUpset x
    principalUpsetMembership x y = invEquiv (fiberEquiv _ _)

    principalUpsetInclusion : ∀ x y → x ≤ y
                            → principalUpset y ⊆ₑ principalUpset x
    principalUpsetInclusion x y x≤y z z∈y↑
      = equivFun (principalUpsetMembership x z)
                 (trans x y z x≤y (invEq (principalUpsetMembership y z) z∈y↑))

    principalDownsetInclusion : ∀ x y → x ≤ y
                              → principalDownset x ⊆ₑ principalDownset y
    principalDownsetInclusion x y x≤y z z∈x↓
      = equivFun (principalDownsetMembership z y)
                 (trans z x y (invEq (principalDownsetMembership z x) z∈x↓) x≤y)

    principalDownsetHasGreatest : ∀ x → isGreatest (isPoset→isProset is) (principalDownset x) (x , rfl x)
    principalDownsetHasGreatest x (y , y≤x) = y≤x

    principalUpsetHasLeast : ∀ x → isLeast (isPoset→isProset is) (principalUpset x) (x , rfl x)
    principalUpsetHasLeast x (y , x≤y) = x≤y

    module _ (S : Embedding ⟨ P ⟩ ℓ'') where
      private f = str S .fst

      -- Not to be confused with the notion of a 'closure operator' (a monad on a poset) in Poset.Mappings
      -- Though they are related, as the downward/upward closure is a closure operator on the poset of embeddings
      -- (not proved here)
      DownwardClosure : Embedding ⟨ P ⟩ (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
      DownwardClosure = (Σ[ x ∈ ⟨ P ⟩ ] ∃[ y ∈ ⟨ S ⟩ ] x ≤ f y) , EmbeddingΣProp λ _ → squash₁

      UpwardClosure : Embedding ⟨ P ⟩ (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
      UpwardClosure = (Σ[ x ∈ ⟨ P ⟩ ] ∃[ y ∈ ⟨ S ⟩ ] f y ≤ x) , EmbeddingΣProp λ _ → squash₁

      DownwardClosureMembership : ∀ x → (∃[ y ∈ ⟨ S ⟩ ] x ≤ f y)
                                ≃ x ∈ₑ DownwardClosure
      DownwardClosureMembership x = invEquiv (fiberEquiv _ _)

      UpwardClosureMembership : ∀ x → (∃[ y ∈ ⟨ S ⟩ ] f y ≤ x)
                              ≃ x ∈ₑ UpwardClosure
      UpwardClosureMembership x = invEquiv (fiberEquiv _ _)

      isDownsetDownwardClosure : isDownset DownwardClosure
      isDownsetDownwardClosure (x , p) y y≤x = equivFun (DownwardClosureMembership y) $ ∥₁.map (map-snd (trans _ _ _ y≤x)) p

      isUpsetUpwardClosure : isUpset UpwardClosure
      isUpsetUpwardClosure (x , p) y x≤y = equivFun (UpwardClosureMembership y) $ ∥₁.map (map-snd (flip (trans _ _ _) x≤y)) p

      is⊆DownwardClosure : S ⊆ₑ DownwardClosure
      is⊆DownwardClosure x (y , fy≡x) = equivFun (DownwardClosureMembership x) $ ∣ y , subst (_≤ f y) fy≡x (rfl _) ∣₁

      is⊆UpwardClosure : S ⊆ₑ UpwardClosure
      is⊆UpwardClosure x (y , fy≡x) = equivFun (UpwardClosureMembership x) $ ∣ y , subst (f y ≤_) fy≡x (rfl _) ∣₁

      -- universal property
      module _ (S' : Embedding ⟨ P ⟩ ℓ''') (S⊆S' : S ⊆ₑ S') where
        DownwardClosureUniversal : isDownset S' → DownwardClosure ⊆ₑ S'
        DownwardClosureUniversal SDown x x∈D = ∃-rec (isProp∈ₑ _ S') (λ y x≤y →
            let fib = S⊆S' (f y) (y , refl) in
            SDown (fib .fst) x (subst (x ≤_) (sym (fib .snd)) x≤y)
          ) (invEq (DownwardClosureMembership x) x∈D)

        UpwardClosureUniversal : isUpset S' → UpwardClosure ⊆ₑ S'
        UpwardClosureUniversal SUp x x∈U = ∃-rec (isProp∈ₑ _ S') (λ y y≤x →
            let fib = S⊆S' (f y) (y , refl) in
            SUp (fib .fst) x (subst (_≤ x) (sym (fib .snd)) y≤x)
          ) (invEq (UpwardClosureMembership x) x∈U)

    module _ (A : Embedding ⟨ P ⟩ ℓ₀) (B : Embedding ⟨ P ⟩ ℓ₁) (A⊆B : A ⊆ₑ B) where
      DownwardClosureInclusion : DownwardClosure A ⊆ₑ DownwardClosure B
      DownwardClosureInclusion = DownwardClosureUniversal A (DownwardClosure B) (
          isTrans⊆ₑ A B (DownwardClosure B) A⊆B (is⊆DownwardClosure B)
        ) (isDownsetDownwardClosure B)

      UpwardClosureInclusion : UpwardClosure A ⊆ₑ UpwardClosure B
      UpwardClosureInclusion = UpwardClosureUniversal A (UpwardClosure B) (
          isTrans⊆ₑ A B (UpwardClosure B) A⊆B (is⊆UpwardClosure B)
        ) (isUpsetUpwardClosure B)

    module _
      (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
      where
        isPrincipalDownset : Type _
        isPrincipalDownset = Σ[ x ∈ ⟨ P ⟩ ] S ≡ (principalDownset x)

        isPropIsPrincipalDownset : isProp isPrincipalDownset
        isPropIsPrincipalDownset (x , S≡x↓) (y , S≡y↓)
          = Σ≡Prop (λ x → isSetEmbedding S (principalDownset x))
                    (anti x y x≤y y≤x)
          where x≤y : x ≤ y
                x≤y = invEq (principalDownsetMembership x y)
                            (subst (x ∈ₑ_)
                                   (sym S≡x↓ ∙ S≡y↓)
                                   (equivFun (principalDownsetMembership x x) (rfl x)))

                y≤x : y ≤ x
                y≤x = invEq (principalDownsetMembership y x)
                            (subst (y ∈ₑ_)
                                   (sym S≡y↓ ∙ S≡x↓)
                                   (equivFun (principalDownsetMembership y y) (rfl y)))

        isPrincipalUpset : Type _
        isPrincipalUpset = Σ[ x ∈ ⟨ P ⟩ ] S ≡ (principalUpset x)

        isPropIsPrincipalUpset : isProp isPrincipalUpset
        isPropIsPrincipalUpset (x , S≡x↑) (y , S≡y↑)
          = Σ≡Prop (λ x → isSetEmbedding S (principalUpset x))
                    (anti x y x≤y y≤x)
          where x≤y : x ≤ y
                x≤y = invEq (principalUpsetMembership x y)
                             (subst (y ∈ₑ_)
                                    (sym S≡y↑ ∙ S≡x↑)
                                    (equivFun (principalUpsetMembership y y) (rfl y)))

                y≤x : y ≤ x
                y≤x = invEq (principalUpsetMembership y x)
                            (subst (x ∈ₑ_)
                                   (sym S≡x↑ ∙ S≡y↑)
                                   (equivFun (principalUpsetMembership x x) (rfl x)))

        isPrincipalDownset→isDownset : isPrincipalDownset → (isDownset S)
        isPrincipalDownset→isDownset (x , p)
          = transport⁻ (cong isDownset p) (isDownsetPrincipalDownset x)

        isPrincipalUpset→isUpset : isPrincipalUpset → (isUpset S)
        isPrincipalUpset→isUpset (x , p)
          = transport⁻ (cong isUpset p) (isUpsetPrincipalUpset x)

    isPrincipalDownset→hasGreatest : (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
                                   → isPrincipalDownset S
                                   → Greatest (isPoset→isProset is) S
    isPrincipalDownset→hasGreatest _ (x , S≡x↓)
      = transport⁻ (cong (Greatest (isPoset→isProset is)) S≡x↓)
                   ((x , rfl x) , principalDownsetHasGreatest x)

    isDownsetWithGreatest→isPrincipalDownset : (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
                                             → isDownset S
                                             → Greatest (isPoset→isProset is) S
                                             → isPrincipalDownset S
    isDownsetWithGreatest→isPrincipalDownset (S , f , emb) down (x , grt)
      = f x , isAntisym⊆ₑ (S , f , emb)
                          (principalDownset (f x))
                          (λ y (w , fw≡y) → equivFun (principalDownsetMembership y (f x))
                                                     (subst (_≤ f x) fw≡y (grt w)))
                           λ y ((w , w≤fx) , w≡y) → down x y (subst (_≤ f x) w≡y w≤fx)

    isPrincipalUpset→hasLeast : (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
                              → isPrincipalUpset S
                              → Least (isPoset→isProset is) S
    isPrincipalUpset→hasLeast _ (x , S≡x↑)
      = transport⁻ (cong (Least (isPoset→isProset is)) S≡x↑)
                   ((x , rfl x) , principalUpsetHasLeast x)

    isUpsetWithLeast→isPrincipalUpset : (S : Embedding ⟨ P ⟩ (ℓ-max ℓ ℓ'))
                                      → isUpset S
                                      → Least (isPoset→isProset is) S
                                      → isPrincipalUpset S
    isUpsetWithLeast→isPrincipalUpset (S , f , emb) up (x , lst)
      = f x , isAntisym⊆ₑ (S , f , emb)
                          (principalUpset (f x))
                          (λ y (w , fw≡y) → equivFun (principalUpsetMembership (f x) y)
                                                     (subst (f x ≤_) fw≡y (lst w)))
                           λ y ((w , fx≤w) , w≡y) → up x y (subst (f x ≤_) w≡y fx≤w)

module PosetDownset (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  _↓ : P → Embedding P (ℓ-max ℓ ℓ')
  u ↓ = principalDownset P' u

  _↓ᴾ : P → Poset (ℓ-max ℓ ℓ') ℓ'
  fst (u ↓ᴾ) = (u ↓) .fst
  PosetStr._≤_ (snd (u ↓ᴾ)) v w = v .fst ≤ w .fst
  PosetStr.isPoset (snd (u ↓ᴾ)) =
    isPosetInduced
      (PosetStr.isPoset (snd P'))
       _
      (principalDownset P' u .snd)

module PosetUpset (P' : Poset ℓ ℓ') where
  private P = ⟨ P' ⟩
  open PosetStr (snd P')

  _↑ : P → Embedding P (ℓ-max ℓ ℓ')
  u ↑ = principalUpset P' u

  _↑ᴾ : P → Poset (ℓ-max ℓ ℓ') ℓ'
  fst (u ↑ᴾ) = (u ↑) .fst
  PosetStr._≤_ (snd (u ↑ᴾ)) v w = v .fst ≤ w .fst
  PosetStr.isPoset (snd (u ↑ᴾ)) =
    isPosetInduced
      (PosetStr.isPoset (snd P'))
       _
      (principalUpset P' u .snd)
