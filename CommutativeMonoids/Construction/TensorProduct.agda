{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import Level using (Level; _⊔_)

module CommutativeMonoids.Construction.TensorProduct {c ℓ : Level} where

import CommutativeMonoids.Construction.Presented {c} {ℓ} as Presented

open import Algebra.Construct.DirectProduct using () renaming (commutativeMonoid to _⊕_)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism)
open import CommutativeMonoids.Construction.FormalSum c ℓ using (⅀)
open import CommutativeMonoids.FreeForget.Adjunction c ℓ using (foldMap)
open import CommutativeMonoids.FreeForget.Forget c (c ⊔ ℓ) using () renaming (Underlying to U)
open import CommutativeMonoids.FreeForget.Free c (c ⊔ ℓ) using (Free) renaming (FreeCommutativeMonoid to F)
open import Data.List using ([_]; _++_; [])
open import Data.Product using (_,_)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Relation.Binary using (Rel)

module Tensor (M N : CommutativeMonoid c (c ⊔ ℓ)) where

  private
    module M = CommutativeMonoid M
    module N = CommutativeMonoid N

  -- Formal sums of M⊕N terms
  ⅀M⊕N : CommutativeMonoid c (c ⊔ ℓ)
  ⅀M⊕N = ⅀ (M ⊕ N)

  open CommutativeMonoid ⅀M⊕N using () renaming (Carrier to Expr) public

  -- Bilinearity laws
  data _~_ : Rel Expr c where
    εˡ : (y : N.Carrier) → [ M.ε , y ] ~ []
    εʳ : (x : M.Carrier) → [ x , N.ε ] ~ []
    ∙ˡ : (x₁ x₂ : M.Carrier) (y : N.Carrier) → [ x₁ , y ] ++ [ x₂ , y ] ~ [ x₁ M.∙ x₂ , y ]
    ∙ʳ : (x : M.Carrier) (y₁ y₂ : N.Carrier) → [ x , y₁ ] ++ [ x , y₂ ] ~ [ x , y₁ N.∙ y₂ ]

  infix 4 _~_

  open Presented ⅀M⊕N _~_ using () renaming (M/≋ to M⊗N; π to eval) public

module _ {M N X : CommutativeMonoid c (c ⊔ ℓ)} where

  private
    module M = CommutativeMonoid M
    module N = CommutativeMonoid N

  open Tensor M N
  open Presented ⅀M⊕N _~_ using () renaming (module Universal to Univ)

  -- The eval homomorphism from ⅀M⊕N to the tensor product M⊗N is universal
  -- among bilinear interpretations.
  -- Given another interpretation function kₘ : ⅀M⊕N ⇒ X such that
  -- ε * b ≈ ε
  -- a * ε ≈ ε
  -- a * c + b * c ≈ (a + b) * y
  -- a * b + a * c ≈ a * (b + c)
  -- there is a unique monoid homomorphism u! : M⊗N ⇒ X
  -- such that kₘ ≈ u! ∘ eval.
  module Universal (kₘ : CommutativeMonoidHomomorphism (⅀ (M ⊕ N)) X) where

    private
      module CMon = CommutativeMonoids

    open CommutativeMonoidHomomorphism kₘ
    open CMon using (_∘_)
    open CommutativeMonoid X renaming (_∙_ to infixl 6 _+_)

    _*_ : M.Carrier → N.Carrier → Carrier
    _*_ x y = ⟦ [ x , y ] ⟧

    infixl 7 _*_

    module Induced
        (≈-εˡ : {y : N.Carrier} → M.ε * y ≈ ε)
        (≈-εʳ : {x : M.Carrier} → x * N.ε ≈ ε)
        (≈-∙ˡ : {x₁ x₂ : M.Carrier} {y : N.Carrier} → x₁ * y + x₂ * y ≈ (x₁ M.∙ x₂) * y)
        (≈-∙ʳ : {x : M.Carrier} {y₁ y₂ : N.Carrier} → x * y₁ + x * y₂ ≈ x * (y₁ N.∙ y₂))
      where

      open _~_

      k-resp : {x y : Expr} → x ~ y → ⟦ x ⟧ ≈ ⟦ y ⟧
      k-resp (εˡ y) = trans ≈-εˡ (sym ε-homo)
      k-resp (εʳ x) = trans ≈-εʳ (sym ε-homo)
      k-resp (∙ˡ x₁ x₂ y) = trans (homo [ x₁ , y ] [ x₂ , y ]) ≈-∙ˡ
      k-resp (∙ʳ x y₁ y₂) = trans (homo [ x , y₁ ] [ x , y₂ ]) ≈-∙ʳ

      open Univ kₘ k-resp renaming (induced to u!) public

    open Induced using (u!; factors; unique) public

  -- Given a bilinear function _*_ : U M → U N → U X (with respect to the _+_ and ε on X),
  -- there is a unique monoid homomorphism from M⊗N to X through
  -- which the interpretation function induced by _*_ factors.
  module Universal′ (k : U (M ⊕ N) ⟶ₛ U X) where

    open CommutativeMonoid X renaming (_∙_ to infixl 6 _+_)

    _*_ : M.Carrier → N.Carrier → Carrier
    _*_ x y = k ⟨$⟩ (x , y)

    infixl 7 _*_

    -- Use _*_ to evaluate a formal sum of M×N-terms into X
    kₘ : CommutativeMonoidHomomorphism (⅀ (M ⊕ N)) X
    kₘ = foldMap {U (M ⊕ N)} {X} k

    open Universal kₘ renaming (_*_ to _⊛_)

    ⊛-* : {x : M.Carrier} {y : N.Carrier} → x ⊛ y ≈ x * y
    ⊛-* {x} {y} = identityʳ (x * y)

    *-⊛ : {x : M.Carrier} {y : N.Carrier} → x * y ≈ x ⊛ y
    *-⊛ = sym ⊛-*

    module _
        (≈-εˡ : {y : N.Carrier} → M.ε * y ≈ ε)
        (≈-εʳ : {x : M.Carrier} → x * N.ε ≈ ε)
        (≈-∙ˡ : {x₁ x₂ : M.Carrier} {y : N.Carrier} → x₁ * y + x₂ * y ≈ (x₁ M.∙ x₂) * y)
        (≈-∙ʳ : {x : M.Carrier} {y₁ y₂ : N.Carrier} → x * y₁ + x * y₂ ≈ x * (y₁ N.∙ y₂))
      where

      open Induced
          (trans ⊛-* ≈-εˡ)
          (trans ⊛-* ≈-εʳ)
          (trans (∙-cong ⊛-* ⊛-*) (trans ≈-∙ˡ *-⊛))
          (trans (∙-cong ⊛-* ⊛-*) (trans ≈-∙ʳ *-⊛))
        using (u!; factors; unique)
        public

open Tensor renaming (M⊗N to infixr 10 _⊗₀_) public
