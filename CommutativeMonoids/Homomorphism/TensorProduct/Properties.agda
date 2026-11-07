{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module CommutativeMonoids.Homomorphism.TensorProduct.Properties {c ℓ : Level} where

open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoids; CommutativeMonoidHomomorphism)
open import CommutativeMonoids.Construction.FormalSum c ℓ using (FormalSum)
open import CommutativeMonoids.Construction.TensorProduct {c} {ℓ} using (_⊗₀_; module Tensor)
open import CommutativeMonoids.Homomorphism.TensorProduct {c} {ℓ} using (_×ₘ_; _⊗₁_)
open import Data.List.Properties using (map-∘; map-cong; map-id)
open import Data.Product using (dmap)

open CommutativeMonoids {c} {c ⊔ ℓ} using (_∘_; id; _≈_; ∘-resp-≈ʳ)

⊗₁-resp-∘
    : {A B C D E F : CommutativeMonoid c (c ⊔ ℓ)}
      {f : CommutativeMonoidHomomorphism B C}
      {g : CommutativeMonoidHomomorphism A B}
      {h : CommutativeMonoidHomomorphism E F}
      {k : CommutativeMonoidHomomorphism D E}
    → (f ∘ g) ⊗₁ (h ∘ k) ≈ f ⊗₁ h ∘ g ⊗₁ k
⊗₁-resp-∘ {B = B} {C} {E = E} {F} {f} {g} {h} {k} x = C⊗F.reflexive (map-∘ x)
  where
    module C⊗F = CommutativeMonoid (C ⊗₀ F)

⊗₁-resp-id
    : {M N : CommutativeMonoid c (c ⊔ ℓ)}
    → id {M} ⊗₁ id {N} ≈ id {M ⊗₀ N}
⊗₁-resp-id {M} {N} x = M⊗N.reflexive (map-id x)
  where
    module M⊗N = CommutativeMonoid (M ⊗₀ N)

⊗₁-resp-≈
    : {A B C D : CommutativeMonoid c (c ⊔ ℓ)}
      {f h : CommutativeMonoidHomomorphism A B}
      {g k : CommutativeMonoidHomomorphism C D}
    → f ≈ h
    → g ≈ k
    → f ⊗₁ g ≈ h ⊗₁ k
⊗₁-resp-≈ {A} {B} {C} {D} {f} {h} {g} {k} f≈h g≈k =
    ∘-resp-≈ʳ
      {f = FormalSum.F.₁ (f ×ₘ g)}
      {FormalSum.F.₁ (h ×ₘ k)}
      {eval}
      (FormalSum.F.F-resp-≈ {f = f ×ₘ g} {h ×ₘ k} f×ₘg≈h×ₘk)
  where
    open Tensor B D using (eval)
    f×ₘg≈h×ₘk : f ×ₘ g ≈ h ×ₘ k
    f×ₘg≈h×ₘk = dmap f≈h g≈k
