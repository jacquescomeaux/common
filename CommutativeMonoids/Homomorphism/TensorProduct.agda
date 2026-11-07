{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Algebra using (CommutativeMonoid)
open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism; CommutativeMonoids; mk-⇒)

module CommutativeMonoids.Homomorphism.TensorProduct {c ℓ : Level} where

import CommutativeMonoids.Construction.CongruenceClosure {c} {ℓ} as CongruenceClosure

open import Algebra.Construct.DirectProduct using () renaming (commutativeMonoid to _⊕_)
open import CommutativeMonoids.Construction.FormalSum c ℓ using (⅀; FormalSum)
open import CommutativeMonoids.Construction.TensorProduct {c} {ℓ} as ⊗ using (_⊗₀_; module Universal; module Tensor)
open import Data.Product using (_,_) renaming (map to ×-map)
open import Function using (Func)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure)
open import Setoids.Multiset c ℓ using (pureₛ)

open CommutativeMonoids using (_∘_)
open Func
open SymClosure

module _
    {A B C D : CommutativeMonoid c (c ⊔ ℓ)}
    (f : CommutativeMonoidHomomorphism A B)
    (g : CommutativeMonoidHomomorphism C D)
  where

  private
    module B = CommutativeMonoid B
    module D = CommutativeMonoid D
    module ⅀B⊕D = CommutativeMonoid (⅀ (B ⊕ D))
    module A⊕C = CommutativeMonoid (A ⊕ C)
    module B⊕D = CommutativeMonoid (B ⊕ D)
    module f = CommutativeMonoidHomomorphism f
    module g = CommutativeMonoidHomomorphism g

  open Tensor B D using (_~_; eval)
  open CongruenceClosure (⅀ (B ⊕ D)) (_~_) using (_~[_]_; one-step)
  open _~_

  ⟦_⟧ : A⊕C.Carrier → B⊕D.Carrier
  ⟦_⟧ = ×-map f.⟦_⟧ g.⟦_⟧

  ⟦⟧-cong : {x y : A⊕C.Carrier} → x A⊕C.≈ y → ⟦ x ⟧ B⊕D.≈ ⟦ y ⟧
  ⟦⟧-cong = ×-map f.⟦⟧-cong g.⟦⟧-cong

  _×ₘ_ : CommutativeMonoidHomomorphism (A ⊕ C) (B ⊕ D)
  _×ₘ_ = mk-⇒ record
      { ⟦_⟧ = ⟦_⟧
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = ⟦⟧-cong }
              ; homo = λ (a , b) (c , d) → f.homo a c , g.homo b d
              }
          ; ε-homo = f.ε-homo , g.ε-homo
          }
      }

  _⊗₁_ : CommutativeMonoidHomomorphism (A ⊗₀ C) (B ⊗₀ D)
  _⊗₁_ =
      Universal.u!
        (eval ∘ FormalSum.F.₁ _×ₘ_)
        (λ {y} → one-step (cong pureₛ (f.ε-homo , D.refl) ~[ fwd (εˡ g.⟦ y ⟧) ] ⅀B⊕D.refl))
        (λ {x} → one-step (cong pureₛ (B.refl , g.ε-homo) ~[ fwd (εʳ f.⟦ x ⟧) ] ⅀B⊕D.refl))
        (λ {x₁ x₂ y} → one-step (_~[_]_ {ctx = ⅀B⊕D.ε} ⅀B⊕D.refl (fwd (∙ˡ f.⟦ x₁ ⟧ f.⟦ x₂ ⟧ g.⟦ y ⟧)) (cong pureₛ (B.sym (f.homo x₁ x₂) , D.refl))))
        (λ {x y₁ y₂} → one-step (_~[_]_ {ctx = ⅀B⊕D.ε} ⅀B⊕D.refl (fwd (∙ʳ f.⟦ x ⟧ g.⟦ y₁ ⟧ g.⟦ y₂ ⟧)) (cong pureₛ (B.refl , D.sym (g.homo y₁ y₂)))))

  infixr 10 _⊗₁_
