{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeMonoid)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; _Preserves_⟶_)

module CommutativeMonoids.Construction.Presented
    {c ℓ q : Level}
    (M : CommutativeMonoid c (c ⊔ ℓ ⊔ q))
    (open CommutativeMonoid M)
    (R : Rel Carrier q)
    where

import CommutativeMonoids.Construction.CongruenceClosure {c} {ℓ} as CongruenceClosure
import CommutativeMonoids.Construction.Quotient {c} {c ⊔ ℓ ⊔ q} as Quotient

open import CommutativeMonoids.Category using (CommutativeMonoidHomomorphism)

open CongruenceClosure M R public
open Quotient M ≋-congruence using (M/≋; π) public

private
  module Q = Quotient M ≋-congruence

-- Universal property of the presented commutative monoid
module Universal
    {N : CommutativeMonoid c (c ⊔ ℓ ⊔ q)}
    -- A homomorphism that equates elements related by R
    (f : CommutativeMonoidHomomorphism M N)
    (let private module N = CommutativeMonoid N)
    (let private module f = CommutativeMonoidHomomorphism f)
    (preserves-R : f.⟦_⟧ Preserves R ⟶ N._≈_)
  = Q.Universal f (equates-≋ f preserves-R)
