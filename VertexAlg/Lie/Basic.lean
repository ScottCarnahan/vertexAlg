/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
Add to `Mathlib.Algebra.Lie.Basic`
-/

@[expose] public section

variable {R L₁ L₂ : Type*} [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂]
  [LieAlgebra R L₂]

instance : LinearEquivClass (L₁ ≃ₗ⁅R⁆ L₂) R L₁ L₂ where
  map_add f a b := by
    rw [show f (a + b) = f.toLieHom (a + b) by rfl, show f a = f.toLieHom a by rfl,
      show f b = f.toLieHom b by rfl, map_add]
  map_smulₛₗ f r a := by
    rw [show f (r • a) = f.toLieHom (r • a) by rfl, show f a = f.toLieHom a by rfl,
      map_smul, RingHom.id_apply]
