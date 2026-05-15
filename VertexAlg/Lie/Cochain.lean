/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Cochain

/-!
Add to `Mathlib.Algebra.Lie.Cochain`
-/

@[expose] public section

namespace LieModule.Cohomology

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
[LieRingModule L M] [LieModule R L M]

/-- A Lie 2-coboundary is a 2-cochain that lies in the image of the coboundary map. -/
def twoCoboundary : Submodule R (twoCochain R L M) := LinearMap.range (d₁₂ R L M)

/-- superfluous? -/
def coboundaryMap : oneCochain R L M →ₗ[R] twoCoboundary R L M := (d₁₂ R L M).rangeRestrict

lemma twoCoboundary_le_twoCocycle : (twoCoboundary R L M) ≤ (twoCocycle R L M) := by
  intro _ h
  obtain ⟨b, hb⟩ := h
  have := d₂₃_comp_d₁₂ R L M
  rw [LinearMap.ext_iff] at this
  simpa [mem_twoCocycle_iff, ← hb] using this b

/-- Degree 2 cohomology `H²(L,M)` is the quotient of 2-cocycles by 2-coboundaries. -/
def twoCohomology := (twoCocycle R L M) ⧸ (twoCoboundary R L M).submoduleOf (twoCocycle R L M)

/-- Degree 2 cohomology `H²(L,M)` is an additive commutative group. -/
instance : AddCommGroup (twoCohomology R L M) :=
  Submodule.Quotient.addCommGroup _

/-- Degree 2 cohomology `H²(L,M)` is a module over the scalar ring `R`. -/
instance : Module R (twoCohomology R L M) :=
  Submodule.Quotient.module' _

end LieModule.Cohomology
