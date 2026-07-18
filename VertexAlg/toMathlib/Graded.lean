/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Graded


/-!
Redo GradedBracket

-/

@[expose] public section

open Finset
open DirectSum

variable {R L M ι κ σ τ : Type*}

section

section heterogenousGradedBracket

/-- A `heterogeneous graded bracket` class that ensures a bracket action preserves a vector-additive
grading. -/
class SetLike.GradedBracket' [SetLike σ L] [SetLike τ M] [Bracket L M] [VAdd ι κ]
    (ℒ : ι → σ) (ℳ : κ → τ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : ∀ ⦃i j⦄ {gi hj}, gi ∈ ℒ i → hj ∈ ℳ j → ⁅gi, hj⁆ ∈ ℳ (i +ᵥ j)

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] (ℳ : κ → Submodule R M)

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
class GradedLieAlgebra' extends SetLike.GradedBracket' ℒ ℒ, DirectSum.Decomposition ℒ

/-- A class that ensures a Lie algebra has a bracket that preserves a decomposition. -/
class GradedLieModule [GradedLieAlgebra' ℒ] [DirectSum.Decomposition ℳ] extends
    SetLike.GradedBracket' ℒ ℳ

end heterogenousGradedBracket

namespace DirectSum

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra' ℒ]

/- This material, up to the next variable declaration, is just to fill in API until
`GradedLieAlgebra` is replaced. -/

instance : LieRing (⨁ i, ℒ i) where
  bracket x y := decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma bracket_apply_apply' (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply'

@[simp]
lemma decompose_bracket' (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆ := by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]
lemma decompose_symm_bracket' (x y : ⨁ i, ℒ i) :
    (decompose ℒ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℒ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

instance : LieAlgebra R (⨁ i, ℒ i) where
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

/-- If `L` is graded by `ι` with degree `i` component `ℒ i`, then it is isomorphic as
a Lie algebra to a direct sum of components. -/
def decomposeLieEquiv' : L ≃ₗ⁅R⁆ ⨁ i, ℒ i :=
  { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

/- End of filler material. -/

variable [DecidableEq κ] [VAdd ι κ] [AddCommGroup M] [Module R M] [LieRingModule L M]
  [LieModule R L M] (ℳ : κ → Submodule R M) [DirectSum.Decomposition ℳ] [GradedLieModule ℒ ℳ]

instance : LieRingModule (⨁ i, ℒ i) (⨁ k, ℳ k) where
  bracket x y := decomposeLinearEquiv ℳ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℳ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  leibniz_lie _ _ _ := by simp

omit [VAdd ι κ] [LieModule R L M] [GradedLieModule ℒ ℳ] in
lemma hbracket_apply_apply (x : ⨁ i, ℒ i) (y : ⨁ k, ℳ k) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℳ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℳ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply

omit [VAdd ι κ] [LieModule R L M] [GradedLieModule ℒ ℳ] in
lemma decompose_hbracket (x : L) (y : M) :
    decompose ℳ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℳ y⁆ := by
  simp only [← decomposeLinearEquiv_apply, hbracket_apply_apply]
  simp

omit [VAdd ι κ] [LieModule R L M] [GradedLieModule ℒ ℳ] in
@[simp]
lemma decompose_symm_hbracket (x : ⨁ i, ℒ i) (y : ⨁ k, ℳ k) :
    (decompose ℳ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℳ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply, hbracket_apply_apply]
  simp

instance : LieModule R (⨁ i, ℒ i) (⨁ k, ℳ k) where
  smul_lie _ _ _ := by simp [⁅·,·⁆]
  lie_smul _ _ _ := by simp [⁅·,·⁆]

end DirectSum
