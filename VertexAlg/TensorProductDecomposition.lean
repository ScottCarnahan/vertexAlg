/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-!
Add to `Mathlib.LinearAlgebra.TensorProduct.Decomposition`
-/

@[expose] public section

open TensorProduct LinearMap
namespace DirectSum
variable {ι R M S : Type*} [DecidableEq ι]
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)
  [CommSemiring S] [Algebra R S]
section Decomposition
variable [Decomposition ℳ]

lemma component_decompose_subtype (i : ι) :
    component R ι (fun i ↦ ↥(ℳ i)) i ∘ₗ (decomposeLinearEquiv ℳ) ∘ₗ (ℳ i).subtype =
    LinearMap.id := by
  ext; simp
--#find_home! component_decompose_subtype --[Mathlib.Algebra.DirectSum.Decomposition]

@[simp]
lemma rTensor_subtype_decomposeTensorEquiv_symm (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : decomposeTensor ℳ N i) :
    (rTensor N (ℳ i).subtype) ((decomposeTensorEquiv ℳ N i).symm x) = x := by
  set y := (decomposeTensorEquiv ℳ N i).symm x with hy
  have : x = (decomposeTensorEquiv ℳ N i) y := by simp [hy]
  simp [this]

lemma decomposeTensorEquiv_symm_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : decomposeTensor ℳ N i) :
    (decomposeTensorEquiv ℳ N i).symm x = (((component R ι (fun i ↦ (ℳ i)) i) ∘ₗ
      ((DirectSum.decomposeLinearEquiv ℳ))).rTensor N) (Submodule.subtype _ x) := by
    obtain ⟨x, h⟩ := x
    have : rTensor N (component R ι (fun i ↦ ↥(ℳ i)) i ∘ₗ ↑(decomposeLinearEquiv ℳ)
        ∘ₗ (ℳ i).subtype) = LinearMap.id := by
      simp [component_decompose_subtype]
    have := LinearMap.congr_fun this ((decomposeTensorEquiv ℳ N i).symm ⟨x, h⟩)
    simp only [rTensor_comp_apply, id_coe, id_eq] at this
    rw [← this, rTensor_comp]
    simp only [Submodule.subtype_apply, coe_comp, Function.comp_apply]
    congr
    exact rTensor_subtype_decomposeTensorEquiv_symm ℳ N ⟨x, h⟩

omit [Decomposition ℳ] in
lemma directSumLeft_symm_of (N : Type*) [AddCommMonoid N] [Module R N] {i : ι} (x : (ℳ i) ⊗[R] N) :
    (directSumLeft R R (fun a ↦ ↥(ℳ a)) N).symm ((of (fun i ↦ (ℳ i) ⊗[R] N) i) x) =
      rTensor N (lof R ι (fun i ↦ ℳ i) i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [rTensor_tmul]
    refine (LinearEquiv.symm_apply_eq (directSumLeft R R (fun a ↦ ↥(ℳ a)) N)).mpr ?_
    rw [directSumLeft_tmul_lof, lof_eq_of]
  | add x y h₁ h₂ => simp [h₁, h₂]
--#find_home! directSumLeft_symm_of --[Mathlib.LinearAlgebra.DirectSum.TensorProduct]

/-
lemma rTensor_component (N : Type*) [AddCommMonoid N] [Module R N] {i : ι} :
    ((component R ι (fun i ↦ (ℳ i)) i).rTensor N) (of (fun i ↦ (ℳ i)) i) = sorry := by
  sorry
-/
lemma rTensor_decomposeLinearEquiv_symm (N : Type*) [AddCommMonoid N] [Module R N] :
    LinearEquiv.rTensor N (decomposeLinearEquiv ℳ).symm =
      (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ)).symm := rfl

-- This needs to be a general theorem about equivalences.
lemma rTensorLinearEquiv_apply (N : Type*) [AddCommMonoid N] [Module R N] (x : M ⊗[R] N) :
    (LinearEquiv.rTensor N (decomposeLinearEquiv ℳ)) x =
      rTensor N (decomposeLinearEquiv ℳ).toLinearMap x :=
  DFunLike.congr_fun rfl x

lemma congrLinearEquiv_coeAddMonoidHom (N : Type*) [AddCommGroup N] [Module R N]
    (x : ⨁ (i : ι), ↥(ℳ i) ⊗[R] N) :
    (DirectSum.coeAddMonoidHom (decomposeTensor ℳ N))
      ((DirectSum.congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a) x) =
    ((DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N)
      ((TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N).symm x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← LinearEquiv.symm_apply_eq, ← LinearEquiv.symm_apply_eq, LinearEquiv.symm_symm,
      decomposeTensorEquiv_of_apply, coeAddMonoidHom_of, rTensor_decomposeLinearEquiv_symm,
      LinearEquiv.symm_symm, decomposeTensorEquiv_apply]
    refine (LinearEquiv.eq_symm_apply (directSumLeft R R (fun a ↦ ↥(ℳ a)) N)).mp ?_
    rw [directSumLeft_symm_of, rTensorLinearEquiv_apply, ← rTensor_comp_apply,
      decomposeLinearEquiv_comp_subtype]
  | add x y hx hy => simp [hx, hy]

end Decomposition

end DirectSum
