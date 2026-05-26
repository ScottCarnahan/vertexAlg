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

/-- The submodule of a tensor product corresponding to a decomposition on the left. -/
def decomposeTensor (N : Type*) [AddCommMonoid N] [Module R N] :
    ι → Submodule R (M ⊗[R] N) :=
  fun i ↦ LinearMap.range ((ℳ i).subtype.rTensor N)

lemma subtype_rTensor_injective (N : Type*) [AddCommMonoid N] [Module R N] (i : ι) :
    Function.Injective ((ℳ i).subtype.rTensor N) :=
  injective_of_comp_eq_id ((ℳ i).subtype.rTensor N) (((component R ι (fun i ↦ ↥(ℳ i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap).rTensor N) (by ext; simp)

/-- The linear isomorphism to the submodule from the tensor product with a summand. -/
noncomputable def decomposeTensorEquiv (N : Type*) [AddCommMonoid N] [Module R N]
    (i : ι) : (ℳ i) ⊗[R] N ≃ₗ[R] decomposeTensor ℳ N i :=
  LinearEquiv.ofInjective ((ℳ i).subtype.rTensor N) (subtype_rTensor_injective ℳ N i)
--#find_home! decomposeTensorEquiv --[Mathlib.LinearAlgebra.TensorProduct.Decomposition]

@[simp]
lemma decomposeTensorEquiv_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : (ℳ i) ⊗[R] N) :
    decomposeTensorEquiv ℳ N i x = ((ℳ i).subtype.rTensor N) x := by rfl

lemma decomposeTensorEquiv_of_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : (ℳ i) ⊗[R] N) :
    (congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a) ((of (fun i ↦ ↥(ℳ i) ⊗[R] N) i) x) =
    (of (fun i ↦ ↥(decomposeTensor ℳ N i)) i) (decomposeTensorEquiv ℳ N i x) := by
  ext; simp [coe_congrLinearEquiv]

lemma component_decompose_subtype (i : ι) :
    component R ι (fun i ↦ ↥(ℳ i)) i ∘ₗ (decomposeLinearEquiv ℳ) ∘ₗ (ℳ i).subtype =
    LinearMap.id := by
  ext; simp
--#find_home! component_decompose_subtype --[Mathlib.Algebra.DirectSum.Decomposition]

lemma decomposeTensorEquiv_symm_apply (N : Type*) [AddCommMonoid N] [Module R N] {i : ι}
    (x : decomposeTensor ℳ N i) :
    (decomposeTensorEquiv ℳ N i).symm x = (((component R ι (fun i ↦ (ℳ i)) i) ∘ₗ
      ((DirectSum.decomposeLinearEquiv ℳ))).rTensor N) (Submodule.subtype _ x) := by
    obtain ⟨x, y, h⟩ := x
    simp only [← h, Submodule.subtype_apply, LinearEquiv.symm_apply_eq, rTensor_comp_apply]
    have : rTensor N (component R ι (fun i ↦ ↥(ℳ i)) i ∘ₗ ↑(decomposeLinearEquiv ℳ)
        ∘ₗ (ℳ i).subtype) = LinearMap.id := by
      simp [component_decompose_subtype]
    have := LinearMap.congr_fun this y
    simp only [id_coe, id_eq, rTensor_comp_apply] at this
    rw [this, ← SetLike.coe_eq_coe, decomposeTensorEquiv_apply]

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

lemma decomposeLinearEquiv_comp_subtype {i : ι} :
    (decomposeLinearEquiv ℳ) ∘ₗ (ℳ i).subtype = lof R ι (fun i ↦ ℳ i) i := by
  ext; simp

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

lemma coe_decomposeTensor (N : Type*) [AddCommGroup N] [Module R N]
    (x : (⨁ (i : ι), decomposeTensor ℳ N i)) :
    (DirectSum.coeAddMonoidHom (decomposeTensor ℳ N)) x =
    ((DirectSum.decomposeLinearEquiv ℳ).symm.rTensor N)
    ((TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N).symm
      ((DirectSum.congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a).symm x)) := by
  rw [rTensor_decomposeLinearEquiv_symm, LinearEquiv.eq_symm_apply]
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    obtain ⟨x, y, h⟩ := x
    simp only [← h, coeAddMonoidHom_of]
    rw [LinearEquiv.eq_symm_apply, LinearEquiv.eq_symm_apply, rTensorLinearEquiv_apply,
      ← rTensor_comp_apply, decomposeLinearEquiv_comp_subtype, ← directSumLeft_symm_of,
      LinearEquiv.apply_symm_apply, decomposeTensorEquiv_of_apply]
    rfl
  | add x y hx hy => simp [hx, hy]

/-- The decomposition on a tensor product given a decomposition of the left module. -/
@[reducible]
noncomputable def tensorDecomposition (N : Type*) [AddCommGroup N] [Module R N] :
    DirectSum.Decomposition (decomposeTensor ℳ N) where
  decompose' x := (DirectSum.congrLinearEquiv fun a ↦ decomposeTensorEquiv ℳ N a)
    (TensorProduct.directSumLeft R R (fun a ↦ ℳ a) N
      ((DirectSum.decomposeLinearEquiv ℳ).rTensor N x))
  left_inv x := by
    simp [coe_decomposeTensor ℳ N _, rTensor_decomposeLinearEquiv_symm]
  right_inv x := by
    simp [coe_decomposeTensor ℳ N _, rTensor_decomposeLinearEquiv_symm]

end Decomposition

end DirectSum
