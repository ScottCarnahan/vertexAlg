/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.PointwiseSMul
public import Mathlib.Data.Finsupp.PointwiseSMul

/-!
Remove this file when the new version of Mathlib hits.
-/

@[expose] public section

noncomputable section

variable {G P R V : Type*}

namespace MonoidAlgebra

@[to_additive]
theorem finite_smulAntidiagonal [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (Set.smulAntidiagonal (SetLike.coe f.support) x.support p).Finite := by
  refine Set.Finite.of_injOn (t := SetLike.coe f.support) (fun _ ⟨h, _⟩ ↦ h) ?_
    f.support.finite_toSet
  intro _ ⟨_, _, hp⟩ gp ⟨_, _, hgp⟩ h
  rw [h, ← hgp] at hp
  exact Prod.ext h (IsLeftCancelSMul.left_cancel gp.1 _ _ hp)

/-- The finset of pairs, whose parts lie in the support of specified functions, that vector-add to
a given element. -/
@[to_additive /-- The finset of pairs, whose parts lie in the support of specified functions, that
scalar-multiply to a given element. -/]
def smulAntidiagonal [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) : Finset (G × P) :=
  (f.finite_smulAntidiagonal x p).toFinset

@[to_additive]
theorem mem_smulAntidiagonal_iff [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [Zero V]
    (f : MonoidAlgebra R G) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ smulAntidiagonal f x p ↔ f gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.1 • gh.2 = p := by
  simp [smulAntidiagonal]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R) smul_eq_addMonoidAlgebra_mul]
theorem smul_eq_MonoidAlgebra_mul [Semiring R] [CancelMonoid G] (a b : MonoidAlgebra R G) :
    a • (b : G → R) = (a * b : MonoidAlgebra R G) := by
  ext g
  classical
  rw [MonoidAlgebra.smul_eq, MonoidAlgebra.mul_apply, Finsupp.sum]
  simp_rw [Finsupp.sum]
  rw [Finset.sum_sigma', Finset.sum_of_injOn]
  · exact fun (x, y) ↦ ⟨x, y⟩
  · simp
  · intro gh h
    rw [Finset.mem_coe, Finset.mem_smulAntidiagonal] at h
    have : b gh.2 ≠ 0 := h.2.1
    simp [h.1, this]
  · intro gh _ h
    simp only [Set.mem_image, Finset.mem_coe, Prod.exists, not_exists, not_and] at h
    contrapose! h
    use gh.fst, gh.snd
    rw [Finset.mem_smulAntidiagonal]
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    exact ⟨⟨(by simp [left_ne_zero_of_mul h.2]), right_ne_zero_of_mul h.2, h.1⟩, rfl⟩
  · intro _ h
    rw [Finset.mem_smulAntidiagonal, smul_eq_mul] at h
    simp [h.2.2]

end MonoidAlgebra
