/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
Remove when merged
-/

@[expose] public section

namespace DirectSum

section

variable {ι : Type*} {β : ι → Type*} [∀ i, AddCommGroup (β i)]

--Add to `Mathlib.Algebra.DirectSum.Basic`
@[simp]
theorem neg_apply (g : ⨁ i, β i) (i : ι) : (- g) i = - (g i) :=
  rfl
end

section
variable {ι : Type*} (R : Type*) [Semiring R] (β : ι → Type*) [∀ i, AddCommMonoid (β i)]
    [∀ i, Module R (β i)]

/-- add to `Mathlib.Algebra.DirectSum.Module` -/
def part [DecidableEq ι] (i : ι) : Submodule R (⨁ i, β i) :=
  (lof R ι (fun i ↦ β i) i).range

lemma mem_part_exist_of [DecidableEq ι] (i : ι) (x : part R β i) :
    ∃ y : β i, of β i y = x := by
  obtain ⟨x, hx⟩ := x
  dsimp only [part] at hx
  obtain ⟨y, hy⟩ := hx
  use y
  simp_rw [← hy, lof_eq_of]

end

section

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A] (F : ι → Submodule R A)

lemma DFinsupp.lsum_subtype_coe [DecidableEq ι] [AddMonoid ι] (x : Π₀ i, F i)
    [(i : ι) → (x : ↥(F i)) → Decidable (x ≠ 0)] (p : ι → Prop) [DecidablePred p] :
    ((DFinsupp.lsum R) fun i ↦ (F i).subtype) (DFinsupp.filter (fun i ↦ p i) x) =
      x.sum fun i r ↦ if p i then r else 0 := by
  simp only [DFinsupp.filter_def, SetLike.coe_sort_coe, DFinsupp.lsum_apply_apply,
    DFinsupp.sumAddHom_apply, DFinsupp.sum, DFinsupp.mk_apply, Finset.mem_filter,
    DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, LinearMap.toAddMonoidHom_coe,
    Submodule.subtype_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr (by grind) (by grind)

end

end DirectSum
