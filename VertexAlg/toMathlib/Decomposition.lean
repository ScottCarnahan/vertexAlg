/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
Add to `Mathlib.Algebra.DirectSum.Decomposition`
-/

@[expose] public section

namespace DirectSum.Decomposition

variable {ι σ R L M : Type*}

section

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ) [Decomposition ℳ]

lemma zero_of_mem_ne {i j : ι} (hij : i ≠ j) {x : M} (hi : x ∈ ℳ i) (hj : x ∈ ℳ j) :
    x = 0 := by
  classical
  have : DFinsupp.support (decomposeAddEquiv ℳ x) ⊆ {i} := by
    rw [decomposeAddEquiv_apply, decompose_of_mem ℳ hi]
    exact DirectSum.support_of_subset
  have : DFinsupp.support (decomposeAddEquiv ℳ x) ⊆ {j} := by
    rw [decomposeAddEquiv_apply, decompose_of_mem ℳ hj]
    exact DirectSum.support_of_subset
  exact (AddEquiv.map_eq_zero_iff (decomposeAddEquiv ℳ)).mp
    (DFinsupp.support_eq_empty.mp (by grind))

end

section

variable [CommSemiring R]

section

variable [AddCommMonoid L] [Module R L] [AddCommMonoid M] [Module R M] (ℳ : ι → Submodule R M)

lemma disjoint_of_ne [DecidableEq ι] [Decomposition ℳ] {i j : ι} (hij : i ≠ j) :
    Disjoint (ℳ i) (ℳ j) :=
  Submodule.disjoint_def.mpr fun _ hi hj ↦ zero_of_mem_ne ℳ hij hi hj

end

section

variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)

variable [Zero ι] (p : L →ₗ[R] M)

/-- The decomposition induced by a section of a surjection, where the kernel is placed in degree
zero. -/
def decompositionOfSection (s : M →ₗ[R] L) (i : ι) [Decidable (i = 0)] :
    Submodule R L :=
  if i = 0 then (s.domRestrict (ℳ 0)).range ⊔ p.ker else (s.domRestrict (ℳ i)).range

lemma sub_mem_decompositionOfSection [DecidableEq ι] {s : M →ₗ[R] L}
    (hs : Function.LeftInverse p s) {i : ι} (hi : i = 0) {x : L} :
    x - s (p x) ∈ decompositionOfSection ℳ p s i := by
  simp only [decompositionOfSection, hi]
  exact Submodule.mem_sup_right (by simp [hs.eq])

lemma section_component_mem_decompositionOfSection [DecidableEq ι] [Decomposition ℳ]
    (i : ι) {s : M →ₗ[R] L} (x : L) :
    s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))) ∈
      decompositionOfSection ℳ p s i := by
  by_cases h : i = 0
  · simp only [decompositionOfSection, h, ↓reduceIte, LinearMap.range_domRestrict]
    refine Submodule.mem_sup_left ?_
    rw [h]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℳ i) 0) (decompose ℳ (p x)))
  · simp only [decompositionOfSection, h, ↓reduceIte, LinearMap.range_domRestrict]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℳ i) i) (decompose ℳ (p x)))

/-- The map to the decomposition induced by a section of a surjection. -/
def toDecompositionOfSection {p : L →ₗ[R] M} [DecidableEq ι] [Decomposition ℳ] (i : ι)
    {s : M →ₗ[R] L} (hs : Function.LeftInverse p s) :
    L →ₗ[R] decompositionOfSection ℳ p s i where
  toFun x := if hi : i = 0 then ⟨x - s (p x), sub_mem_decompositionOfSection ℳ p hs hi⟩ +
    ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
      section_component_mem_decompositionOfSection ℳ p i x⟩
  else ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
    section_component_mem_decompositionOfSection ℳ p i x⟩
  map_add' _ _ := by
    by_cases hi : i = 0
    · simp [hi]
      abel
    · simp [hi]
  map_smul' _ _ := by
    by_cases hi : i = 0
    · simp [hi, smul_sub]
    · simp [hi]

@[simp]
lemma toDecompositionOfSection_apply_zero [DecidableEq ι] [Decomposition ℳ]
    {s : M →ₗ[R] L} (hs : Function.LeftInverse p s) (x : L) :
    toDecompositionOfSection ℳ 0 hs x =
    (⟨x - s (p x), sub_mem_decompositionOfSection ℳ p hs rfl⟩ : decompositionOfSection ℳ p s 0) +
    (⟨s (component R ι (fun i ↦ ℳ i) 0 (decompose ℳ (p x))),
      section_component_mem_decompositionOfSection ℳ p 0 x⟩ :
        decompositionOfSection ℳ p s 0) := by
  simp [toDecompositionOfSection]

@[simp]
lemma toDecompositionOfSection_apply_of_ne [DecidableEq ι] [Decomposition ℳ] {i : ι}
    (hi : i ≠ 0) {s : M →ₗ[R] L} (hs : Function.LeftInverse p s) (x : L) :
    toDecompositionOfSection ℳ i hs x =
    ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
      section_component_mem_decompositionOfSection ℳ p i x⟩ := by
  simp [hi, toDecompositionOfSection]

lemma mk_toDecompositionOfSection_apply [DecidableEq ι] [Decomposition ℳ]
    [(i : ι) → (x : (ℳ i)) → Decidable (x ≠ 0)] {s : M →ₗ[R] L} (hs : Function.LeftInverse p s)
    (x : L) :
    DirectSum.mk (fun i ↦ (decompositionOfSection ℳ p s i)) ((decompose ℳ (p x)).support ⊔ {0})
        (fun i ↦ (toDecompositionOfSection ℳ i hs x)) = ∑ i ∈ ((decompose ℳ (p x)).support ⊔ {0}),
          ((of _ i) (toDecompositionOfSection ℳ i hs x)) := by
  ext i
  simp only [Finset.sup_eq_union', SetLike.coe_sort_coe, Finset.union_singleton, sum_apply,
    AddSubmonoidClass.coe_finsetSum]
  simp only [DirectSum.mk, SetLike.coe_sort_coe, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    DFinsupp.mk_apply, Finset.union_singleton, Finset.mem_insert, DFinsupp.mem_support_toFun, ne_eq]
  rw [Finset.sum_eq_single i]
  · by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, false_or, ne_eq, not_false_eq_true, toDecompositionOfSection_apply_of_ne,
      dite_eq_ite, Classical.ite_not, of_eq_same]
      by_cases h : ((decompose ℳ) (p x)) i = 0
      · simp [h, ← apply_eq_component]
      · simp [h]
  · intro j hj hji
    simp only [ZeroMemClass.coe_eq_zero]
    rw [of_eq_of_ne j i _ hji.symm]
  · intro hi
    have hi0 : i ≠ 0 := by
      contrapose! hi
      exact Finset.mem_insert.mpr <| Or.inl hi
    have his : i ∉ DFinsupp.support ((decompose ℳ) (p x)) := by
      contrapose! hi
      exact Finset.mem_insert_of_mem hi
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at his
    simp [toDecompositionOfSection, hi0, ← apply_eq_component, his]
/-
noncomputable instance [DecidableEq ι] [Decomposition ℳ] {s : M →ₗ[R] L}
    (hs : Function.LeftInverse p s) :
    Decomposition (fun i ↦ decompositionOfSection ℳ p s i) := by
  refine ofLinearMap (fun i ↦ decompositionOfSection ℳ p s i) ?_ ?_ ?_
  · letI _ (i : ι) (x : ℳ i) := Classical.propDecidable (x ≠ 0)
    exact {
      toFun x := DirectSum.mk (fun i ↦ (decompositionOfSection ℳ p s i))
        ((decompose ℳ (p x)).support ⊔ {0}) (fun i ↦ (toDecompositionOfSection ℳ i hs x))
      map_add' x y := by
        ext i
        by_cases hi : i = 0
        · simp [hi]
        · by_cases hx : ((decompose ℳ) (p x)) i = 0
          · by_cases hy : ((decompose ℳ) (p y)) i = 0
            · simp [hi, hx, hy]
            · simp [hi, hx, hy, ← apply_eq_component]
          · by_cases hy : ((decompose ℳ) (p y)) i = 0
            · simp [hi, hx, hy, ← apply_eq_component]
            · by_cases h : ((decompose ℳ) (p x) i) + ((decompose ℳ) (p y) i) = 0
              · simp [h, hi, hx, hy, ← apply_eq_component, ← map_add, ← Submodule.coe_add]
              · simp [h, hi, hx, hy]
      map_smul' r x := by
        ext i
        simp only [Finset.sup_eq_union', SetLike.coe_sort_coe, map_smul, DFinsupp.mk_apply,
          decompose_smul, Finset.union_singleton, Finset.mem_insert, DFinsupp.mem_support_toFun,
          ne_eq, RingHom.id_apply, SetLike.coe_eq_coe]
        by_cases hi : i = 0
        · simp [hi, smul_apply]
        · by_cases hx : ((decompose ℳ) (p x)) i = 0
          · simp [hi, hx, smul_apply]
          · by_cases hr : (r • (decompose ℳ) (p x)) i = 0
            · simp only [hi, hr, not_true_eq_false, or_self, ↓reduceDIte]
              simp only [smul_apply, DFinsupp.mk_apply, Finset.union_singleton, Finset.mem_insert,
                hi, DFinsupp.mem_support_toFun, ne_eq, hx, not_false_eq_true, or_true, ↓reduceDIte,
                toDecompositionOfSection_apply_of_ne, SetLike.mk_smul_mk]
              simp_rw [← map_smul, ← apply_eq_component, ← Submodule.coe_smul_of_tower,
                ← smul_apply]
              simp [hr, ZeroMemClass.zero_def]
            · simp only [hi, smul_apply, false_or, ne_eq, not_false_eq_true,
              toDecompositionOfSection_apply_of_ne, SetLike.mk_smul_mk, dite_eq_ite,
              Classical.ite_not, DFinsupp.mk_apply, Finset.union_singleton, Finset.mem_insert,
              DFinsupp.mem_support_toFun, hx, or_true, ↓reduceDIte, ite_eq_right_iff]
              simp_rw [← map_smul, ← apply_eq_component, ← Submodule.coe_smul_of_tower,
                ← smul_apply]
              simp [hr] }
  · ext x
    simp only [Finset.sup_eq_union', SetLike.coe_sort_coe, LinearMap.coe_comp, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [mk_toDecompositionOfSection_apply]

    sorry
  · ext1 i
    simp only [Finset.sup_eq_union', SetLike.coe_sort_coe, LinearMap.id_comp]
    ext1 x
    obtain ⟨x, hx⟩ := x
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      coeLinearMap_lof]



    sorry
-/
end

end

end DirectSum.Decomposition
