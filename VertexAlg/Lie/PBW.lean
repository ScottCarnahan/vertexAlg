/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

module

public import Mathlib.Algebra.Lie.Loop
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.FilteredAlgebra.Basic

/-!
## Attempt at PBW
Following Bourbaki, `Lie groups and Lie algebras` Chapter 1 section 2.7

For M a monotonic tuple (λ₁,…,λₙ), define z_M = z_λ₁ ⋯ z_λₙ and
x_M = x_λ₁ ⊗ ⋯ ⊗ x_λₙ
say deg z_M ≤ p
1. f_p (z_λ, x_M) = x_λ x_M if λ ≤ M -- so adding the least element is a product.
2. f_p (z_λ, x_M) - x_λ x_M ∈ P_q if z_M ∈ P_q, q ≤ p
3. f_p (z_λ, f_p(z_μ, x_N)) = f_p (z_μ, f_p(z_λ, x_N)) + f_p(⁅z_λ,z_μ⁆, x_N)

Unfold to:
If p = 0 then z_M = 1 and x_M = 1, so f_p(z_λ, x_M) = x_λ.
Write M = (λ₁,M') for M' = (λ₂,…,λₙ)
f_p (z_λ, f_p(z_λ₁, x_M')) =
  f_p (z_λ₁,f_p(z_λ,x_M')) + f_p(⁅z_λ,z_λ₁⁆,x_M'))
but f_p(z_λ₁, x_M') = x_M.

If λ ≤ λ₁, then f_p(z_λ,x_M) = x_λ x_M
otherwise, f_p(z_λ,x_M) = x_λ₁ f_{p-1}(z_λ,x_M') + f_{p-1}(⁅z_λ,z_λ₁⁆,x_M')
* Expand ⁅z_λ,z_λ₁⁆ = ∑ i ∈ (f λ λ₁).support, (f λ λ₁ i) • f_{p-1}(z_i, x_M')
where f : ι → ι → (ι →₀ R)

* `UniversalEnvelopingAlgebra.mkAlgHom` : the quotient map from tensor algebra
* `SymmetricAlgebra.algHom` : The quotient map from tensor algebra

Lemma B: linear representation `ρ : L → gl(Sym(L))` satisfying the two properties:
1. ρ(x_λ)z_Σ = z_λz_Σ for λ ≤ Σ
2. ρ(x_λ)z_Σ ≅ z_λz_Σ (mod S_m) when Σ has length m

Lemma C: If `t ∈ T_m ∩ (UniversalEnvelopingAlgebra.mkAlgHom).ker` then the homogeneous component
of degree m lies in `(SymmetricAlgebra.algHom).ker`.

Final argument: For `t ∈ T_m`, if `UniversalEnvelopingAlgebra.mkAlgHom t ∈ U_{m-1}`, then
there exists `t' ∈ T_{m-1}`  such that `t - t' ∈ (UniversalEnvelopingAlgebra.mkAlgHom).ker`. Then by
Lemma C, since the homogeneous component is `t`, `t` lies in `(SymmetricAlgebra.algHom).ker`.

-/

@[expose] public section

variable {ι σ A B R L M : Type*}

section filtration

variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [IsOrderedAddMonoid ι] [CommSemiring R]
  [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

open DirectSum

lemma isRingFiltration_of_graded :
    IsRingFiltration (fun i ↦ ⨆ j ≤ i, 𝒜 j) (fun i ↦ ⨆ j < i, 𝒜 j) where
  mono _ j h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i ≤ j := hi.trans h
    tauto
  is_le {_ j} h := by
    simp only [iSup_le_iff]
    intro i hi
    refine le_iSup_of_le i ?_
    rw [le_iSup_iff]
    have : i < j := lt_of_le_of_lt hi h
    tauto
  is_sup _ _ h := by
    simp only [iSup_le_iff]
    intro i hi
    simp only [iSup_le_iff] at h
    exact h i hi i (Std.IsPreorder.le_refl i)
  one_mem := mem_of_le_of_mem (S := 𝒜 0)
    (le_iSup_iff.mpr fun _ h ↦ (by simpa using h 0)) (SetLike.one_mem_graded 𝒜)
  mul_mem {i j} gi gj hi hj := by
    classical
    obtain ⟨fgi, hgi⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp (fun k ↦ k ≤ i) 𝒜 gi).mp hi
    obtain ⟨fgj, hgj⟩ := (Submodule.mem_biSup_iff_exists_dfinsupp (fun k ↦ k ≤ j) 𝒜 gj).mp hj
    rw [← hgi, ← hgj]
    simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
      DFinsupp.support_filter, DFinsupp.filter_apply, LinearMap.toAddMonoidHom_coe,
      Submodule.subtype_apply, Finset.sum_mul_sum]
    refine sum_mem fun k hk ↦ sum_mem fun l hl ↦ ?_
    have hki : k ≤ i := by grind
    have hlj : l ≤ j := by grind
    simp only [hki, ↓reduceIte, hlj]
    refine Set.mem_of_subset_of_mem (le_sSup (α := Submodule R A) ?_) <|
      SetLike.mul_mem_graded (Submodule.coe_mem (fgi k)) (Submodule.coe_mem (fgj l))
    use k + l
    simp [add_le_add hki hlj]

end filtration

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open DFinsupp

variable [DecidableEq ι]

theorem biSup_eq_range_dfinsupp_lsum' (R' : Type*) [Semiring R'] [Module R' N]
    [SMulCommClass R R' N] (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range (LinearMap.comp
        (DFinsupp.lsum R' (fun i => (S i).subtype))
          (DFinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply, filterLinearMap_apply, filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]

theorem mem_biSup_iff_exists_dfinsupp' (R' : Type*) [Semiring R'] [Module R' N]
    [SMulCommClass R R' N] (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i,
        DFinsupp.lsum R' (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum' R' p S) x


end Submodule

section

variable {ι A σ : Type*} [Preorder ι] [CompleteLattice σ] [SetLike σ A]
  (F : ι → σ) (F_lt : outParam <| ι → σ) [IsFiltration F F_lt]

lemma IsFiltration.f_lt_eq_sup (i : ι) :
    F_lt i = ⨆ j < i, F j :=
  le_antisymm_iff.mpr ⟨IsFiltration.is_sup (⨆ j < i, F j) i fun _ h ↦ le_biSup F h,
    iSup₂_le fun _ h ↦ IsFiltration.is_le h⟩

end

open DirectSum

variable [CommRing R] [Ring A] [Algebra R A] (F : ι → Submodule R A) (F_lt : ι → Submodule R A)

abbrev gradedPart (i : ι) := (F i) ⧸ (F_lt i).submoduleOf (F i)

--def quotmap (i : ι) : F i → gradedPart F i := Submodule.Quotient.mk
--instance (i : ι) : AddCommGroup (gradedPart F F_lt i) := inferInstance

abbrev associatedGraded := ⨁ i, gradedPart F F_lt i

namespace AssociatedGraded

/-- Cast between "equal" graded parts. -/
def cast {i j} (h : i = j) : gradedPart F F_lt i ≃ₗ[R] gradedPart F F_lt j := LinearEquiv.cast h

theorem cast_mk {i j} (h : i = j) (a : F i) :
    cast F F_lt h (Submodule.Quotient.mk a) =
    (Submodule.Quotient.mk (LinearEquiv.cast (M := fun k ↦ F k) (R := R) h a)) := by
  subst h
  rfl

@[simp]
theorem cast_refl {i} (h : i = i) : cast F F_lt h = LinearEquiv.refl _ _ :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
theorem cast_symm {i j} (h : i = j) : (cast F F_lt h).symm = cast F F_lt h.symm :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast F F_lt h).trans (cast F F_lt h') = cast F F_lt (h.trans h') := by
  subst h h'
  simp

@[simp]
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : gradedPart F F_lt i) :
    cast F F_lt h' (cast F F_lt h a) = cast F F_lt (h.trans h') a := by
  subst h h'
  simp

@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun i => gradedPart F F_lt i}
    (h : a.fst = b.fst) (h2 : cast F F_lt h a.snd = b.snd) :
    a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at h h2
  subst h
  simp only [cast_refl, LinearEquiv.refl_apply] at h2
  rw [h2]

theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast F F_lt h) = _root_.cast (congrArg (fun i => gradedPart F F_lt i) h) := by
  subst h
  rw [cast_refl]
  rfl

-- see LinearAlgebra/TensorPower/Basic.lean for use of casts.

variable [PartialOrder ι]

lemma DFinsupp.lsum_subtype_coe [DecidableEq ι] [AddMonoid ι] [IsRingFiltration F F_lt]
    (x : Π₀ i, F i) [(i : ι) → (x : ↥(F i)) → Decidable (x ≠ 0)] (p : ι → Prop) [DecidablePred p] :
    ((DFinsupp.lsum R) fun i ↦ (F i).subtype) (DFinsupp.filter (fun i ↦ p i) x) =
      x.sum fun i r ↦ if p i then r else 0 := by
  simp only [DFinsupp.filter_def, SetLike.coe_sort_coe, DFinsupp.lsum_apply_apply,
    DFinsupp.sumAddHom_apply, DFinsupp.sum, DFinsupp.mk_apply, Finset.mem_filter,
    DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, LinearMap.toAddMonoidHom_coe,
    Submodule.subtype_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr (by grind) (by grind)
--#find_home! dfinsupp_lsum_coe -- here

omit [PartialOrder ι] in
lemma dfinsupp_mul [DecidableEq ι] (x : Π₀ i, F i) {y : A}
    [(i : ι) → (x : ↥(F i)) → Decidable (x ≠ 0)] :
    (x.sum fun _ r ↦ (r : A)) * y = x.sum fun _ r ↦ r * y := by
  simp only [DFinsupp.sum]
  rw [Finset.sum_mul]
--#find_home! dfinsupp_mul --[Mathlib.LinearAlgebra.DFinsupp]

lemma mul_mem_f_lt [AddCommMonoid ι] [AddRightStrictMono ι]
    [IsRingFiltration F F_lt] (i j : ι) {x y : A} (hx : x ∈ F_lt i) (hy : y ∈ F j) :
    x * y ∈ F_lt (i + j) := by
  classical
  rw [IsFiltration.f_lt_eq_sup F F_lt i, Submodule.mem_biSup_iff_exists_dfinsupp' R] at hx
  obtain ⟨f, hf⟩ := hx
  rw [← hf, DFinsupp.lsum_subtype_coe, DFinsupp.sum, Finset.sum_mul]
  refine Submodule.sum_mem (F_lt (i + j)) ?_
  intro k _
  by_cases hk : k < i
  · simp only [hk, ↓reduceIte]
    suffices F (k + j) ≤ F_lt (i + j) by
      exact (Submodule.mem_toAddSubgroup (F_lt (i + j))).mp
        (this (SetLike.mul_mem_graded (Submodule.coe_mem (f k)) hy))
    exact IsFiltration.is_le <| add_lt_add_left hk j
  · simp [hk]

lemma mul_mem_f_lt' [AddCommMonoid ι] [AddLeftStrictMono ι]
    [IsRingFiltration F F_lt] (i j : ι) {x y : A} (hx : x ∈ F i) (hy : y ∈ F_lt j) :
    x * y ∈ F_lt (i + j) := by
  classical
  rw [IsFiltration.f_lt_eq_sup F F_lt j, Submodule.mem_biSup_iff_exists_dfinsupp' R] at hy
  obtain ⟨f, hf⟩ := hy
  rw [← hf, DFinsupp.lsum_subtype_coe, DFinsupp.sum, Finset.mul_sum]
  refine Submodule.sum_mem (F_lt (i + j)) ?_
  intro k _
  by_cases hk : k < j
  · simp only [hk, ↓reduceIte]
    suffices F (i + k) ≤ F_lt (i + j) by
      exact (Submodule.mem_toAddSubgroup (F_lt (i + j))).mp
        (this (SetLike.mul_mem_graded hx (Submodule.coe_mem (f k))))
    refine IsFiltration.is_le <| add_lt_add_right hk i
  · simp [hk]


variable [AddCommMonoid ι] [IsOrderedCancelAddMonoid ι] [IsRingFiltration F F_lt]

def filteredMul (i j : ι) : F i →ₗ[R] F j →ₗ[R] F (i + j) where
  toFun x := {
    toFun y := ⟨x.val * y.val, SetLike.mul_mem_graded x.2 y.2⟩
    map_add' _ _ := by simp [mul_add]
    map_smul' _ _ := by simp }
  map_add' _ _ := by ext; simp [add_mul]
  map_smul' _ _ := by ext; simp

lemma mem_lt_of_mul_left (i j : ι) {x y : A} (hx : x ∈ F i) (hxlt : x ∈ F_lt i)
    (hy : y ∈ F j) :
    (filteredMul F F_lt i j ⟨x, hx⟩ ⟨y, hy⟩).val ∈ F_lt (i + j) := by
  simp only [filteredMul, LinearMap.coe_mk, AddHom.coe_mk]
  exact mul_mem_f_lt F F_lt _ _ hxlt hy

noncomputable def mulQuotient (i j : ι) :
    F i →ₗ[R] F j →ₗ[R] gradedPart F F_lt (i + j) :=
  (filteredMul F F_lt i j).compr₂ (Submodule.mkQ _)

omit [IsOrderedCancelAddMonoid ι] in
lemma mulQuotient_eq {i j} (x : F i) (y : F j) :
    mulQuotient F F_lt i j x y = Submodule.Quotient.mk (filteredMul F F_lt i j x y) := by
  simp [mulQuotient]

lemma submodule_le_mulQuotient (i j : ι) :
    (F_lt i).submoduleOf (F i) ≤ (mulQuotient F F_lt i j).ker := by
  intro x hx
  ext y
  simp only [mulQuotient, filteredMul, LinearMap.compr₂_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact mul_mem_f_lt F F_lt i j hx y.2

lemma submodule_le_flip_mulQuotient (i j : ι) :
    (F_lt j).submoduleOf (F j) ≤ (mulQuotient F F_lt i j).flip.ker := by
  intro x hx
  ext y
  simp only [mulQuotient, filteredMul, LinearMap.flip_apply, LinearMap.compr₂_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.mkQ_apply, LinearMap.zero_apply,
    Submodule.Quotient.mk_eq_zero]
  exact mul_mem_f_lt' F F_lt i j y.2 hx

@[simps]
noncomputable instance : GradedMonoid.GMul (gradedPart F F_lt) where
  mul {i j} x y := (mulQuotient F F_lt i j).liftQ₂ _ _ (submodule_le_mulQuotient F F_lt i j)
    (submodule_le_flip_mulQuotient F F_lt i j) x y

@[simps]
noncomputable instance : GradedMonoid.GOne (gradedPart F F_lt) where
  one := Submodule.Quotient.mk (1 : F 0)

/-
theorem mk_mul_mk {i j} (a b : A) (ha : a ∈ F i) (hb : b ∈ F j) :
    GradedMonoid.GMul.mul ((Submodule.mkQ _ ⟨a, ha⟩) : gradedPart F F_lt i)
      ((Submodule.mkQ _ ⟨b, hb⟩) : gradedPart F F_lt j) =
    Submodule.Quotient.mk (filteredMul F F_lt i j a b) := by
  sorry

theorem one_mul {n} (a : gradedPart F F_lt n) :
    cast F F_lt (zero_add n) (GradedMonoid.GOne.one (A := gradedPart F F_lt) a) = a := by


noncomputable instance : GradedMonoid.GMonoid (gradedPart F F_lt) where
  one_mul x := by
    obtain ⟨k, x⟩ := x
    induction x using Quotient.inductionOn with
    | h x =>
      obtain ⟨x, hx⟩ := x
      simp only [HMul.hMul, Mul.mul, GradedMonoid.fst_one, GradedMonoid.snd_one, one_def, mul_def]
      congr 1
      · exact AddZeroClass.zero_add k
      ·
        sorry

noncomputable instance :
    DirectSum.GRing (gradedPart F F_lt) where
  mul {i j} x y := (mulQuotient F F_lt i j).liftQ₂ _ _ (submodule_le_mulQuotient F F_lt i j)
    (submodule_le_flip_mulQuotient F F_lt i j)  x y
  mul_zero _ := by simp
  zero_mul _ := by simp
  mul_add  _ _ _ := by simp
  add_mul _ _ _ := by simp
  one := Submodule.Quotient.mk (1 : F 0)
  one_mul x := by
    obtain ⟨k, x⟩ := x
    induction x using Quotient.inductionOn with
    | h a => sorry
    --have : (1 : gradedPart' F F_lt 0) = Submodule.Quotient.mk (1 : F 0) := rfl
  mul_one x := by sorry
  mul_assoc := by sorry
  natCast := by sorry
  natCast_zero := by sorry
  natCast_succ := by sorry
  intCast := sorry
  intCast_ofNat := by sorry
  intCast_negSucc_ofNat := sorry
-/

end AssociatedGraded

end

namespace LieAlgebra.PBW

variable [CommRing R] [LinearOrder ι]

@[implicit_reducible]
noncomputable def Bracket.ofStructureConstant [AddCommGroup L] [Module R L]
    (bL : Module.Basis ι R L) [AddCommGroup M] [Module R M] (bM : Module.Basis σ R M)
    (f : ι → σ → σ →₀ R) : Bracket L M where
  bracket x y := (bL.repr x).sum fun i r ↦ (bM.repr y).sum fun j s ↦ bM.repr.symm (r • s • (f i j))

noncomputable def structureConstant [LieRing L] [LieAlgebra R L] (b : Module.Basis ι R L) :
    ι → ι → ι →₀ R :=
  fun i ↦ fun j ↦ b.repr ⁅b.repr.symm (Finsupp.single i 1), b.repr.symm (Finsupp.single j 1)⁆

lemma Finset.sum_sym2_of_eq_swap [AddCommMonoid L] (s : Finset ι) (ij : ι × ι) (hijs : ij ∈ s ×ˢ s)
    (hij : ij = ij.swap) (f : ι × ι → L) :
    ∑ ab ∈ s ×ˢ s with (Sym2.Rel.setoid ι) ab ij, f ab = f ij := by
  unfold Sym2.Rel.setoid
  simp only [Sym2.rel_iff']
  rw [Finset.sum_eq_single_of_mem ij (by simp [hijs])]
  intro _ hab habij
  simp only [← hij, or_self, Finset.mem_filter, Finset.mem_product] at hab
  exact (habij hab.2).elim

lemma Finset.sum_sym2_of_ne_swap [AddCommMonoid L] (s : Finset ι) (ij : ι × ι) (hijs : ij ∈ s ×ˢ s)
    (hij : ij ≠ ij.swap) (f : ι × ι → L) :
    ∑ ab ∈ s ×ˢ s with (Sym2.Rel.setoid ι) ab ij, f ab = f ij + f ij.swap := by
  unfold Sym2.Rel.setoid
  simp only [Sym2.rel_iff']
  rw [Finset.filter_or, Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h ↦ by simp [h, hij]),
    Finset.sum_eq_single_of_mem ij, Finset.sum_eq_single_of_mem ij.swap]
  · simpa [And.comm] using hijs
  · intro ab hab habij
    simp only [Finset.mem_filter] at hab
    exact (habij hab.2).elim
  · simpa [And.comm] using hijs
  · intro ab hab habij
    simp only [Finset.mem_filter] at hab
    exact (habij hab.2).elim
/-
 -- induct on basis...
@[implicit_reducible]
noncomputable def LieRing.ofStructureConstant [AddCommGroup L] [Module R L] (b : Module.Basis ι R L)
    (f : ι → ι → ι →₀ R) (hfa : ∀ i : ι, f i i = 0) (hfb : ∀ i j : ι, f i j + f j i = 0)
    (hfc : ∀ i j k m : ι, (∑ l ∈ (f j k).support, f i l m * f j k l) +
    (∑ l ∈ (f k i).support, f j l m * f k i l) + (∑ l ∈ (f i j).support, f k l m * f i j l) = 0) :
    LieRing L where
  bracket := (Bracket.ofStructureConstant b b f).bracket
  add_lie x y z := by
    unfold Bracket.bracket Bracket.ofStructureConstant
    simp only [map_add, map_smul, Module.Basis.repr_symm_apply]
    rw [Finsupp.sum_add_index' (fun _ ↦ by simp)]
    intro i r s
    simp_rw [add_smul]
    rw [Finsupp.sum_add]
  lie_add x y z := by
    unfold Bracket.bracket Bracket.ofStructureConstant
    simp only [map_add, Module.Basis.repr_symm_apply]
    rw [← Finsupp.sum_add]
    congr 1
    ext i r
    rw [Finsupp.sum_add_index' (fun _ ↦ by simp)]
    intro j s t
    simp [add_smul]
  lie_self x := by
    unfold Bracket.bracket Bracket.ofStructureConstant
    simp only [Module.Basis.repr_symm_apply, Finsupp.sum, map_smul]
    rw [← Finset.sum_product', Finset.sum_cancels_of_partition_cancels (Sym2.Rel.setoid ι)]
    intro ij hij
    by_cases h : ij.1 = ij.2
    · simp [Finset.sum_sym2_of_eq_swap (b.repr x).support ij hij (Prod.ext h h.symm), h, hfa]
    · rw [Finset.sum_sym2_of_ne_swap (b.repr x).support ij hij (ne_of_apply_ne Prod.fst h)]
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [smul_comm, ← smul_add, ← smul_add, ← map_add, hfb ij.1]
      simp
  leibniz_lie x y z := by
    unfold Bracket.bracket Bracket.ofStructureConstant
    simp only [Module.Basis.repr_symm_apply, Finsupp.sum, map_smul]
    sorry

@[implicit_reducible]
noncomputable def LieModule.ofStructureConstant [LieRing L] [LieAlgebra R L]
    (b : Module.Basis ι R L) [AddCommGroup M] [Module R M] (c : Module.Basis σ R M)
    (f : ι → σ → σ →₀ R) :
    LieRingModule L M where
  bracket x y := (b.repr x).sum fun i r ↦ (c.repr y).sum fun j s ↦ c.repr.symm (r • s • (f i j))
  add_lie x y z := sorry
  lie_add x y z := sorry
  leibniz_lie x y z := sorry
-/

-- List.SortedLE

noncomputable def subMin (x : ι →₀ ℕ) (h : x.support.Nonempty) : ι →₀ ℕ :=
  x - (Finsupp.single (x.support.min' h) 1)

lemma subMin_apply (x : ι →₀ ℕ) (h : x.support.Nonempty) (i : ι) :
    (subMin x h) i = x i - (Finsupp.single (x.support.min' h) 1) i :=
  rfl

/-- Action of a basis vector on polynomials, restricted to monomials. This is essentially
the recursive definition in Bourbaki, but with bracket expanded in structure constants,
and no degree restriction on domain. -/
noncomputable def actionAux (f : ι → ι → ι →₀ R) : ℕ → (ι →₀ ℕ) → ι → MvPolynomial ι R
  | 0, x, i => MvPolynomial.monomial (Finsupp.single i 1) 1
  | d + 1, x, i => if hi : ∀ j ∈ x.support, i ≤ j
    then MvPolynomial.monomial (x + Finsupp.single i 1) 1
    else have h : x.support.Nonempty := by grind only [= Finset.nonempty_def]
      (MvPolynomial.monomial (Finsupp.single (x.support.min' h) 1) (1 : R)) *
        (actionAux f d (subMin x h) i) +
      ∑ j ∈ (f i (x.support.min' h)).support,
        (f i (x.support.min' h) j) • actionAux f d (subMin x h) i

/-- Action of a basis vector on polynomials, restricted to monomials. -/
noncomputable def actionMap (f : ι → ι → ι →₀ R) (x : ι →₀ ℕ) (i : ι) : MvPolynomial ι R :=
  actionAux f (x.sum fun _ e => e) x i

-- TODO: show that this yields a representation

end LieAlgebra.PBW
