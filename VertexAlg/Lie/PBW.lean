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
    refine Set.mem_of_subset_of_mem (IsConcreteLE.coe_subset_coe'.mpr (le_sSup ?_)) <|
      SetLike.mul_mem_graded (Submodule.coe_mem (fgi k)) (Submodule.coe_mem (fgj l))
    use k + l
    simp [add_le_add hki hlj]

--def associatedGraded [Ring R] (F : ι → Submodule R R)

end filtration

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
