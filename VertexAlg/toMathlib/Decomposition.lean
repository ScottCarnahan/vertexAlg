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

variable {ι σ κ R L M : Type*}

section

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ) [Decomposition ℳ]

lemma support_subset_of_mem {i : ι} {x : M} (hi : x ∈ ℳ i)
    [(i : ι) → (x : ℳ i) → Decidable (x ≠ 0)] :
    DFinsupp.support (decomposeAddEquiv ℳ x) ⊆ {i} := by
  rw [decomposeAddEquiv_apply, decompose_of_mem ℳ hi]
  exact DirectSum.support_of_subset

lemma zero_of_mem_ne {i j : ι} (hij : i ≠ j) {x : M} (hi : x ∈ ℳ i) (hj : x ∈ ℳ j) :
    x = 0 := by
  classical
  have := support_subset_of_mem ℳ hi
  have := support_subset_of_mem ℳ hj
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

variable [AddCommMonoid M] [Module R M] (ℳ : ι → Submodule R M)

/-- The sum of pieces of a decomposition parametrized by the preimage of a point. -/
def fiberModule [DecidableEq ι] [Decomposition ℳ] [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)]
    (f : ι → κ) (k : κ) : Submodule R M where
  carrier := {x : M | ∀ i ∈ (decompose ℳ x).support, f i = k}
  add_mem' {a b} hx hy i hi := by
    simp only [decompose_add, DFinsupp.mem_support_toFun, add_apply] at hi
    obtain (h|h) : ((decompose ℳ) a) i ≠ 0 ∨ ((decompose ℳ) b) i ≠ 0 := by
      contrapose! hi
      simp [hi.1, hi.2]
    · simp only [DFinsupp.mem_support_toFun, Set.mem_setOf_eq] at hx
      exact hx i h
    · simp only [DFinsupp.mem_support_toFun, Set.mem_setOf_eq] at hy
      exact hy i h
  zero_mem' := by simp
  smul_mem' _ _ h i hi := by
    simp only [DFinsupp.mem_support_toFun, Set.mem_setOf_eq] at h hi
    refine h i ?_
    contrapose! hi
    simp [smul_apply, hi]

lemma mem_fiberModule_iff [DecidableEq ι] [Decomposition ℳ]
    [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] (f : ι → κ) (k : κ) (x : M) :
    x ∈ fiberModule ℳ f k ↔ ∀ i ∈ (decompose ℳ x).support, f i = k := by
  simp [fiberModule]

lemma decompose_mem_fiberModule_of [DecidableEq ι] [Decomposition ℳ]
    [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] (f : ι → κ) (k : κ) (x : M) (i : ι) :
    f i = k → (decompose ℳ x i : M) ∈ fiberModule ℳ f k := by
  simp only [mem_fiberModule_iff, decompose_coe, DFinsupp.mem_support_toFun]
  intro h j hj
  contrapose! hj
  have : j ≠ i := by contrapose! hj; rw [hj, h]
  exact of_eq_of_ne i j _ this

/-- The submodule of a fiberModule given by a single component. -/
@[simps]
def decomposeAsSubmodule [DecidableEq ι] [Decomposition ℳ]
    [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] (f : ι → κ) (k : κ) (i : ι) :
    Submodule R (fiberModule ℳ f k) where
  carrier := {x : fiberModule ℳ f k | x.1 ∈ ℳ i}
  add_mem' ha hb := by
    refine Set.mem_setOf.mpr ?_
    simp only [Submodule.coe_add]
    exact Submodule.add_mem (ℳ i) ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    refine Set.mem_setOf.mpr ?_
    simp only [SetLike.val_smul]
    exact Submodule.smul_of_tower_mem (ℳ i) c hx

/-
instance [DecidableEq ι] [Decomposition ℳ] [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] {κ : Type*}
    (f : ι → κ) (k : κ) [DecidablePred fun i ↦ f i = k] :
    Decomposition (decomposeAsSubmodule ℳ f k) where
  decompose' x := DFinsupp.mk (decompose ℳ x).support fun i ↦ if h : f i = k then
    ⟨(⟨decompose ℳ x i, decompose_mem_fiberModule_of ℳ f k x i h⟩ : fiberModule ℳ f k),
      by simp [decomposeAsSubmodule]⟩
    else 0
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    beta_reduce
    rw [@Subtype.ext_iff]



    sorry
  right_inv x := by
    ext j
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      obtain ⟨⟨x, hfx⟩, hdx⟩ := x
      simp only [SetLike.coe_sort_coe, coeAddMonoidHom_of, DFinsupp.mk_apply,
        DFinsupp.mem_support_toFun, Classical.dite_not, SetLike.coe_eq_coe]
      simp only [decomposeAsSubmodule, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hdx
      by_cases hij : j = i
      · by_cases hj : decompose ℳ x j = 0
        · have : x = 0 := by
            rw [hij, decompose_of_mem ℳ hdx] at hj
            simpa using hj
          rw [hij]
          simp only [this, decompose_zero, zero_apply, ↓reduceDIte, of_eq_same]
          exact SetLike.coe_eq_coe.mp rfl
        · simp only [hj, ↓reduceDIte]
          by_cases hfj : f j = k
          · ext
            simp only [hfj, ↓reduceDIte]
            rw [hij, decompose_of_mem ℳ hdx]
            simp
          · simp only [fiberModule, DFinsupp.mem_support_toFun, ne_eq, Submodule.mem_mk,
            AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hfx
            exact (hfj (hfx j hj)).elim
      · by_cases hj : decompose ℳ x j = 0
        · simp only [hj, ↓reduceDIte]
          rw [of_eq_of_ne i j _ hij]
        · simp only [hj, ↓reduceDIte]
          rw [of_eq_of_ne i j _ hij]
          by_cases hfj : f j = k
          · simp only [hfj, ↓reduceDIte, Submodule.mk_eq_zero, ZeroMemClass.coe_eq_zero]
            rw [← Submodule.coe_eq_zero, decompose_of_mem_ne ℳ hdx (fun (h : i = j) ↦ hij h.symm)]
          · simp [hfj]
    | add x y hx hy =>

      sorry

/-- An element of the fiberModule given by summing pieces in fibers. -/
def sumOverFiber [DecidableEq ι] {κ : Type*} [DecidableEq κ] [Decomposition ℳ]
    [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] (f : ι → κ) (k : κ) (x : M) : fiberModule ℳ f k :=
  ∑ i ∈ (decompose ℳ x).support,
    if h : f i = k then ⟨(decompose ℳ x i), decompose_mem_fiberModule_of ℳ f k x i h⟩ else 0



instance [DecidableEq ι] {κ : Type*} [DecidableEq κ] [Decomposition ℳ]
    [(i : ι) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] (f : ι → κ) :
    Decomposition (fiberModule ℳ f) where
  decompose' x := DFinsupp.mk ((decompose ℳ x).support.image f)
    fun k ↦ sumOverFiber ℳ f k x
  left_inv x := by
    simp [SetLike.coe_sort_coe, sumOverFiber]
    sorry
  right_inv x := by
    simp
    sorry

-/
end

section

section DirectSum.of
/- additional _of lemmas for isos already present in Mathlib -/
variable (R : Type*) [Semiring R] [DecidableEq ι]

@[simp] lemma sigmaLcurry_of {α : ι → Type*} [∀ i : ι, DecidableEq (α i)]
    {M : (i : ι) → α i → Type*} [∀ i : ι, ∀ j : α i, AddCommMonoid (M i j)]
    [∀ i : ι, ∀ j : α i, Module R (M i j)]
    (ij : (i : ι) × α i) (m : M ij.1 ij.2) :
    sigmaLcurryEquiv R (of (fun k ↦ M k.1 k.2) ij m) =
      of (fun i' ↦ ⨁ (j' : α i'), M i' j') ij.1 (of (fun j' ↦ M ij.1 j') ij.2 m) :=
  DFinsupp.sigmaCurry_single ij m

/-
/-- The types of the left and right sides don't match. Also not in simpNF -/
@[simp] lemma lequivCongrLeft_of' {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
    [(i : ι) → Module R (M i)] {κ : Type*} [DecidableEq κ] (e : κ ≃ ι) (k : κ) (m : M (e k)) :
    (lequivCongrLeft R e.symm) ((of M (e k)) m) = (of (fun k ↦ M (e k)) k) m := by
  simp only [Equiv.symm_symm]
  exact DFinsupp.comapDomain'_single e e.symm.right_inv k m
-/

@[simp] lemma lequivCongrLeft_of {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
    [(i : ι) → Module R (M i)] {κ : Type*} [DecidableEq κ] {e : ι ≃ κ} (i : ι) (k : κ)
    (hik : i = e.symm k) (m : M i) (m' : M (e.symm k)) (h : cast congr(M $hik) m = m') :
    (lequivCongrLeft R e) ((of M i) m) = (of _ k) m' := by
  rw [← lof_eq_of (R := R), lequivCongrLeft_lof R hik m m' h, lof_eq_of]

end DirectSum.of

section DirectSum.sigmaFiberLinearEquiv
/-
2. `sigmaFiberLinearEquiv_of` lemma, proved from the …_of lemmas for iso₁ and iso₂.
   This is all still very messy and probably not done the correct way.
-/
variable (R : Type*) [Semiring R] [DecidableEq ι] [DecidableEq κ] (f : ι → κ)

/-- A composition of two linear equivalences that gives turns a decomposition into a dependent pair
of decompositions. -/
def sigmaFiberLinearEquiv
    (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)] :
    (⨁ i : ι, M i) ≃ₗ[R] ⨁ (k : κ) (i : {i : ι // f i = k}), M i :=
  (lequivCongrLeft R (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaLcurryEquiv R (δ := fun (k : κ) ↦ (fun (i : { i : ι // f i = k}) ↦ M i)))

/-
lemma sigmaFiberLinearEquiv_of' (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] (ki : (k : κ) × {i : ι // f i = k})
    (m : M (Equiv.sigmaFiberEquiv f ki)) :
    (sigmaFiberLinearEquiv R f M) ((of (fun i ↦ M i) (Equiv.sigmaFiberEquiv f ki)) m) =
      (of _ ki.1) ((of (fun (j : { i : ι // f i = ki.1}) ↦ M j) ki.2) m) := by
  rw [sigmaFiberLinearEquiv, LinearEquiv.trans_apply, ← sigmaLcurry_of R,
    lequivCongrLeft_of R _ ki (by simp) _ m rfl]
  simp only [Equiv.symm_symm, sigmaLcurry_of]
  erw [sigmaLcurry_of]

@[simp] lemma sigmaFiberLinearEquiv_of (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] (i : ι) (m : M i) :
    (sigmaFiberLinearEquiv R f M) ((of M i) m) = (of _ ((Equiv.sigmaFiberEquiv f).symm i).1)
      ((of _ ((Equiv.sigmaFiberEquiv f).symm i).2) m) := by
  rw [sigmaFiberLinearEquiv, LinearEquiv.trans_apply, lequivCongrLeft_of R i
    ((Equiv.sigmaFiberEquiv f).symm i) (by simp) m _ rfl]

  --simp only [Equiv.symm_symm]
  erw [sigmaLcurry_of R _]
  exact AddMonoidHom.mem_eqLocusM.mp rfl

--  sigmaFiberLinearEquiv_of' R f M (ki := ⟨f i, ⟨i, rfl⟩⟩) m


-/
end DirectSum.sigmaFiberLinearEquiv

section coeLinearMap
variable (R : Type*) [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)
variable [DecidableEq ι]

/-- The codomain restriction of the summation map. -/
abbrev coeLinearMap.codRestrict :
  (⨁ (i : ι), ℳ i) →ₗ[R] (⨆ (i : ι), ℳ i : Submodule R M)
  := (LinearEquiv.ofEq _ _ range_coeLinearMap).toLinearMap ∘ₗ (coeLinearMap ℳ).rangeRestrict
  -- This is just an `abbrev` so that `simp` and other tactics will unfold it automatically.

lemma coeLinearMap.codRestrict_surjective :
  Function.Surjective (⇑(coeLinearMap.codRestrict R ℳ)) := by
  simp only [codRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective]
  exact LinearMap.surjective_rangeRestrict _
end coeLinearMap


/- MAIN PART:  Construction of induced decomposition -/

variable (R : Type*) [Semiring R]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {M : Type*} [AddCommMonoid M] [Module R M] (ℳ : ι → Submodule R M)
variable [DirectSum.Decomposition ℳ]
variable (f : ι → κ)

/-- The decomposition on the target type induced by a map of parametrizing types. -/
def induced : κ → Submodule R M
  := fun j ↦ (⨆ (i : { i : ι // f i = j}), ℳ i : Submodule R M)
/-
instance : (DirectSum.Decomposition (induced R ℳ f) ) :=
  DirectSum.Decomposition.ofLinearMap
    (induced R ℳ f)
    (lmap (fun _ ↦ coeLinearMap.codRestrict R _) ∘ₗ
      (sigmaFiberLinearEquiv R f (fun i ↦ ↥(ℳ i))).toLinearMap ∘ₗ
      (decomposeLinearEquiv ℳ).toLinearMap)
    (by
    -- 2 reduction steps:
      rw [← (decomposeLinearEquiv ℳ).symm.eq_comp_toLinearMap_iff _ _]
      apply linearMap_ext
    -- now simplify everything:
      intro i
      ext m
      unfold induced
      simp [lof_eq_of]
    ) (by
    -- 3 reduction steps:
      apply linearMap_ext
      intro j
      unfold induced -- needed in v4.29r8, but not in v4.28.0
      rw [← LinearMap.cancel_right
        (coeLinearMap.codRestrict_surjective R (fun (i : { i : ι // f i = j}) ↦ ((ℳ ↑i))))]
      apply linearMap_ext
    -- now simplify everything:
      intro ⟨i, hi⟩
      subst hi
      ext m : 1
      simp [lof_eq_of]
    )
-/
end

section

variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)

/-- The trivial decomposition into the sum over a singleton. -/
@[implicit_reducible]
protected def ofUnique [DecidableEq ι] [Unique ι] :
    Decomposition fun (_ : ι) ↦ (⊤ : Submodule R L) where
  decompose' x := of (fun _ ↦ (⊤ : Submodule R L)) default ⟨x, Submodule.mem_top⟩
  left_inv _ := by simp
  right_inv x := by
    ext j
    simp only [Unique.eq_default j, of_eq_same]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [Unique.eq_default i]
    | add x y hx hy => simp [hx, hy]
--#find_home! DirectSum.Decomposition.ofUnique --[Mathlib.Algebra.DirectSum.Decomposition]

variable [Zero ι] (p : L →ₗ[R] M)

/-- The decomposition induced by a section of a surjection, where the kernel is placed in degree
zero. -/
def submoduleOfSection (s : M →ₗ[R] L) (i : ι) [Decidable (i = 0)] :
    Submodule R L :=
  if i = 0 then (s.domRestrict (ℳ 0)).range ⊔ p.ker else (s.domRestrict (ℳ i)).range

lemma sub_mem_submoduleOfSection [DecidableEq ι] {s : M →ₗ[R] L}
    (hs : Function.LeftInverse p s) {i : ι} (hi : i = 0) {x : L} :
    x - s (p x) ∈ submoduleOfSection ℳ p s i := by
  simp only [submoduleOfSection, hi]
  exact Submodule.mem_sup_right (by simp [hs.eq])

lemma section_component_mem_submoduleOfSection [DecidableEq ι] [Decomposition ℳ]
    (i : ι) {s : M →ₗ[R] L} (x : L) :
    s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))) ∈
      submoduleOfSection ℳ p s i := by
  by_cases h : i = 0
  · simp only [submoduleOfSection, h, ↓reduceIte, LinearMap.range_domRestrict]
    refine Submodule.mem_sup_left ?_
    rw [h]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℳ i) 0) (decompose ℳ (p x)))
  · simp only [submoduleOfSection, h, ↓reduceIte, LinearMap.range_domRestrict]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℳ i) i) (decompose ℳ (p x)))

/-- The map to the decomposition induced by a section of a surjection. -/
def toDecompositionOfSection {p : L →ₗ[R] M} [DecidableEq ι] [Decomposition ℳ] (i : ι)
    {s : M →ₗ[R] L} (hs : Function.LeftInverse p s) :
    L →ₗ[R] submoduleOfSection ℳ p s i where
  toFun x := if hi : i = 0 then ⟨x - s (p x), sub_mem_submoduleOfSection ℳ p hs hi⟩ +
    ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
      section_component_mem_submoduleOfSection ℳ p i x⟩
  else ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
    section_component_mem_submoduleOfSection ℳ p i x⟩
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
    (⟨x - s (p x), sub_mem_submoduleOfSection ℳ p hs rfl⟩ : submoduleOfSection ℳ p s 0) +
    (⟨s (component R ι (fun i ↦ ℳ i) 0 (decompose ℳ (p x))),
      section_component_mem_submoduleOfSection ℳ p 0 x⟩ :
        submoduleOfSection ℳ p s 0) := by
  simp [toDecompositionOfSection]

@[simp]
lemma toDecompositionOfSection_apply_of_ne [DecidableEq ι] [Decomposition ℳ] {i : ι}
    (hi : i ≠ 0) {s : M →ₗ[R] L} (hs : Function.LeftInverse p s) (x : L) :
    toDecompositionOfSection ℳ i hs x =
    ⟨s (component R ι (fun i ↦ ℳ i) i (decompose ℳ (p x))),
      section_component_mem_submoduleOfSection ℳ p i x⟩ := by
  simp [hi, toDecompositionOfSection]

lemma mk_toDecompositionOfSection_apply [DecidableEq ι] [Decomposition ℳ]
    [(i : ι) → (x : (ℳ i)) → Decidable (x ≠ 0)] {s : M →ₗ[R] L} (hs : Function.LeftInverse p s)
    (x : L) :
    DirectSum.mk (fun i ↦ (submoduleOfSection ℳ p s i)) ((decompose ℳ (p x)).support ⊔ {0})
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
noncomputable def ofSection [DecidableEq ι] [Decomposition ℳ] (s : M →ₗ[R] L)
    (hs : Function.LeftInverse p s) :
    Decomposition (fun i ↦ submoduleOfSection ℳ p s i) := by
  refine ofLinearMap (fun i ↦ submoduleOfSection ℳ p s i) ?_ ?_ ?_
  · letI _ (i : ι) (x : ℳ i) := Classical.propDecidable (x ≠ 0)
    exact {
      toFun x := DirectSum.mk (fun i ↦ (submoduleOfSection ℳ p s i))
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
