/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Graded
public import VertexAlg.Lie.Extension
public import VertexAlg.toMathlib.Decomposition

/-!
Possibly add to `Mathlib.Algebra.Lie.Graded`.
-/

@[expose] public section

open DirectSum

variable {ι σ R L M N P : Type*}

section pullback

instance instZeroPullbackCoeZeroHom [Zero L] [Zero M] (f : ZeroHom L M) [Zero N] (g : ZeroHom N M) :
    Zero (Function.Pullback f g) where
  zero := ⟨0, by simp⟩

@[simp]
lemma zero_coe [Zero L] [Zero M] (f : ZeroHom L M) [Zero N] (g : ZeroHom N M) :
    (0 : Function.Pullback f g).1 = 0 :=
  rfl

instance instAddPullbackCoeAddMonoidHom [AddMonoid L] [AddMonoid M] (f : L →+ M) [AddMonoid N]
    (g : N →+ M) :
    Add (Function.Pullback f g) where
  add x y := ⟨x.1 + y.1, by simp [x.2, y.2]⟩

@[simp]
lemma add_coe [AddMonoid L] [AddMonoid M] {f : L →+ M} [AddMonoid N] {g : N →+ M}
    (x y : Function.Pullback f g) :
    (x + y).1 = x.1 + y.1 :=
  rfl

lemma nsmul_mem_pullback [AddMonoid L] [AddMonoid M] {f : L →+ M} [AddMonoid N] {g : N →+ M}
    (x : Function.Pullback f g) (n : ℕ) :
    f (n • x.1).1 = g (n • x.1).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [add_nsmul, Prod.fst_add, Prod.snd_add, AddMonoidHom.map_add, ih, one_smul]
      grind

instance instAddMonoidPullbackCoeAddMonoidHom [AddMonoid L] [AddMonoid M] (f : L →+ M) [AddMonoid N]
    (g : N →+ M) :
    AddMonoid (Function.Pullback f g) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero := ⟨0, by simp⟩
  zero_add _ := by ext <;> simp [zero_add]
  add_zero _ := by ext <;> simp
  nsmul n x := ⟨n • x.1, nsmul_mem_pullback x n⟩
  nsmul_zero n := by ext <;> simp
  nsmul_succ n x := by ext <;> simp [add_nsmul]

instance instAddCommMonoidPullbackCoeAddMonoidHom [AddCommMonoid L] [AddCommMonoid M] {f : L →+ M}
    [AddCommMonoid N] {g : N →+ M} :
    AddCommMonoid (Function.Pullback f g) where
  add_comm x y := by ext <;> simp [add_comm]


namespace LinearMap

variable [Semiring R] [AddCommMonoid L] [Module R L] [AddCommMonoid M] [Module R M] {f : L →ₗ[R] M}
    [AddCommMonoid N] [Module R N] {g : N →ₗ[R] M}

/-- The fiber product $X \times_Y Z$. -/
abbrev Pullback (f : L →ₗ[R] M) (g : N →ₗ[R] M) := Function.Pullback f g

namespace Pullback

instance : Zero (f.Pullback g) where zero := ⟨0, by simp⟩

@[simp] lemma zero_coe : (0 : f.Pullback g).1 = 0 := rfl
--#find_home! zero_module_coe --[Mathlib.Algebra.Module.LinearMap.Defs]

instance : Add (f.Pullback g) where
  add x y := ⟨x.1 + y.1, by simp [x.2, y.2]⟩

@[simp] lemma add_coe (x y : f.Pullback g) : (x + y).1 = x.1 + y.1 := rfl

lemma nsmul_mem_pullback (x : f.Pullback g) (n : ℕ) :
    f (n • x.1).1 = g (n • x.1).2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [x.2]

instance : AddCommMonoid (f.Pullback g) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero := ⟨0, by simp⟩
  zero_add _ := by ext <;> simp [zero_add]
  add_zero _ := by ext <;> simp
  nsmul n x := ⟨n • x.1, nsmul_mem_pullback x n⟩
  nsmul_zero n := by ext <;> simp
  nsmul_succ n x := by ext <;> simp [add_nsmul]
  add_comm _ _ := by ext <;> simp [add_comm]

instance : SMul R (f.Pullback g) where
  smul r x := ⟨(r • x.1.1, r • x.1.2), by simp [x.2]⟩

@[simp] lemma smul_coe (r : R) (x : f.Pullback g) : (r • x).1 = r • x.1 := rfl
--#find_home! smul_coe --[Mathlib.Algebra.Module.LinearMap.Defs]

instance : Module R (f.Pullback g) where
  mul_smul _ _ x := by ext1; simp [mul_smul]
  one_smul _ := by ext1; simp
  smul_zero _ := by ext1; simp
  smul_add _ _ _ := by ext1; simp
  add_smul _ _ _ := by ext1; simp [add_smul]
  zero_smul _ := by ext1; simp

/-- The linear projection from the fiber product to the first factor. -/
@[simps]
def fst (f : L →ₗ[R] M) (g : N →ₗ[R] M) : f.Pullback g →ₗ[R] L where
  toFun p := p.val.1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma fst_injective (hg : Function.Injective g) : Function.Injective (fst f g) := by
  intro x y h
  simp only [fst_apply] at h
  ext
  · exact h
  · exact hg (by rw [← x.2, h, y.2])

lemma fst_surjective (hg : Function.Surjective g) : Function.Surjective (fst f g) := by
  intro x
  simp only [fst_apply]
  obtain ⟨y, hy⟩ := hg (f x)
  use ⟨(x, y), by simp [hy]⟩

lemma fst_bijective (hg : Function.Bijective g) : Function.Bijective (fst f g) :=
  ⟨fst_injective <| hg.injective, fst_surjective <| hg.surjective⟩

/-- The linear projection from the fiber product to the second factor. -/
@[simps]
def snd (f : L →ₗ[R] M) (g : N →ₗ[R] M) : f.Pullback g →ₗ[R] N where
  toFun p := p.val.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

lemma snd_injective (hf : Function.Injective f) : Function.Injective (snd f g) := by
  intro x y h
  simp only [snd_apply] at h
  ext
  · exact hf (by rw [x.2, h, y.2])
  · exact h

lemma snd_surjective (hf : Function.Surjective f) : Function.Surjective (snd f g) := by
  intro x
  simp only [snd_apply]
  obtain ⟨y, hy⟩ := hf (g x)
  use ⟨(y, x), by simp [hy]⟩

lemma snd_bijective (hf : Function.Bijective f) : Function.Bijective (snd f g) :=
  ⟨snd_injective <| hf.injective, snd_surjective <| hf.surjective⟩

/-- The canonical map from a module with two maps to the legs of a pullback diagram to the
pullback object. -/
@[simps]
def toPullback [AddCommMonoid P] [Module R P] {fL : P →ₗ[R] L} {fN : P →ₗ[R] N}
    (hf : f ∘ₗ fL = g ∘ₗ fN) :
    P →ₗ[R] f.Pullback g where
  toFun x := ⟨(fL x, fN x), by rw [LinearMap.ext_iff] at hf; simpa using hf x⟩
  map_add' _ _ := Subtype.ext <| Prod.ext_iff.mpr (by simp)
  map_smul' _ _ := Subtype.ext <| Prod.ext_iff.mpr (by simp)

end Pullback

end LinearMap

namespace LinearEquiv

variable [Semiring R] [AddCommMonoid L] [Module R L] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The pullback of an isomorphism along a linear map is an isomorphism. -/
noncomputable def PullbackSnd (f : L ≃ₗ[R] M) (g : N →ₗ[R] M) :
    f.toLinearMap.Pullback g ≃ₗ[R] N :=
  LinearEquiv.ofBijective (LinearMap.Pullback.snd f.toLinearMap g) (by
    refine LinearMap.Pullback.snd_bijective ?_
    rw [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective f)

@[simp]
lemma pullbackSnd_symm_apply (f : L ≃ₗ[R] M) (g : N →ₗ[R] M) (x : N) :
    (PullbackSnd f g).symm x = ⟨(f.symm (g x), x), by simp⟩ := by
  simp [symm_apply_eq, PullbackSnd]

/-- The pullback of an isomorphism along a linear map is an isomorphism. -/
noncomputable def PullbackFst (f : L →ₗ[R] M) (g : N ≃ₗ[R] M) :
    f.Pullback g.toLinearMap ≃ₗ[R] L :=
  LinearEquiv.ofBijective (LinearMap.Pullback.fst f g.toLinearMap) (by
    refine LinearMap.Pullback.fst_bijective ?_
    rw [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective g)

@[simp]
lemma pullbackFst_symm_apply (f : L →ₗ[R] M) (g : N ≃ₗ[R] M) (x : L) :
    (PullbackFst f g).symm x = ⟨(x, g.symm (f x)), by simp⟩ := by
  simp [symm_apply_eq, PullbackFst]

end LinearEquiv

namespace DirectSum.Decomposition

variable [CommSemiring R] [AddCommMonoid L] [Module R L] [AddCommMonoid M] [Module R M]

variable (f : L →ₗ[R] M) (ℳ : ι → Submodule R M)

/-- The pullback of a decomposition along a linear map. -/
def Pullback [DecidableEq ι] [Decomposition ℳ] : ι → Submodule R L :=
  fun i ↦ (LinearMap.Pullback.fst f
    ((decomposeLinearEquiv ℳ).symm ∘ₗ DirectSum.lof R ι (fun i ↦ ℳ i) i)).range

lemma pullback_apply [DecidableEq ι] [Decomposition ℳ] (i : ι) :
    Pullback f ℳ i = (ℳ i).comap f := by
  ext
  simp [Pullback]

-- want equiv from L to sum Pullback. Have decompose: equiv from M to sum ℳ i. This should be
-- change definition of Pullback to LinearMap.Pullback of
-- `((decompose ℳ).symm ∘ₗ DirectSum.of ℳ i)` along f.

end DirectSum.Decomposition

end pullback

namespace LieAlgebra.Extension

variable [CommRing R] [LieRing L] [LieAlgebra R L] (ℒ : ι → Submodule R L) [LieRing M]
  [LieAlgebra R M] (E : LieAlgebra.Extension R M L)

/-- The decomposition on an extension induced by a section. -/
def decompositionOfSection [Zero ι] (i : ι) [Decidable (i = 0)] (s : L →ₗ[R] E.L) :
    Submodule R E.L :=
  if i = 0 then (s.domRestrict (ℒ 0)).range ⊔ E.proj.ker else (s.domRestrict (ℒ i)).range

lemma sub_section_mem_decompositionOfSection [DecidableEq ι] [Decomposition ℒ] [Zero ι]
    {s : L →ₗ[R] E.L} (hs : Function.LeftInverse E.proj s) {i : ι} (hi : i = 0) (x : E.L) :
    x - s (E.proj x) ∈ E.decompositionOfSection ℒ i s := by
  simp only [decompositionOfSection, hi]
  exact Submodule.mem_sup_right (by simp [hs.eq])

lemma section_component_mem_decompositionOfSection [DecidableEq ι] [Decomposition ℒ] [Zero ι]
    (i : ι) {s : L →ₗ[R] E.L} (x : E.L) :
    s (component R ι (fun i ↦ ℒ i) i (decompose ℒ (E.proj x))) ∈
      E.decompositionOfSection ℒ i s := by
  by_cases h : i = 0
  · simp only [decompositionOfSection, h, ↓reduceIte, LinearMap.range_domRestrict,
    LieIdeal.toLieSubalgebra_toSubmodule, LieHom.ker_toSubmodule]
    refine Submodule.mem_sup_left ?_
    rw [h]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℒ i) 0) (decompose ℒ (E.proj x)))
  · simp only [decompositionOfSection, h, ↓reduceIte, LinearMap.range_domRestrict]
    exact Submodule.apply_coe_mem_map s ((component R ι (fun i ↦ ℒ i) i) (decompose ℒ (E.proj x)))

/-- The map to the decomposition on an extension induced by a section. -/
def toDecompositionOfSection [DecidableEq ι] [Decomposition ℒ] [Zero ι] (i : ι) {s : L →ₗ[R] E.L}
    (hs : Function.LeftInverse E.proj s) (x : E.L) :
    decompositionOfSection ℒ E i s :=
  if hi : i = 0 then ⟨x - s (E.proj x), E.sub_section_mem_decompositionOfSection ℒ hs hi x⟩ +
    ⟨s (component R ι (fun i ↦ ℒ i) i (decompose ℒ (E.proj x))),
      E.section_component_mem_decompositionOfSection ℒ i x⟩
  else ⟨s (component R ι (fun i ↦ ℒ i) i (decompose ℒ (E.proj x))),
    E.section_component_mem_decompositionOfSection ℒ i x⟩

@[simp]
lemma toDecompositionOfSection_apply_zero [DecidableEq ι] [Decomposition ℒ] [Zero ι]
    {s : L →ₗ[R] E.L} (hs : Function.LeftInverse E.proj s) (x : E.L) :
    toDecompositionOfSection ℒ E 0 hs x =
    ⟨x - s (E.proj x), E.sub_section_mem_decompositionOfSection ℒ hs rfl x⟩ +
    (⟨s (component R ι (fun i ↦ ℒ i) 0 (decompose ℒ (E.proj x))),
      E.section_component_mem_decompositionOfSection ℒ 0 x⟩ :
        decompositionOfSection ℒ E 0 s) := by
  simp [toDecompositionOfSection]

@[simp]
lemma toDecompositionOfSection_apply_of_ne [DecidableEq ι] [Decomposition ℒ] [Zero ι] {i : ι}
    (hi : i ≠ 0) {s : L →ₗ[R] E.L} (hs : Function.LeftInverse E.proj s) (x : E.L) :
    toDecompositionOfSection ℒ E i hs x =
    ⟨s (component R ι (fun i ↦ ℒ i) i (decompose ℒ (E.proj x))),
      E.section_component_mem_decompositionOfSection ℒ i x⟩ := by
  simp [hi, toDecompositionOfSection]

variable [DecidableEq ι] [AddCommMonoid ι] [GradedLieAlgebra ℒ]
/-
--set_option trace.Meta.synthInstance true in
noncomputable instance {s : L →ₗ[R] E.L} (hs : Function.LeftInverse E.proj s) :
    Decomposition (fun i ↦ E.decompositionOfSection ℒ i s) where
  decompose' x :=
    letI _ (i : ι) (x : ℒ i) := Classical.propDecidable (x ≠ 0)
    DFinsupp.mk (decompose ℒ (E.proj x)).support (fun i ↦ (E.toDecompositionOfSection ℒ i hs x))
  left_inv x := by
    simp only [decompositionOfSection, LieIdeal.toLieSubalgebra_toSubmodule,
      LieHom.ker_toSubmodule, SetLike.coe_sort_coe]

    refine E.eq_of_proj_eq hs ?_ ?_
    · sorry

    sorry


  right_inv := sorry
-/
end LieAlgebra.Extension

section GradedLieRing

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [SetLike σ L] [AddSubmonoidClass σ L] (ℒ : ι → σ)

open DirectSum

variable (A : ι → Type*)
/-- A graded version of `Bracket`. Grades are combined additively, like
`AddMonoidAlgebra`. -/
class GBracket [Add ι] where
  /-- The homogeneous multiplication map `bracket`. We do not use `A i → A j → A (i + j)` because
    the `leibniz_lie` rule for graded Lie algebras would then require a cast. -/
  bracket {i j k} (h : i + j = k) : A i → A j → A k

namespace DirectSum

/-- A graded version of `LieRing`. -/
class GLieRing [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] extends GBracket A where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ {i j k} (h : i + j = k) (x y : A i) (z : A j),
    bracket h (x + y) z = bracket h x z + bracket h y z
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ {i j k} (h : i + j = k) (x : A i) (y z : A j),
    bracket h x (y + z) = bracket h x y + bracket h x z
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ {i j} (h : i + i = j) (x : A i), bracket h x x = 0
  protected lie_antisymm : ∀ {i j k} (hij : i + j = k) (hji : j + i = k) (x : A i) (y : A j),
    bracket hij x y + bracket hji y x = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ {i j k ij ik jk ijk} (hij : i + j = ij) (hik : i + k = ik)
      (hjk : j + k = jk) (hi : i + jk = ijk) (hk : ij + k = ijk) (hj : j + ik = ijk) (x : A i)
      (y : A j) (z : A k),
    bracket hi x (bracket hjk y z) = bracket hk (bracket hij x y) z + bracket hj y (bracket hik x z)

/-- The piecewise multiplication from the `GBracket` instance, as a bundled homomorphism. -/
@[simps]
def gBracketHom [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] {i j k} (h : i + j = k) :
    A i →+ A j →+ A k where
  toFun a :=
    { toFun := fun b => GBracket.bracket h a b
      map_zero' := by
        have : GBracket.bracket h a (0 : A j) = GBracket.bracket h a 0 := rfl
        nth_rw 1 [← add_zero 0] at this
        rwa [GLieRing.lie_add, add_eq_left] at this
      map_add' x y := by rw [GLieRing.lie_add] }
  map_zero' := by
    ext b
    have : GBracket.bracket h (0 : A i) b = GBracket.bracket h 0 b := rfl
    nth_rw 1 [← add_zero 0] at this
    rwa [GLieRing.add_lie, add_eq_left] at this
  map_add' _ _ := by
    ext b
    simp [GLieRing.add_lie]

/-- The multiplication from the `GBracket` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
def bracketHom [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
    AddMonoidHom.flip <|
      DirectSum.toAddMonoid fun _ =>
        AddMonoidHom.flip <| (DirectSum.of A _).compHom.comp <| gBracketHom A rfl

instance [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    Bracket (⨁ i, A i)  (⨁ i, A i) where
  bracket a b := bracketHom A a b

@[simp]
lemma bracketHom_apply [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    (a b : ⨁ i, A i) :
    bracketHom A a b = ⁅a, b⁆ := rfl

@[simp]
lemma bracket_of_of [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j} (a : A i) (b : A j) :
    ⁅of A i a, of A j b⁆ = of A (i + j) (GBracket.bracket rfl a b) := by
  simp [← bracketHom_apply]

lemma rec_bracket [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A]
    {i j k l} (a : A i) (b : A j) (hk : i + j = k) (hl : i + j = l) (hkl : k = l) :
    Eq.rec (GBracket.bracket hk a b) hkl = GBracket.bracket hl a b := by
  grind

instance instBracket [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)] [GLieRing A] :
    Bracket (⨁ i, A i) (⨁ i, A i) where
  bracket := fun a b => bracketHom A a b

/-- `GLieRing` implies a Lie ring structure. -/
instance GLieRing.toLieRing [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [GLieRing A] :
    LieRing (⨁ i, A i) :=
  { (inferInstance : AddCommGroup _) with
    bracket x y := ⁅x, y⁆
    add_lie _ _ _ := by simp [← bracketHom_apply]
    lie_add _ _ _ := by simp [← bracketHom_apply]
    lie_self x := by
      have hsum (i : ι) (a : A i) (f : (⨁ i, A i)) :
          ⁅(of A i a), f⁆ + ⁅f, (of A i a)⁆ = 0 := by
        induction f using DirectSum.induction_on' with
        | h0 => simp [← bracketHom_apply]
        | hadd j b f hj _ h =>
          simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at h ⊢
          rw [add_rotate, add_left_comm, h, add_zero]
          ext k
          by_cases h : i + j = k
          · simp [of_apply, h, add_comm i j ▸ h, rec_bracket, GLieRing.lie_antisymm]
          · simp [of_apply, h, add_comm i j ▸ h]
      induction x using DirectSum.induction_on' with
      | h0 => simp [← bracketHom_apply]
      | hadd j b f hj _ h =>
        simp only [← bracketHom_apply] at h hsum
        rw [← bracketHom_apply, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h,
          add_zero, add_assoc, add_comm (((bracketHom A) f) ((of A j) b)), hsum]
        simp [GLieRing.lie_self]
    leibniz_lie x y z := by
      have hbss (i j : ι) (a : A i) (b : A j) :
          ⁅of A i a, ⁅of A j b, z⁆⁆ =
          ⁅of A j b, ⁅of A i a, z⁆⁆ +
          ⁅⁅of A i a, of A j b⁆, z⁆ := by
        induction z using DirectSum.induction_on' with
        | h0 => simp [← bracketHom_apply]
        | hadd k c f _ _ ih =>
          simp only [← bracketHom_apply, map_add] at ih ⊢
          rw [ih]
          simp only [bracketHom_apply, ← add_assoc]
          rw [add_right_cancel_iff, add_right_comm, add_right_cancel_iff]
          ext l
          by_cases h : i + j + k = l
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h, rec_bracket,
            GLieRing.leibniz_lie, add_comm (GBracket.bracket _ (GBracket.bracket _ a b) c)]
          · simp [of_apply, h, add_assoc i j k ▸ h, add_assoc j i k ▸ add_comm i j ▸ h]
      have hbs (i : ι) (a : A i) :
          ⁅of A i a, ⁅y, z⁆⁆ = ⁅y, ⁅of A i a, z⁆⁆ + ⁅⁅of A i a, y⁆, z⁆ := by
        induction y using DirectSum.induction_on' with
        | h0 => simp [← bracketHom_apply]
        | hadd j b f _ _ ih =>
          simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at ih ⊢
          rw [ih]
          simp only [bracketHom_apply, ← add_assoc]
          rw [add_right_cancel_iff, add_right_comm, add_right_cancel_iff]
          exact hbss i j a b
      induction x using DirectSum.induction_on' with
      | h0 => simp [← bracketHom_apply]
      | hadd i a f _ _ ih =>
        simp only [← bracketHom_apply, map_add, AddMonoidHom.add_apply] at ih ⊢
        rw [ih]
        simp only [bracketHom_apply, ← add_assoc]
        rw [add_right_cancel_iff, ← add_rotate, add_right_cancel_iff]
        exact hbs i a }

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[ext] class GLieAlgebra (R : Type*) (A : ι → Type*) [CommRing R] [AddCommMonoid ι]
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] extends GLieRing A where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.
  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : ∀ (t : R) {i j k} (h : i + j = k) (x : A i) (y : A j),
    bracket h x (t • y) = t • bracket h x y

/-- `GLieAlgebra` implies a Lie algebra structure. -/
instance GLieAlgebra.toLieAlgebra [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommGroup (A i)]
    [∀ i, Module R (A i)] [GLieAlgebra R A] : LieAlgebra R (⨁ i, A i) where
  add_smul := Module.add_smul
  zero_smul := MulActionWithZero.zero_smul
  lie_smul r x y := by
    have (i : ι) (a : A i) : ⁅of A i a, r • y⁆ = r • ⁅of A i a, y⁆ := by
      induction y using DirectSum.induction_on' with
        | h0 => simp
        | hadd j b f _ _ ih =>
          simp only [smul_add, lie_add, ih, add_left_inj, ← bracketHom_apply, ]
          rw [← of_smul]
          simp only [toAddMonoid_of, AddMonoidHom.flip_apply, AddMonoidHom.coe_comp,
            Function.comp_apply, AddMonoidHom.compHom_apply_apply, gBracketHom_apply_apply,
            GLieAlgebra.lie_smul]
          rw [of_smul]
    induction x using DirectSum.induction_on' with
    | h0 => simp
    | hadd i b f _ _ ih =>
      simp only [add_lie, ih, smul_add, add_left_inj]
      exact this i b

-- Internal grading?
/-
/-- A type alias of sigma types for graded monoids. -/
def GradedBracket :=
  Sigma A
namespace GradedBracket
/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type*} : ∀ i, A i → GradedBracket A :=
  Sigma.mk
/-- `GBracket` implies `Bracket (GradedMonoid A)`. -/
instance GBracket.toBracket [Add ι] [GBracket A] : Bracket (GradedBracket A) (GradedBracket A) :=
  ⟨fun x y : GradedBracket A => ⟨_, GBracket.bracket rfl x.snd y.snd⟩⟩
@[simp] theorem fst_bracket [Add ι] [GBracket A] (x y : GradedBracket A) :
    ⁅x, y⁆.fst = x.fst + y.fst := rfl
@[simp] theorem snd_bracket [Add ι] [GBracket A] (x y : GradedBracket A) :
    ⁅x, y⁆.snd = GBracket.bracket rfl x.snd y.snd := rfl
theorem mk_bracket_mk [Add ι] [GBracket A] {i j} (a : A i) (b : A j) :
    ⁅mk i a, mk j b⁆ = mk (i + j) (GBracket.bracket rfl a b) :=
  rfl
/-- A version of `GradedMonoid.ghas_one` for internally graded objects. -/
class SetLike.GradedBracket {L} {S : Type*} [SetLike S L] [Bracket L L] [Add ι] (A : ι → S) :
    Prop where
  /-- Bracket is homogeneous -/
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → ⁅gi, gj⁆ ∈ A (i + j)
-/

end DirectSum

namespace LieDerivation

@[simp]
lemma toModule_lof_smul_of [DecidableEq ι] [AddCommMonoid ι]
    (φ : ι →+ R) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] (k : ι) (b : A k) :
    (toModule R ι (⨁ (i : ι), A i) fun i ↦ lof R ι A i ∘ₗ (φ i • LinearMap.id))
      (of A k b) = (φ k) • (of A k b) := by
  simp [← lof_eq_of R]

end LieDerivation
