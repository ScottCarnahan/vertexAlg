/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Extension

/-!
Some should be added To `Mathlib.Algebra.Lie.Extension`. However, specialized lemmata which are
better written as general principles are frowned upon.
-/

@[expose] public section

namespace LieAlgebra

open Function

variable {L M N R : Type*}

section

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M] [LieRing N]
[LieAlgebra R N]

lemma IsExtension.range_eq_ker (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) (h : IsExtension i p) :
    LinearMap.range i.toLinearMap = p.ker := by
  have := h.exact
  rw [← LieSubalgebra.coe_set_eq] at this
  exact Submodule.ext fun x ↦ Eq.to_iff (congrFun this x)

lemma proj_choose_sub_mem (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x : L) :
    E.proj_surjective.hasRightInverse.choose x - s x ∈ E.proj.ker := by
  rw [LieHom.mem_ker, map_sub, hs, E.proj_surjective.hasRightInverse.choose_spec, sub_eq_zero]

end

section
open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] [LieRingModule L M]
[LieModule R L M] (c : twoCocycle R L M)

@[simp] lemma of_sub (x y : L × M) : ofProd c (x - y) = ofProd c x - ofProd c y := rfl

end

namespace Extension

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

section TwoCocycle

variable [IsLieAbelian M] [LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

/-- The standard section of the extension, coming from the product decomposition. -/
@[simps]
def section_ofTwoCocycle : L →ₗ[R] (ofTwoCocycle c).L where
  toFun x := ofAlg c (ofProd c (x, 0))
  map_add' _ _ := by rw [← Prod.mk_zero_add_mk_zero, of_add, map_add]
  map_smul' _ _ := by rw [← Prod.smul_mk_zero, of_smul, map_smul, RingHom.id_apply]

lemma section_proj_leftInverse : LeftInverse (ofTwoCocycle c).proj (section_ofTwoCocycle c) := by
  intro x
  rfl

end TwoCocycle

@[simp]
lemma toKer_coe (E : Extension R M L) (x : M) :
    E.toKer x = E.incl x :=
  rfl

lemma ofAlg_ofProd [LieRingModule L M] [LieModule R L M] [IsLieAbelian M] (c : twoCocycle R L M)
    (x : M) : (ofAlg c) (ofProd c (0, x)) = (ofTwoCocycle c).incl x  := by
  rfl

@[simp]
lemma twoCocycleOf_apply_apply [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x y : L) :
    (E.twoCocycleOf hs).1 x y = E.toKer.symm ⟨⁅s x, s y⁆ - s ⁅x, y⁆, by simp [hs.eq]⟩ := by
  exact (DFunLike.congr_arg E.toKer.symm rfl)

-- remove?
lemma twoCocycleOf_bracket [IsLieAbelian M] (E : Extension R M L) {s : L →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (x y : L) :
    ⁅s x, s y⁆ = s ⁅x, y⁆ + E.toKer ((E.twoCocycleOf hs).1 x y) := by
  simp

@[simp]
lemma twoCocycleOf_ofTwoCocycle [LieRingModule L M] [LieModule R L M] [IsLieAbelian M]
    (c : twoCocycle R L M) :
    (twoCocycleOf (ofTwoCocycle c) (section_proj_leftInverse c)).1 = c := by
  ext x y
  simp only [twoCocycleOf_coe_coe, LinearMap.compr₂_apply, LinearMap.coe_mk,
    section_ofTwoCocycle_apply, AddHom.coe_mk, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  refine (LinearEquiv.symm_apply_eq (ofTwoCocycle c).toKer.toLinearEquiv).mpr ?_
  refine (Subtype.coe_eq_of_eq_mk ?_).symm
  rw [bracket]
  simp only [LieEquiv.coe_toLinearEquiv, toKer_coe, ofTwoCocycle_incl_apply,
    LieEquiv.symm_apply_apply]
  rw [← map_sub]
  simp [bracket_ofTwoCocycle, ← of_sub]
  rfl

variable [LieRing N] [LieAlgebra R N] (E : Extension R N M)

/- The equivalence between the range of the inclusion and the source.
def sectLeft (E : Extension R N M) : E.incl.range ≃ₗ[R] N :=
  (LinearEquiv.ofInjective E.incl.toLinearMap E.incl_injective).symm
@[simp]
lemma incl_sectLeft (E : Extension R N M) (x : E.incl.range) :
    E.incl (E.sectLeft x) = x.val := by
  rw [sectLeft, ← LieHom.coe_toLinearMap, ← LinearEquiv.ofInjective_apply (h := E.incl_injective)]
  exact Subtype.eq_iff.mp <| LinearEquiv.apply_symm_apply _ x
 -/

lemma eq_of_proj_eq (E : Extension R N M) {x y : E.L} {s : M →ₗ[R] E.L} (hs : LeftInverse E.proj s)
    (hK : E.toKer.symm ⟨x - s (E.proj x), by simp [hs.eq]⟩ =
      E.toKer.symm ⟨y - s (E.proj y), by simp [hs.eq]⟩) (hp : E.proj x = E.proj y) :
    x = y := by
  rwa [EquivLike.apply_eq_iff_eq, Subtype.mk_eq_mk, hp, sub_left_inj] at hK

/-- `Extension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
@[ext] structure Equiv (E' : Extension R N M) where
  /-- The homomorphism -/
  toLieEquiv : E.L ≃ₗ⁅R⁆ E'.L
  /-- The left-hand side of the diagram commutes. -/
  incl_comm : toLieEquiv.comp E.incl = E'.incl
  /-- The right-hand side of the diagram commutes. -/
  proj_comm : E'.proj.comp toLieEquiv = E.proj

namespace Equiv

instance : Mul (E.Equiv E) where
  mul x y := {
    toLieEquiv := x.toLieEquiv.trans y.toLieEquiv
    incl_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply, ← LieHom.comp_apply _ _ z,
        x.incl_comm, ← LieHom.comp_apply, y.incl_comm]
    proj_comm := by
      ext z
      rw [LieHom.comp_apply, LieEquiv.trans, LieHom.comp_apply,
        ← LieHom.comp_apply _ _ (x.toLieEquiv.toLieHom z), y.proj_comm, ← LieHom.comp_apply,
        x.proj_comm] }

@[simp]
lemma mul_eq (x y : E.Equiv E) : (x * y).toLieEquiv = x.toLieEquiv.trans y.toLieEquiv :=
  rfl

instance : One (E.Equiv E) where
  one := {
    toLieEquiv := LieEquiv.refl
    incl_comm := by ext; simp
    proj_comm := by ext; simp }

@[simp] lemma one_eq : (1 : E.Equiv E).toLieEquiv = LieEquiv.refl := rfl

instance : Inv (E.Equiv E) where
  inv x := {
    toLieEquiv := x.toLieEquiv.symm
    incl_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, comp_apply]
      nth_rw 2 [show E.incl y = x.toLieEquiv.symm (x.toLieEquiv (E.incl y)) by simp]
      have : (x.toLieEquiv (E.incl y)) = (x.toLieEquiv.comp E.incl) y := by
        rw [LieHom.comp_apply, LieEquiv.coe_toLieHom]
      rw [this, x.incl_comm]
    proj_comm := by
      ext y
      simp only [LieHom.coe_comp, LieEquiv.coe_coe, comp_apply]
      rw [show E.proj y = E.proj.comp x.toLieEquiv (x.toLieEquiv.symm y) by simp, x.proj_comm]
  }

@[simp] lemma inv_eq (x : E.Equiv E) : x⁻¹.toLieEquiv = x.toLieEquiv.symm := rfl

instance : Group (E.Equiv E) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel x := by ext; simp

end Equiv

section Lift

/-- Lift a Lie subalgebra of the target to the extension, when the restricted 2-cocycle is trivial.
-/
@[simps]
def trivialLift [IsLieAbelian N] (E : Extension R N M) {s : M →ₗ[R] E.L} (hs : LeftInverse E.proj s)
    {P : LieSubalgebra R M} (hP : ∀ (p q : P), (E.twoCocycleOf hs).1 p q = 0) :
    LieSubalgebra R E.L where
  carrier := (s.domRestrict P).range
  add_mem' {a b} ha hb  := by
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x + y
    simp [← hx, ← hy]
  zero_mem' := by
    use 0
    simp
  smul_mem' r {x} hx := by
    obtain ⟨y, hy⟩ := hx
    use r • y
    simp [hy]
  lie_mem' {a b} ha hb := by
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    rw [← hx, ← hy]
    let x' : P := ⟨x.1, SetLike.coe_mem x⟩
    let y' : P := ⟨y.1, SetLike.coe_mem y⟩
    simp_all only [Subtype.forall, LinearMap.domRestrict_apply, LinearMap.range_domRestrict,
      Submodule.map_coe, Set.mem_image, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule]
    use ⁅x', y'⁆
    constructor
    · exact LieSubalgebra.lie_mem P (SetLike.coe_mem x') (SetLike.coe_mem y')
    · simp only [Subtype.coe_eta, LieSubalgebra.coe_bracket_of_module, ← hx, ← hy, x', y']
      rw [twoCocycleOf_bracket E hs, left_eq_add,
        hP x.1 (SetLike.coe_mem x) y.1 (SetLike.coe_mem y), map_zero, ZeroMemClass.coe_zero]

lemma domRestrict_section_injective (E : Extension R N M) {s : M →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (P : LieSubalgebra R M) :
    Injective (s.domRestrict P) := by
  rw [LinearMap.injective_domRestrict_iff, LinearMap.ker_eq_bot.mpr (LeftInverse.injective hs),
    inf_bot_eq]

lemma domRestrict_proj_injective [IsLieAbelian N] (E : Extension R N M) {s : M →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) {P : LieSubalgebra R M}
    (hP : ∀ (p q : P), (E.twoCocycleOf hs).1 p q = 0) :
    Injective (E.proj.domRestrict (E.trivialLift hs hP)) := by
  intro x y h
  obtain ⟨x', hx'⟩ := x
  obtain ⟨y', hy'⟩ := y
  simp only [LinearMap.domRestrict_apply, LieHom.coe_toLinearMap] at h
  simp only [trivialLift, LinearMap.range_domRestrict, Submodule.map_coe, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_image, SetLike.mem_coe,
    LieSubalgebra.mem_toSubmodule] at hx' hy'
  obtain ⟨x'', hx''⟩ := hx'
  obtain ⟨y'', hy''⟩ := hy'
  rw [← hy''.2, ← hx''.2, hs, hs] at h
  simp [h, ← hy''.2, ← hx''.2]

lemma proj_domRestrict (E : Extension R N M) {s : M →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) (P : LieSubalgebra R M) (x : P) :
    E.proj (s.domRestrict P x) = x := by
  rw [LinearMap.domRestrict_apply, hs]

lemma domRestrict_section_proj [IsLieAbelian N] (E : Extension R N M) {s : M →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) {P : LieSubalgebra R M}
    (hP : ∀ (p q : P), (E.twoCocycleOf hs).1 p q = 0) (x : E.trivialLift hs hP) :
    s (E.proj.domRestrict (E.trivialLift hs hP) x) = x := by
  simp only [LinearMap.domRestrict_apply, LieHom.coe_toLinearMap]
  obtain ⟨-, y, hy⟩ := x
  simp only [← hy, LinearMap.domRestrict_apply]
  rw [hs]

lemma range_eq [IsLieAbelian N] (E : Extension R N M) {s : M →ₗ[R] E.L} (hs : LeftInverse E.proj s)
    {P : LieSubalgebra R M} (hP : ∀ (p q : P), (E.twoCocycleOf hs).1 p q = 0) (x : P) :
    s x ∈ E.trivialLift hs hP := by
  simp only [trivialLift, LinearMap.range_domRestrict, Submodule.map_coe, LieSubalgebra.mem_mk_iff',
    Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_image, SetLike.mem_coe,
    LieSubalgebra.mem_toSubmodule]
  use x
  simp

lemma restrict_bijective [IsLieAbelian N] (E : Extension R N M) {s : M →ₗ[R] E.L}
    (hs : LeftInverse E.proj s) {P : LieSubalgebra R M}
    (hP : ∀ (p q : P), (E.twoCocycleOf hs).1 p q = 0) :
    Bijective (s.restrict (fun x hx ↦ E.range_eq hs hP ⟨x, hx⟩)) := by
  constructor
  · intro x y h
    simp only [LinearMap.restrict_apply, Subtype.mk.injEq] at h
    exact SetLike.coe_eq_coe.mp (LeftInverse.injective hs h)
  · intro x
    obtain ⟨y, hy⟩ := x
    simp only [trivialLift, LinearMap.range_domRestrict, Submodule.map_coe, Submodule.mem_mk,
      AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_image, SetLike.mem_coe,
      LieSubalgebra.mem_toSubmodule] at hy
    obtain ⟨z, hz⟩ := hy
    use ⟨z, hz.1⟩
    exact Subtype.coe_eq_of_eq_mk (by simp [hz])

end Lift

end Extension

section Algebra

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
(c : twoCocycle R L M)

/-- The Lie algebra map from a central extension derived from a 2-cocycle. -/
@[simps]
def twoCocycleProj : (ofTwoCocycle c) →ₗ⁅R⁆ L where
  toLinearMap := {
    toFun x := ((ofProd c).symm x).1
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }
  map_lie' {x y} := by simp [bracket_ofTwoCocycle]

lemma surjective_of_cocycle : Surjective (twoCocycleProj c) :=
  fun x ↦ Exists.intro ((ofProd c) (x, 0)) rfl

end Algebra

namespace Extension

section ofTwoCocycle

open LieModule.Cohomology

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M] [IsLieAbelian M]
[LieRingModule L M] [LieModule R L M] (c : twoCocycle R L M)

lemma bracket_ofTwoCocycle (x y : (ofTwoCocycle c).L) :
    ⁅x, y⁆ = ofAlg c ⁅(ofAlg c).symm x, (ofAlg c).symm y⁆ := rfl

end ofTwoCocycle

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

open LieModule.Cohomology

lemma apply_sub_apply_mem_ker (E : Extension R M L) {s₁ s₂ : L →ₗ[R] E.L}
    (hs₁ : LeftInverse E.proj s₁) (hs₂ : LeftInverse E.proj s₂)
    (a : L) :
    (s₁ a) - (s₂ a) ∈ LinearMap.ker E.proj.toLinearMap := by
  rw [LinearMap.mem_ker, LieHom.coe_toLinearMap, map_sub, hs₁, hs₂, sub_eq_zero]

end Extension

end LieAlgebra
