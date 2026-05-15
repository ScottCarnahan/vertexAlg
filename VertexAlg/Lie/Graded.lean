/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Graded

/-!
Add to `Mathlib.Algebra.Lie.Graded`
-/

@[expose] public section

open DirectSum

variable {ι σ R L : Type*}


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
