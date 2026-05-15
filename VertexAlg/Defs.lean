/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import VertexAlg.VertexOperator

/-!
# Vertex algebras
In this file we introduce a non-unital non-associative vertex algebra over a commutative ring `R` as
an `R`-module `V` with a left-multiplication operation `Y` to vertex operators in `V` over `R`.  We
may view `Y` as a bilinear map `V × V → V((z))`, or as a family of non-associative products
parametrized by `ℤ`.  The unit element is introduced with the `AddCommGroupWithOne` type, and the
Borcherds identity that defines vertex algebras is introduced in pieces for easier manipulation.
## Definitions
 * `VertexAlg.stateField` : This is the left-multiplication structure in a vertex algebra, sometimes
   called a state-field correspondence. It is fundamentally a linear map `V →ₗ[R] V →ₗ[R] V((z))`.
 * Borcherds identity sums: These are composites of vertex operators multiplied by binomial powers.
 * Various identities: Borcherds, commutator, locality, associativity, skew-symmetry.
 * VertexAlgebra: An `AddCommGroupWithOne` with a `stateField`, satisfying associativity and
   locality.
## Main results
We postpone the proofs of equivalences of various identities to Mathlib.Algebra.Vertex.Basic.
## To do:
* Refactor: remove non-unital non-associative vertex algebra.  Introduce Y by itself.
* Use formal series more, instead of combinatorial coefficient calculations.
* order of associativity, weak associativity
* Fix weak associativity defs
* cofiniteness conditions?
* Typeclasses for worldsheet symmetry:
  * `Graded`: A class for vertex algebras with a grading that is compatible with a semisimple
  operator `L(0)`, such that translation has degree `-1` and the unit has degree `0`.
  * `Mobius`: A class for vertex algebras with `sl2`-action, extending the grading by a `L(1)`
  operator.
  * `QuasiConformal`: A class for an action of Der 𝒪.
  * `Conformal`: A class for an internal Virasoro action given by a conformal element.
  * `Gauged` ??
## References
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118
-/

@[expose] public section

/-- The multiplication in a vertex algebra. -/
abbrev stateField (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  V →ₗ[R] VertexOperator R V

namespace stateField

/-! A non-associative non-unital vertex algebra over a commutative ring `R` is an `R`-module `V`
with a multiplication that takes values in Laurent series with coefficients in `V`.
class NonAssocNonUnitalVertexAlgebra (R : Type*) (V : Type*) [CommRing R] [AddCommGroup V] extends
    Module R V where
  /-- The multiplication operation in a vertex algebra. -/
  Y: V →ₗ[R] VertexOperator R V
-/
open HVertexOperator VertexOperator

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (Y : stateField R V)

--scoped[VertexAlg] notation a "[[" n "]]" => ncoeff (Y a) n

theorem Y_coeff_add_left_eq (Y : stateField R V) (a b : V) (n : ℤ) :
    HVertexOperator.coeff (Y a + Y b) n =
      HVertexOperator.coeff (Y a) n + HVertexOperator.coeff (R := R) (Y b) n := by
  exact rfl

theorem Y_ncoeff_add_left_eq (a b : V) (n : ℤ) :
    ncoeff (Y a + Y b) n = ncoeff (Y a) n + ncoeff (R := R) (Y b) n := by
  exact rfl

theorem Y_coeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    HVertexOperator.coeff (Y (r • a)) n = r • HVertexOperator.coeff (R := R) (Y a) n := by
  simp only [map_smul]
  exact rfl

theorem Y_ncoeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    ncoeff (Y (r • a)) n = r • ncoeff (R := R) (Y a) n := by
  simp only [map_smul]
  exact rfl

theorem coeff_add_left_eq (a b c : V) (n : ℤ) :
    HVertexOperator.coeff (Y (a + b)) n c =
      HVertexOperator.coeff (Y a) n c + HVertexOperator.coeff (R := R) (Y b) n c := by
  rw [map_add, Y_coeff_add_left_eq, LinearMap.add_apply]

theorem ncoeff_add_left_eq (a b c : V) (n : ℤ) :
    ncoeff (Y (a + b)) n c = ncoeff (Y a) n c + ncoeff (Y b) n c := by
  rw [map_add, Y_ncoeff_add_left_eq, LinearMap.add_apply]

theorem coeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    HVertexOperator.coeff (Y (r • a)) n b = r • HVertexOperator.coeff (Y a) n b := by
  rw [Y_coeff_smul_left_eq, LinearMap.smul_apply]

theorem ncoeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    ncoeff (Y (r • a)) n b = r • ncoeff (Y a) n b := by
  rw [Y_ncoeff_smul_left_eq, LinearMap.smul_apply]

/-- The order is the smallest integer `n` such that `a [[-n-1]] b ≠ 0` if `Y a b` is nonzero, and
zero otherwise.  In particular, `a ⁅n⁆ b = 0` for `n ≥ -order a b`. -/
noncomputable def order (a b : V) : ℤ := HahnSeries.order ((HahnModule.of R).symm (Y a b))

theorem coeff_zero_if_lt_order (a b : V) (n : ℤ) (h : n < order Y a b) :
    HVertexOperator.coeff (Y a) n b = 0 := by
  rw [order] at h
  simp only [HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_nonzero_at_order (a b : V) (h : Y a b ≠ 0) :
    HVertexOperator.coeff (Y a) (order Y a b) b ≠ 0 :=
  HahnSeries.coeff_order_eq_zero.not.mpr h

theorem ncoeff_zero_if_neg_order_leq (a b : V) (n : ℤ) (h : -order Y a b ≤ n) :
    ncoeff (Y a) n b = 0 := by
  rw [ncoeff]
  refine coeff_zero_if_lt_order Y a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem ncoeff_nonzero_at_neg_order_minus_one (a b : V) (h : Y a b ≠ 0) :
    ncoeff (Y a) (-order Y a b - 1) b ≠ 0 := by
  dsimp [ncoeff]
  rw [neg_sub, sub_neg_eq_add, add_sub_cancel_left]
  exact coeff_nonzero_at_order Y a b h

-- Reminder: a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The first sum in the Borcherds identity, giving the `x^t z^s` coefficient of
`x^r (1 + z/x)^r (a(x)b)(z)c`. -/
noncomputable def Borcherds_sum_1 (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-t - order Y a b)))
    (fun i ↦ (Ring.choose r i) • ncoeff (Y (ncoeff (Y a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`y^t (1 - z/y)^t a(y)b(z)c`. -/
noncomputable def Borcherds_sum_2 (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order Y b c)))
    (fun i ↦ (-1)^i • (Ring.choose t i) • ncoeff (Y a) (r+t-i)
    (ncoeff (Y b) (s+i) c))

/-- The third sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`-(-y)^t (1 - y/z)^t b(z)a(y)c`. -/
noncomputable def Borcherds_sum_3 (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order Y a c)))
    (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • ncoeff (Y b) (s+t-i)
    (ncoeff (Y a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable def Borcherds_id (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 Y a b c r s t = Borcherds_sum_2 Y a b c r s t + Borcherds_sum_3 Y a b c r s t

/-- The associativity property of vertex algebras. -/
def associativity (a b c : V) (s t : ℤ) : Prop :=
  ncoeff (Y (ncoeff (Y a) t b)) s c = Finset.sum (Finset.range
    (Int.toNat (-s - order Y b c))) (fun i ↦ (-1)^i • (Ring.choose (t : ℤ)  i) •
    (ncoeff (Y a) (t-i) (ncoeff (Y b) (s+i) c))) + Finset.sum (Finset.range (Int.toNat
    (- order Y a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) • (Ring.choose t i) • ncoeff (Y b) (s+t-i)
    (ncoeff (Y a) i c))

/-- The commutator formula for vertex algebras. -/
def commutator_formula (a b c : V) (r s : ℤ) : Prop :=
  ncoeff (Y a) r (ncoeff (Y b) s c) - ncoeff (Y b) s (ncoeff (Y a) r c) =
  Finset.sum (Finset.range (Int.toNat (- order Y a b))) (fun i ↦ (Ring.choose r i) •
  ncoeff (Y (ncoeff (Y a) i b)) (r+s-i) c)

/-!
/-- The locality property, asserting that `(x-y)^N Y(a,x)Y(b,y) = (x-y)^N Y(b,y)Y(a,x)` for
sufficiently large `N`.  That is, the vertex operators commute up to finite order poles on the
diagonal. -/
def IsLocal (a b : V) : Prop :=
  ∃ n, IsLocalToOrderLeq (Y a) (Y b) n
-- was Borcherds_sum_2 R a b c r s t + Borcherds_sum_3 R a b c r s t = 0
-- weak associativity needs to be changed to the vertex operator definition.
-/
/-- The weak associativity property for vertex algebras. -/
def weak_associativity (a b c : V) (r s t : ℤ) : Prop :=
  Borcherds_sum_1 Y a b c r s t = Borcherds_sum_2 Y a b c r s t

section Unital

open HVertexOperator VertexOperator

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroupWithOne V] [Module R V]

/-- A field is creative with respect to the unit vector `1` if evaluating at `1` yields a regular
series. -/
def IsCreative (A : VertexOperator R V) : Prop :=
  0 ≤ HahnSeries.order (A 1)

/-- The state attached to a creative field is its `z^0`-coefficient at `1`. We omit the creative
hypothesis. -/
def state (A : VertexOperator R V) : V :=
  HVertexOperator.coeff A 0 1

/-- A divided-power system of translation operators.  `T 1` is often written `T`. -/
def T (Y : stateField R V) (n : ℕ) : Module.End R V where
  toFun := fun (x : V) => HVertexOperator.coeff (Y x) n 1
  map_add' := by intros; simp only [coeff_add_left_eq]
  map_smul' := by intros; simp only [coeff_smul_left_eq, RingHom.id_apply]

/-- The skew-symmetry property for vertex algebras: `Y(u,z)v = exp(Tz)Y(v,-z)u`. -/
def skew_symmetry (Y : stateField R V) (a b : V) (n : ℤ) : Prop :=
  ncoeff (Y b) n a = Finset.sum (Finset.range (Int.toNat (-n - order Y a b)))
    (fun i ↦ (-1:ℤˣ)^(n + i + 1) • T Y i (ncoeff (Y a) (n+i) b))

/-- A field is translation covariant with respect to a divided-power system of endomorphisms that
stabilizes identity if left translation satisfies the Leibniz rule.  We omit conditions on `f`. -/
def translation_covariance (Y : stateField R V) (A : VertexOperator R V) (f : ℕ → Module.End R V) :
    Prop :=
  ∀ (i : ℕ) (n : ℤ), f i * HVertexOperator.coeff A n =
    Finset.sum (Finset.antidiagonal i) fun m => (-1 : ℤˣ) ^ m.fst • Ring.choose n m.fst •
      (HVertexOperator.coeff A (n - m.fst) * T Y m.snd)

end Unital

end stateField

section VertexAlgebra

/-* There are multiple definitions of vertex algebra in the literature. I have experimented with the
following two. It seems that manipulating Borcherds's identity is a major pain. A well-known fact is
that with the other axioms, Borcherds's identity is equivalent to a combination of one of
`{skew-symmetry, the commutator formula, locality}` and one of
`{associativity formula, weak associativity, ResProdHom}`.

-/
open HVertexOperator VertexOperator stateField

/-- A vertex algebra over a commutative ring `R` is an `R`-module `V` with a distinguished unit
element `1`, together with a multiplication operation that takes values in Laurent series with
coefficients in `V`, such that `a(z) 1 ∈ a + zV[[z]]` for all `a ∈ V` -/
class VertexAlgebra1 (R V : Type*) [CommRing R] [AddCommGroupWithOne V] extends Module R V where
  /-- The multiplication operation. -/
  Y : stateField R V
  /-- The Borcherds identity holds. -/
  Borcherds_id : ∀ (a b c : V) (r s t : ℤ), Borcherds_id Y a b c r s t
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), order Y a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), coeff (Y a) 0 1 = a

/-- A vertex algebra over a commutative ring `R` is an `R`-module `V` with a distinguished unit
element `1`, together with a multiplication operation that takes values in Laurent series with
coefficients in `V`, such that `a(z) 1 ∈ a + zV[[z]]` for all `a ∈ V` -/
class VertexAlgebra2 (R V : Type*) [CommRing R] [AddCommGroupWithOne V] extends Module R V where
  /-- The multiplication operation. -/
  Y : stateField R V
  /-- Any pair of fields are mutually local. -/
  IsLocal a b : ∃ n, (Y a).IsLocalToOrderLeq (Y b) n
  /-- Passing to residue products is a homomorphism. -/
  ResProdHom (a : V) (b : V) n : resProd n (Y a) (Y b) = Y (((Y a)[[n]]) b)
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), order Y a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), coeff (Y a) 0 1 = a

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra1 R V]

theorem Borcherds_identity (a b c : V) (r s t : ℤ) :
    Borcherds_id VertexAlgebra1.Y (R := R) a b c r s t :=
  VertexAlgebra1.Borcherds_id a b c r s t

theorem unit_comm (a : V) : order VertexAlgebra1.Y (R := R) a 1 = 0 := VertexAlgebra1.unit_comm a

theorem unit_right (a : V) : HVertexOperator.coeff (R := R) (VertexAlgebra1.Y a) 0 1 = a :=
  VertexAlgebra1.unit_right a

-- homs? cofiniteness?

end VertexAlgebra
