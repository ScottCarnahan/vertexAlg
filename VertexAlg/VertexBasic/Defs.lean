/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import VertexAlg.VertexBasic.VertexOperator

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
 * Various identities: Borcherds, commutator, locality, associativity, skew-symmetry.
 * VertexAlgebra: An `AddCommGroupWithOne` with a `stateField`, satisfying associativity and
   locality.
## Main results
We postpone the proofs of equivalences of various identities to Mathlib.Algebra.Vertex.Basic.
## To do:
* Refactor: Make the `Y` notation easier to use.
* Use formal series more, instead of combinatorial coefficient calculations.
* order of associativity, weak associativity
* Fix weak associativity defs
* cofiniteness conditions?
* Typeclasses for worldsheet symmetry:
  * `Graded`: A class for vertex algebras with a grading that is compatible with a semisimple
  operator `L(0)`, such that translation has degree `-1` and the unit has degree `0`.
  * `Mobius`: A class for vertex algebras with `sl2`-action, extending the grading by a `L(1)`
  operator.
  * `QuasiConformal`: A class for an action of the Lie algebra Der 𝒪.
  * `Conformal`: A class for an internal Virasoro action given by a conformal element.
  * `Gauged`: Affine Lie symmetry?
## References
R. Borcherds `Vertex algebras, Kac-Moody algebras, and the monster` PNAS 1986
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
A. Matsuo, K. Nagatomo `On axioms for a vertex algebra and locality of quantum fields`
arXiv:hep-th/9706118
-/

@[expose] public section

/-- The multiplication in a vertex algebra. -/
abbrev stateField (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  V →ₗ[R] VertexOperator R V

namespace stateField

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
zero otherwise.  In particular, `a [[n]] b = 0` for `n ≥ -order a b`. -/
noncomputable def order (a b : V) : ℤ := HahnSeries.order ((HahnModule.of R).symm (Y a b))

theorem coeff_eq_zero_of_lt_order (a b : V) (n : ℤ) (h : n < Y.order a b) :
    HVertexOperator.coeff (Y a) n b = 0 := by
  rw [order] at h
  simp only [HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact HahnSeries.coeff_eq_zero_of_lt_order h

theorem coeff_ne_zero_at_order (a b : V) (h : Y a b ≠ 0) :
    HVertexOperator.coeff (Y a) (Y.order a b) b ≠ 0 :=
  HahnSeries.coeff_order_eq_zero.not.mpr h

theorem ncoeff_zero_if_neg_order_leq (a b : V) (n : ℤ) (h : -Y.order a b ≤ n) :
    (Y a).ncoeff n b = 0 := by
  rw [ncoeff]
  refine coeff_eq_zero_of_lt_order Y a b (-n-1) ?_
  rw [Int.sub_one_lt_iff, neg_le]
  exact h

theorem ncoeff_ne_zero_at_neg_order_minus_one (a b : V) (h : Y a b ≠ 0) :
    (Y a).ncoeff (-Y.order a b - 1) b ≠ 0 := by
  dsimp [ncoeff]
  rw [neg_sub, sub_neg_eq_add, add_sub_cancel_left]
  exact coeff_ne_zero_at_order Y a b h

-- Reminder: a (t + i) b = 0 for i ≥ -t - (order a b)

/-- The associativity property of vertex algebras. -/
def associativity (a b c : V) (s t : ℤ) : Prop :=
  ncoeff (Y (ncoeff (Y a) t b)) s c = Finset.sum (Finset.range
    (Int.toNat (-s - order Y b c))) (fun i ↦ (-1)^i • (Ring.choose (t : ℤ)  i) •
    (ncoeff (Y a) (t-i) (ncoeff (Y b) (s+i) c))) + Finset.sum (Finset.range (Int.toNat
    (- order Y a c))) (fun i ↦ (t+i+1).negOnePow • (Ring.choose t i) • ncoeff (Y b) (s+t-i)
    (ncoeff (Y a) i c))

/-- The commutator formula for vertex algebras. -/
def commutatorFormula (a b c : V) (r s : ℤ) : Prop :=
  ncoeff (Y a) r (ncoeff (Y b) s c) - ncoeff (Y b) s (ncoeff (Y a) r c) =
  Finset.sum (Finset.range (Int.toNat (- order Y a b))) (fun i ↦ (Ring.choose r i) •
  ncoeff (Y (ncoeff (Y a) i b)) (r+s-i) c)

/-!
/-- The locality property, asserting that `(x-y)^N Y(a,x)Y(b,y) = (x-y)^N Y(b,y)Y(a,x)` for
sufficiently large `N`.  That is, the vertex operators commute up to finite order poles on the
diagonal. -/
def IsLocal (a b : V) : Prop :=
  ∃ n, IsLocalToOrderLeq (Y a) (Y b) n
-- was borcherdsSum2 R a b c r s t + borcherdsSum3 R a b c r s t = 0
-- weak associativity needs to be changed to the vertex operator definition.
-/

section Unital

open HVertexOperator VertexOperator

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroupWithOne V] [Module R V]

/-- A divided-power system of translation operators.  `T 1` is often written `T`. -/
def T (Y : stateField R V) (n : ℕ) : Module.End R V where
  toFun := fun (x : V) => HVertexOperator.coeff (Y x) n 1
  map_add' := by intros; simp only [coeff_add_left_eq]
  map_smul' := by intros; simp only [coeff_smul_left_eq, RingHom.id_apply]

/-- The skew-symmetry property for vertex algebras: `Y(u,z)v = exp(Tz)Y(v,-z)u`. -/
def skewSymmetry (Y : stateField R V) (a b : V) (n : ℤ) : Prop :=
  ncoeff (Y b) n a = Finset.sum (Finset.range (Int.toNat (-n - order Y a b)))
    (fun i ↦ (n + i + 1).negOnePow • T Y i (ncoeff (Y a) (n+i) b))

/-- A field is translation covariant with respect to a divided-power system of endomorphisms that
stabilizes identity if left translation satisfies the Leibniz rule.  We omit conditions on `f`. -/
def translationCovariance (Y : stateField R V) (A : VertexOperator R V) (f : ℕ → Module.End R V) :
    Prop :=
  ∀ (i : ℕ) (n : ℤ), f i * HVertexOperator.coeff A n =
    Finset.sum (Finset.HasAntidiagonal.antidiagonal i) fun m => (Int.negOnePow m.fst) •
      Ring.choose n m.fst • (HVertexOperator.coeff A (n - m.fst) * T Y m.snd)
-- This is clearly wrong. Why does `Y` not appear on the left side???

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
class VertexAlgebra (R V : Type*) [CommRing R] [AddCommGroupWithOne V] extends Module R V where
  /-- The multiplication operation. -/
  Y : stateField R V
  /-- Any pair of fields are mutually local. -/
  IsLocal a b : ∃ n, (Y a).IsLocalToOrderLeq (Y b) n
  /-- Passing to residue products is a homomorphism. -/
  ResProdHom (a : V) (b : V) (n : ℤ) : resProd n (Y a) (Y b) = Y (((Y a)[[n]]) b)
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), order Y a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), ((Y a)[[-1]]) 1 = a

lemma apply_nat_unit {R V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (v : V)
    {k : ℤ} (hk : 0 ≤ k) :
    ((VertexAlgebra.Y (R := R) v)[[k]]) (1 : V) = 0 :=
  ncoeff_zero_if_neg_order_leq VertexAlgebra.Y v 1 k
    (by simp [VertexAlgebra.unit_comm (R := R) v, hk])

open VertexAlgebra in
/-- A homomorphism of vertex algebras is a linear map that preserves the unit and products. -/
structure VertexAlgebraHom (R V W : Type*) [CommRing R] [AddCommGroupWithOne V]
    [AddCommGroupWithOne W] [VertexAlgebra R V] [VertexAlgebra R W] where
  /-- The underlying linear map. -/
  toLinearMap : V →ₗ[R] W
  /-- Vertex algebra homomorphisms preserve units -/
  mapOne : Prop := toLinearMap 1 = 1
  /-- Vertex algebra homomorphisms preserve the vertex products. -/
  IsVertexHom (n : ℤ) (x y : V) : Prop :=
    toLinearMap ((Y (R := R) x).ncoeff n y) = (Y (R := R) (toLinearMap x)).ncoeff n (toLinearMap y)

/-- The Poisson kernel of a vertex algebra, which typically appears in the literature as the
subspace `C₂(V)`. -/
def poissonKernel (R V : Type*) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] :
    Submodule R V :=
  Submodule.span R
    {w : V | ∃ (u v : V) (n : ℤ), n ≤ -2 ∧ (VertexAlgebra.Y (R := R) u).ncoeff n v = w}

/-
/-- The `Subgroup` generated by a set. -/
@[to_additive /-- The `AddSubgroup` generated by a set -/]
def closure (k : Set G) : Subgroup G :=
  sInf { K | k ⊆ K }

variable {k : Set G}

@[to_additive]
theorem mem_closure {x : G} : x ∈ closure k ↔ ∀ K : Subgroup G, k ⊆ K → x ∈ K :=
  mem_sInf

/-- The subgroup generated by a set includes the set. -/
@[to_additive (attr := simp, aesop safe 20 (rule_sets := [SetLike]))
  /-- The `AddSubgroup` generated by a set includes the set. -/]
theorem subset_closure : k ⊆ closure k := fun _ hx => mem_closure.2 fun _ hK => hK hx

@[to_additive (attr := aesop 80% (rule_sets := [SetLike]))]
theorem mem_closure_of_mem {s : Set G} {x : G} (hx : x ∈ s) : x ∈ closure s := subset_closure hx

@[to_additive]
theorem notMem_of_notMem_closure {P : G} (hP : P ∉ closure k) : P ∉ k := fun h =>
  hP (subset_closure h)

open Set

/-- A subgroup `K` includes `closure k` if and only if it includes `k`. -/
@[to_additive (attr := simp)
  /-- An additive subgroup `K` includes `closure k` if and only if it includes `k` -/]
theorem closure_le : closure k ≤ K ↔ k ⊆ K :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩

@[to_additive]
theorem closure_eq_of_le (h₁ : k ⊆ K) (h₂ : K ≤ closure k) : closure k = K :=
  le_antisymm ((closure_le <| K).2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `k`, and
is preserved under multiplication and inverse, then `p` holds for all elements of the closure
of `k`.

See also `Subgroup.closure_induction_left` and `Subgroup.closure_induction_right` for versions that
only require showing `p` is preserved by multiplication by elements in `k`. -/
@[to_additive (attr := elab_as_elim)
      /-- An induction principle for additive closure membership. If `p`
      holds for `0` and all elements of `k`, and is preserved under addition and inverses, then `p`
      holds for all elements of the additive closure of `k`.

      See also `AddSubgroup.closure_induction_left` and `AddSubgroup.closure_induction_left` for
      versions that only require showing `p` is preserved by addition by elements in `k`. -/]
theorem closure_induction {p : (g : G) → g ∈ closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ closure k) : p x hx :=
  let K : Subgroup G :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, ha⟩ ⟨_, hb⟩ ↦ ⟨_, mul _ _ _ _ ha hb⟩
      one_mem' := ⟨_, one⟩
      inv_mem' := fun ⟨_, hb⟩ ↦ ⟨_, inv _ _ hb⟩ }
  closure_le (K := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

-/

/-- A submodule is a vertex subalgebra if it contains the identity and is closed under all
products. -/
structure VertexSubalgebra (R : Type u) (V : Type v) [CommRing R] [AddCommGroupWithOne V]
    [VertexAlgebra R V] : Type v extends Submodule R V where
  one_mem' : 1 ∈ carrier
  mul_mem' {a b : V} (ha : a ∈ carrier) (hb : b ∈ carrier) (n : ℤ) :
      (VertexAlgebra.Y (R := R) a).ncoeff n b ∈ carrier

/-- Reinterpret a `VertexSubalgebra` as a `Submodule`. -/
add_decl_doc VertexSubalgebra.toSubmodule

namespace VertexSubalgebra

variable (R : Type u) (V : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]

instance : SetLike (VertexSubalgebra R V) V where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

instance : PartialOrder (VertexSubalgebra R V) :=
  .ofSetLike (VertexSubalgebra R V) V

initialize_simps_projections VertexSubalgebra (carrier → coe, as_prefix coe)

@[simp]
theorem coe_mk (s : Submodule R V) (h1) (hm) :
    (VertexSubalgebra.mk (R := R) s h1 hm : Set V) = s :=
  rfl

@[simp]
theorem mem_mk (s : Submodule R V) (h1) (hm) (x) :
    x ∈ VertexSubalgebra.mk (R := R) s h1 hm ↔ x ∈ s :=
  .rfl
/-
instance : Bot (VertexSubalgebra R V) :=
  ⟨⟨Submodule.span R {(1 : V)}, by simp, fun {a b} ha hb n ↦ by
    rw [Submodule.carrier_eq_coe, SetLike.mem_coe, Submodule.mem_span_singleton] at ha hb
    obtain ⟨r, hr⟩ := ha
    obtain ⟨s, hs⟩ := hb
    rw [← hr, ← hs]
    simp only [Submodule.carrier_eq_coe, map_smul, Pi.smul_apply, LinearMap.smul_apply,
      SetLike.mem_coe, smul_smul]
    by_cases h : n = -1
    · simp [h, VertexAlgebra.unit_right, Submodule.mem_span_singleton]
    · sorry
    ⟩⟩

instance : Inhabited (Subsemiring R) :=
  ⟨⊥⟩

@[norm_cast]
theorem coe_bot : ((⊥ : Subsemiring R) : Set R) = Set.range ((↑) : ℕ → R) :=
  (Nat.castRingHom R).coe_rangeS

theorem mem_bot {x : R} : x ∈ (⊥ : Subsemiring R) ↔ ∃ n : ℕ, ↑n = x :=
  RingHom.mem_rangeS

instance : InfSet (Subsemiring R) :=
  ⟨fun s =>
    Subsemiring.mk' (⋂ t ∈ s, ↑t) (⨅ t ∈ s, Subsemiring.toSubmonoid t) (by simp)
      (⨅ t ∈ s, Subsemiring.toAddSubmonoid t)
      (by simp)⟩

@[simp, norm_cast]
theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
theorem mem_sInf {S : Set (Subsemiring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂


def closure (R : Type u) (V : Type v) [CommRing R] [AddCommGroupWithOne V]
    [VertexAlgebra R V] (k : Set V) : VertexSubalgebra R V := sInf {U | k ⊆ U}

def ofGeneratingSet (R V : Type*) [CommRing R] [AddCommGroupWithOne V] [Module R V] {s : Set V}
    (hs : V = Submodule.span {w : V | ∃ })
-/

end VertexSubalgebra

/-- A morphism of vertex algebras (denoted as `U →ₗ[[R]] V`)
is a linear map respecting the unit and product operations. -/
structure VertexHom (R U V : Type*) [CommRing R] [AddCommGroupWithOne U] [VertexAlgebra R U]
    [AddCommGroupWithOne V] [VertexAlgebra R V]
  extends U →ₗ[R] V where
  /-- A morphism of Vertex algebras is compatible with brackets. -/
  map_vertex' : ∀ {a b : U} {n : ℤ}, toFun ((VertexAlgebra.Y (R := R) a).ncoeff n b) =
    (VertexAlgebra.Y (R := R) (toFun a)).ncoeff n (toFun b)

@[inherit_doc]
notation:25 U " →ₗ[[" R:25 "]] " V:0 => VertexHom R U V

namespace VertexHom

variable {R : Type u} {U : Type v} {V : Type w} {W : Type w₁}
variable [CommRing R]
variable [AddCommGroupWithOne U] [VertexAlgebra R U]
variable [AddCommGroupWithOne V] [VertexAlgebra R V]
variable [AddCommGroupWithOne W] [VertexAlgebra R W]

attribute [coe] VertexHom.toLinearMap

instance : Coe (U →ₗ[[R]] V) (U →ₗ[R] V) :=
  ⟨VertexHom.toLinearMap⟩

instance : FunLike (U →ₗ[[R]] V) U V where
  coe f := f.toFun
  coe_injective x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections VertexHom (toFun → apply)

@[simp, norm_cast]
theorem coe_toLinearMap (f : U →ₗ[[R]] V) : ⇑(f : U →ₗ[R] V) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : U →ₗ[[R]] V) : f.toFun = ⇑f :=
  rfl

instance : LinearMapClass (U →ₗ[[R]] V) R U V where
  map_add _ _ _ := by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, MulActionSemiHomClass.map_smulₛₗ]

@[simp]
theorem map_vertex (f : U →ₗ[[R]] V) (a b : U) (n : ℤ) :
    f ((VertexAlgebra.Y (R := R) a).ncoeff n b) =
      (VertexAlgebra.Y (R := R) (f a)).ncoeff n (f b) :=
  VertexHom.map_vertex' f

/-- The identity map is a morphism of vertex algebras. -/
def id : U →ₗ[[R]] U :=
  { (LinearMap.id : U →ₗ[R] U) with map_vertex' := rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(id : U →ₗ[[R]] U) = _root_.id :=
  rfl

theorem id_apply (x : U) : (id : U →ₗ[[R]] U) x = x :=
  rfl

/-- The constant 0 map is a vertex algebra morphism. -/
instance : Zero (U →ₗ[[R]] V) :=
  ⟨{ (0 : U →ₗ[R] V) with map_vertex' := by simp }⟩

@[norm_cast, simp]
theorem coe_zero : ((0 : U →ₗ[[R]] V) : U → V) = 0 :=
  rfl

theorem zero_apply (x : U) : (0 : U →ₗ[[R]] V) x = 0 :=
  rfl

/-- The identity map is a Vertex algebra morphism. -/
instance : One (U →ₗ[[R]] U) :=
  ⟨id⟩

@[simp]
theorem coe_one : ((1 : U →ₗ[[R]] U) : U → U) = _root_.id :=
  rfl

theorem one_apply (x : U) : (1 : U →ₗ[[R]] U) x = x :=
  rfl

instance : Inhabited (U →ₗ[[R]] V) :=
  ⟨0⟩

theorem coe_injective : @Function.Injective (U →ₗ[[R]] V) (U → V) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]
theorem ext {f g : U →ₗ[[R]] V} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

theorem congr_fun {f g : U →ₗ[[R]] V} (h : f = g) (x : U) : f x = g x :=
  h ▸ rfl

@[simp]
theorem mk_coe (f : U →ₗ[[R]] V) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : U →ₗ[[R]] V) = f := by
  ext
  rfl

@[simp]
theorem coe_mk (f : U → V) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : U →ₗ[[R]] V) : U → V) = f :=
  rfl

/-- The composition of morphisms is a morphism. -/
def comp (f : V →ₗ[[R]] W) (g : U →ₗ[[R]] V) : U →ₗ[[R]] W :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_vertex' := by simp }

theorem comp_apply (f : V →ₗ[[R]] W) (g : U →ₗ[[R]] V) (x : U) : f.comp g x = f (g x) :=
  rfl

@[norm_cast, simp]
theorem coe_comp (f : V →ₗ[[R]] W) (g : U →ₗ[[R]] V) : (f.comp g : U → W) = f ∘ g :=
  rfl

@[norm_cast, simp]
theorem toLinearMap_comp (f : V →ₗ[[R]] W) (g : U →ₗ[[R]] V) :
    (f.comp g : U →ₗ[R] W) = (f : V →ₗ[R] W).comp (g : U →ₗ[R] V) :=
  rfl

@[simp]
theorem comp_id (f : U →ₗ[[R]] V) : f.comp (id : U →ₗ[[R]] U) = f :=
  rfl

@[simp]
theorem id_comp (f : U →ₗ[[R]] V) : (id : V →ₗ[[R]] V).comp f = f :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : U →ₗ[[R]] V) (g : V → U) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : V →ₗ[[R]] U :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_vertex' := by
      intro x y n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      nth_rw 1 [← h₂ x, ← h₂ y]
      rw [← map_vertex]
      apply h₁ }

end VertexHom

/-- An equivalence of vertex algebras (denoted as `U ≃ₗ[[R]] V`) is a morphism
which is also a linear equivalence.
We could instead define an equivalence to be a morphism which is also a (plain) equivalence.
However, it is more convenient to define via linear equivalence to get `.toLinearEquiv` for free. -/
structure VertexEquiv (R : Type u) (U : Type v) (V : Type w) [CommRing R] [AddCommGroupWithOne U]
    [VertexAlgebra R U] [AddCommGroupWithOne V] [VertexAlgebra R V] extends U →ₗ[[R]] V where
  /-- The inverse function of an equivalence of Vertex algebras -/
  invFun : V → U
  /-- The inverse function of an equivalence of Vertex algebras is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toVertexHom.toFun := by intro; first | rfl | ext <;> rfl
  /-- The inverse function of an equivalence of Vertex algebras is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toVertexHom.toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
notation:50 U " ≃ₗ[[" R "]] " V => VertexEquiv R U V

namespace VertexEquiv

variable {R : Type u} {U : Type v} {V : Type w} {L₃ : Type w₁}
variable [CommRing R] [AddCommGroupWithOne U] [AddCommGroupWithOne V] [AddCommGroupWithOne W]
  [VertexAlgebra R U] [VertexAlgebra R V] [VertexAlgebra R W]

/-- Consider an equivalence of Vertex algebras as a linear equivalence. -/
def toLinearEquiv (f : U ≃ₗ[[R]] V) : U ≃ₗ[R] V :=
  { f.toVertexHom, f with }

instance hasCoeToVertexHom : Coe (U ≃ₗ[[R]] V) (U →ₗ[[R]] V) :=
  ⟨toVertexHom⟩

instance hasCoeToLinearEquiv : Coe (U ≃ₗ[[R]] V) (U ≃ₗ[R] V) :=
  ⟨toLinearEquiv⟩

instance : EquivLike (U ≃ₗ[[R]] V) U V where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

theorem coe_toVertexHom (e : U ≃ₗ[[R]] V) : ⇑(e : U →ₗ[[R]] V) = e :=
  rfl

@[simp]
theorem coe_toLinearEquiv (e : U ≃ₗ[[R]] V) : ⇑(e : U ≃ₗ[R] V) = e :=
  rfl

@[simp] theorem coe_coe (e : U ≃ₗ[[R]] V) : ⇑e.toVertexHom = e := rfl

@[simp]
theorem toLinearEquiv_mk (f : U →ₗ[[R]] V) (g h₁ h₂) :
    (mk f g h₁ h₂ : U ≃ₗ[R] V) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl

theorem toLinearEquiv_injective : Function.Injective ((↑) : (U ≃ₗ[[R]] V) → U ≃ₗ[R] V) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

theorem coe_injective : @Function.Injective (U ≃ₗ[[R]] V) (U → V) (↑) :=
  LinearEquiv.coe_injective.comp toLinearEquiv_injective

instance : LinearEquivClass (U ≃ₗ[[R]] V) R U V where
  map_add _ _ _ := by
    rw [← coe_toLinearEquiv, map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv, map_smul, RingHom.id_apply]

@[ext]
theorem ext {f g : U ≃ₗ[[R]] V} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

instance : One (U ≃ₗ[[R]] U) :=
  ⟨{ (1 : U ≃ₗ[R] U) with map_vertex' := rfl }⟩

@[simp]
theorem one_apply (x : U) : (1 : U ≃ₗ[[R]] U) x = x :=
  rfl

instance : Inhabited (U ≃ₗ[[R]] U) :=
  ⟨1⟩

lemma map_vertex (e : U ≃ₗ[[R]] V) (x y : U) (n : ℤ) :
    e ((VertexAlgebra.Y (R := R) x).ncoeff n y) =
      ((VertexAlgebra.Y (R := R) (e x)).ncoeff n (e y)) :=
  VertexHom.map_vertex e.toVertexHom x y n

/-- Vertex algebra equivalences are reflexive. -/
def refl : U ≃ₗ[[R]] U :=
  1

@[simp]
theorem refl_apply (x : U) : (refl : U ≃ₗ[[R]] U) x = x :=
  rfl

/-- Vertex algebra equivalences are symmetric. -/
@[symm]
def symm (e : U ≃ₗ[[R]] V) : V ≃ₗ[[R]] U :=
  { VertexHom.inverse e.toVertexHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]
theorem symm_symm (e : U ≃ₗ[[R]] V) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (VertexEquiv.symm : (U ≃ₗ[[R]] V) → V ≃ₗ[[R]] U) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem apply_symm_apply (e : U ≃ₗ[[R]] V) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : U ≃ₗ[[R]] V) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply

theorem symm_apply_eq (e : U ≃ₗ[[R]] V) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : U ≃ₗ[[R]] V) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

@[simp]
theorem refl_symm : (refl : U ≃ₗ[[R]] U).symm = refl :=
  rfl

/-- Vertex algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : U ≃ₗ[[R]] V) (e₂ : V ≃ₗ[[R]] W) : U ≃ₗ[[R]] W :=
  { VertexHom.comp e₂.toVertexHom e₁.toVertexHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
theorem self_trans_symm (e : U ≃ₗ[[R]] V) : e.trans e.symm = refl :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : U ≃ₗ[[R]] V) : e.symm.trans e = refl :=
  e.symm.self_trans_symm

@[simp]
theorem trans_apply (e₁ : U ≃ₗ[[R]] V) (e₂ : V ≃ₗ[[R]] W) (x : U) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem symm_trans (e₁ : U ≃ₗ[[R]] V) (e₂ : V ≃ₗ[[R]] W) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

protected theorem bijective (e : U ≃ₗ[[R]] V) : Function.Bijective ((e : U →ₗ[[R]] V) : U → V) :=
  e.toLinearEquiv.bijective

protected theorem injective (e : U ≃ₗ[[R]] V) : Function.Injective ((e : U →ₗ[[R]] V) : U → V) :=
  e.toLinearEquiv.injective

protected theorem surjective (e : U ≃ₗ[[R]] V) :
    Function.Surjective ((e : U →ₗ[[R]] V) : U → V) :=
  e.toLinearEquiv.surjective

/-- A bijective morphism of vertex algebras yields an equivalence of vertex algebras. -/
@[simps!]
noncomputable def ofBijective (f : U →ₗ[[R]] V) (h : Function.Bijective f) : U ≃ₗ[[R]] V :=
  { LinearEquiv.ofBijective (f : U →ₗ[R] V)
      h with
    toFun := f
    map_vertex' := by intro x y n; exact f.map_vertex x y n }

end VertexEquiv

end VertexAlgebra
