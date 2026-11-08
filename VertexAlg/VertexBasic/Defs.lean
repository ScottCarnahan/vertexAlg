/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import VertexAlg.VertexBasic.StateField

/-!
# Vertex algebras
In this file we introduce a non-unital non-associative vertex algebra over a commutative ring `R` as
an `R`-module `V` with a left-multiplication operation `Y` to vertex operators in `V` over `R`.  We
may view `Y` as a bilinear map `V × V → V((z))`, or as a family of non-associative products
parametrized by `ℤ`.  The unit element is introduced with the `AddCommGroupWithOne` type, and the
Borcherds identity that defines vertex algebras is introduced in pieces for easier manipulation.
## Definitions
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
  /-- Residue products take vertex operators to vertex operators. -/
  ResProdHom (a : V) (b : V) (n : ℤ) : resProd n (Y a) (Y b) = Y (((Y a)[[n]]) b)
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), order Y a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), ((Y a)[[-1]]) 1 = a

namespace VertexAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]

lemma apply_nat_unit (v : V) {k : ℤ} (hk : 0 ≤ k) :
    ((VertexAlgebra.Y (R := R) v)[[k]]) (1 : V) = 0 :=
  ncoeff_zero_if_neg_order_leq VertexAlgebra.Y v 1 k
    (by simp [VertexAlgebra.unit_comm (R := R) v, hk])

/-- The associativity formula -/
lemma apply_apply (a b c : V) (m n : ℤ) :
  (VertexAlgebra.Y (R := R) (((VertexAlgebra.Y (R := R) a)[[m]]) b)[[n]]) c =
    ∑ᶠ i : ℕ, Int.negOnePow i • (Ring.choose m i) •
    (((VertexAlgebra.Y (R := R) a)[[m - i]]) (((VertexAlgebra.Y (R := R) b)[[n + i]]) c) -
    Int.negOnePow m • (((VertexAlgebra.Y (R := R) b)[[m + n - i]])
      (((VertexAlgebra.Y (R := R) a)[[i]]) c))) := by
  rw [← ResProdHom]
  simp only [resProd_apply_apply, map_sub, Pi.sub_apply, LinearMap.sub_apply,
    resProdLeft_apply_ncoeff, Module.End.smul_def, resProdRight_apply_ncoeff]
  simp_rw [smul_sub]
  rw [finsum_sub_distrib]
  · congr
    rw [Units.smul_def, smul_finsum']
    · refine finsum_congr ?_
      intro i
      rw [smul_comm]
      congr 1
      rw [zsmul_comm]
      congr
    · refine BddAbove.finite <| bddAbove_def.mpr ?_
      use Int.toNat (-Y.order (R := R) a c)
      intro i hi
      contrapose! hi
      have : ((Y (R := R) a)[[i]]) c = 0 := ncoeff_zero_if_neg_order_leq Y a c i (by lia)
      simp [this]
  · refine BddAbove.finite <| bddAbove_def.mpr ?_
    use Int.toNat (-n - Y.order (R := R) b c)
    intro i hi
    contrapose! hi
    have : ((Y (R := R) b)[[n + i]]) c = 0 := ncoeff_zero_if_neg_order_leq Y b c (n + i) (by lia)
    simp [this]
  · refine BddAbove.finite <| bddAbove_def.mpr ?_
    use Int.toNat (-Y.order (R := R) a c)
    intro i hi
    contrapose! hi
    have : ((Y (R := R) a)[[i]]) c = 0 := ncoeff_zero_if_neg_order_leq Y a c i (by lia)
    simp [this]

-- show that the Borcherds identity everywhere follows from holding on two independent hyperplanes.





--lemma apply_neg_unit {R V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V]
--    (v : V) {k : ℤ} (hk : k ≤ -1) : ((VertexAlgebra.Y (R := R) v)[[k]]) (1 : V) = 0 := by

end VertexAlgebra

open stateField in
/-- A vertex algebra over a commutative ring `R` is an `R`-module `V` with a distinguished unit
element `1`, together with a multiplication operation that takes values in Laurent series with
coefficients in `V`, such that `a(z) 1 ∈ a + zV[[z]]` for all `a ∈ V` -/
class VertexAlgebra1 (R V : Type*) [CommRing R] [AddCommGroupWithOne V] extends Module R V where
  /-- The multiplication operation. -/
  Y : stateField R V
  /-- The Borcherds identity holds. -/
  borcherdsId : ∀ (a b c : V) (r s t : ℤ), borcherdsId Y a b c r s t
  /-- Right multiplication by the unit vector is nonsingular. -/
  unit_comm : ∀ (a : V), order Y a 1 = 0
  /-- The constant coefficient of right multiplication by the unit vector is identity. -/
  unit_right : ∀ (a : V), coeff (Y a) 0 1 = a

section

variable {R : Type*} {V : Type*} [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra1 R V]

theorem borcherdsIdentity (a b c : V) (r s t : ℤ) :
    borcherdsId VertexAlgebra1.Y (R := R) a b c r s t :=
  VertexAlgebra1.borcherdsId a b c r s t

theorem unit_right_order (a : V) : order VertexAlgebra1.Y (R := R) a 1 = 0 :=
  VertexAlgebra1.unit_comm a

theorem unit_right_zero (a : V) : HVertexOperator.coeff (R := R) (VertexAlgebra1.Y a) 0 1 = a :=
  VertexAlgebra1.unit_right a

end

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
  .ofSetLike (VertexSubalgebra R V)

initialize_simps_projections VertexSubalgebra (carrier → coe, as_prefix coe)

@[simp]
theorem coe_mk (s : Submodule R V) (h1) (hm) :
    (VertexSubalgebra.mk (R := R) s h1 hm : Set V) = s :=
  rfl

@[simp]
theorem mem_mk (s : Submodule R V) (h1) (hm) (x) :
    x ∈ VertexSubalgebra.mk (R := R) s h1 hm ↔ x ∈ s :=
  .rfl

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

/-
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
