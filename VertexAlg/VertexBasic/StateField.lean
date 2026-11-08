/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import VertexAlg.VertexBasic.VertexOperator

/-!
# State-field correspondences
In this file we introduce state-field correspondences prove some basic results about them.
## Definitions
 * `VertexAlg.stateField` : This is the left-multiplication structure in a vertex algebra, sometimes
   called a state-field correspondence. It is fundamentally a linear map `V →ₗ[R] V →ₗ[R] V((z))`.
 * Borcherds identity sums: These are composites of vertex operators multiplied by binomial powers.
## Main results
* Associativity is equivalent to a special case of the Borcherds identity.
* The commutator formula is equivalent to a special case of the Borcherds identity.
* The Borcherds identity is equivalent to a combination of either associativity or
  weak associativity, and either locality or the commutator formula.
## TODO
* Hasse-Schmidt differential
* creative fields?
* reconstruction?
## References
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
Matsuo-Nagatomo `On axioms for a vertex algebra and the locality of quantum fields` ArXiv
  hep-th/9706118
Borcherds
-/

@[expose] public section

/-- The multiplication in a vertex algebra. -/
abbrev stateField (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  V →ₗ[R] VertexOperator R V

namespace stateField

open HVertexOperator VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (Y : stateField R V)

--scoped[VertexAlg] notation a "[[" n "]]" => ncoeff (Y a) n

theorem Y_coeff_add_left_eq (Y : stateField R V) (a b : V) (n : ℤ) :
    HVertexOperator.coeff (Y a + Y b) n =
      HVertexOperator.coeff (Y a) n + HVertexOperator.coeff (R := R) (Y b) n :=
  rfl

theorem Y_ncoeff_add_left_eq (a b : V) (n : ℤ) :
    (Y a + Y b).ncoeff n = (Y a).ncoeff n + (Y b).ncoeff n := rfl

theorem Y_coeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    HVertexOperator.coeff (Y (r • a)) n = r • HVertexOperator.coeff (R := R) (Y a) n := by
  simp only [map_smul]
  exact rfl

theorem Y_ncoeff_smul_left_eq (r : R) (a : V) (n : ℤ) :
    (Y (r • a)).ncoeff n = r • (Y a).ncoeff n := by
  simp only [map_smul]
  exact rfl

theorem coeff_add_left_eq (a b c : V) (n : ℤ) :
    HVertexOperator.coeff (Y (a + b)) n c =
      HVertexOperator.coeff (Y a) n c + HVertexOperator.coeff (R := R) (Y b) n c := by
  rw [map_add, Y_coeff_add_left_eq, LinearMap.add_apply]

theorem ncoeff_add_left_eq (a b c : V) (n : ℤ) :
    (Y (a + b)).ncoeff n c = (Y a).ncoeff n c + (Y b).ncoeff n c := by
  rw [map_add, Y_ncoeff_add_left_eq, LinearMap.add_apply]

theorem coeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    HVertexOperator.coeff (Y (r • a)) n b = r • HVertexOperator.coeff (Y a) n b := by
  rw [Y_coeff_smul_left_eq, LinearMap.smul_apply]

theorem ncoeff_smul_left_eq (r : R) (a b : V) (n : ℤ) :
    (Y (r • a)).ncoeff n b = r • (Y a).ncoeff n b := by
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
  (Y ((Y a).ncoeff t b)).ncoeff s c = (Finset.range (-s - order Y b c).toNat).sum
    (fun i ↦ (-1) ^ i • (Ring.choose (t : ℤ)  i) •
    ((Y a).ncoeff (t - i) ((Y b).ncoeff (s + i) c))) +
    (Finset.range (- order Y a c).toNat).sum (fun i ↦ (t + i + 1).negOnePow • (Ring.choose t i) •
      (Y b).ncoeff (s + t - i) ((Y a).ncoeff i c))

/-- The commutator formula for vertex algebras. -/
def commutatorFormula (a b c : V) (r s : ℤ) : Prop :=
  (Y a).ncoeff r ((Y b).ncoeff s c) - (Y b).ncoeff s ((Y a).ncoeff r c) =
  (Finset.range (- order Y a b).toNat).sum (fun i ↦ (Ring.choose r i) •
  (Y ((Y a).ncoeff i b)).ncoeff (r+s-i) c)

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

variable {R V : Type*} [CommRing R] [AddCommGroupWithOne V] [Module R V]

/-- A divided-power system of translation operators.  `T 1` is often written `T`. -/
def T (Y : stateField R V) (n : ℕ) : Module.End R V where
  toFun := fun (x : V) => HVertexOperator.coeff (Y x) n 1
  map_add' := by intros; simp only [coeff_add_left_eq]
  map_smul' := by intros; simp only [coeff_smul_left_eq, RingHom.id_apply]

/-- The skew-symmetry property for vertex algebras: `Y(u,z)v = exp(Tz)Y(v,-z)u`. -/
def skewSymmetry (Y : stateField R V) (a b : V) (n : ℤ) : Prop :=
  (Y b).ncoeff n a = (Finset.range (-n - order Y a b).toNat).sum
    (fun i ↦ (n + i + 1).negOnePow • T Y i ((Y a).ncoeff (n+i) b))

/-- A state-field map is translation covariant with respect to a divided-power system of
endomorphisms that stabilizes identity if left translation satisfies the Leibniz rule, i.e.,
`T_n Y(a,z)b = ∑ k, Y(T_k a, z) (T_{n-k} b)`.  We omit conditions on the divided-power
system `f`. -/
def translationCovariance (Y : stateField R V) (a b : V) (f : ℕ → Module.End R V) :
    Prop :=
  ∀ (i : ℕ) (n : ℤ), f i • (Y a).ncoeff n • b =
    (Finset.HasAntidiagonal.antidiagonal i).sum fun m =>
      f m.fst • ((Y a).ncoeff (n - m.fst)) • (f m.snd b)

end Unital

/-- The first sum in the Borcherds identity, giving the `x^t z^s` coefficient of
`x^r (1 + z/x)^r (a(x)b)(z)c`. -/
noncomputable abbrev borcherdsSum1 (a b c : V) (r s t : ℤ) : V :=
  (Finset.range (-t - order Y a b).toNat).sum
    (fun i ↦ (Ring.choose r i) • ncoeff (Y (ncoeff (Y a) (t+i) b)) (r+s-i) c)

/-- The second sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`y^t (1 - z/y)^t a(y)b(z)c`. -/
noncomputable abbrev borcherdsSum2 (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-s - order Y b c)))
    (fun i ↦ (Int.negOnePow i) • (Ring.choose t i) • ncoeff (Y a) (r+t-i)
    (ncoeff (Y b) (s+i) c))

/-- The third sum in the Borcherds identity, giving the `y^r z^s` coefficient of
`-(-y)^t (1 - y/z)^t b(z)a(y)c`. -/
noncomputable abbrev borcherdsSum3 (a b c : V) (r s t : ℤ) : V :=
  Finset.sum (Finset.range (Int.toNat (-r - order Y a c)))
    (fun i ↦ (t+i+1).negOnePow • (Ring.choose t i) • ncoeff (Y b) (s+t-i)
    (ncoeff (Y a) (r+i) c))

/-- The Borcherds identity, also called the Jacobi identity or Cauchy-Jacobi identity when put in
power-series form.  It is a formal distribution analogue of the combination of commutativity and
associativity. -/
noncomputable abbrev borcherdsId (a b c : V) (r s t : ℤ) : Prop :=
  borcherdsSum1 Y a b c r s t = borcherdsSum2 Y a b c r s t + borcherdsSum3 Y a b c r s t

/-- The weak associativity property for vertex algebras (needs fixing). It should be that
`Y(Y(a,x)b,y) ∼ Y(a,x + y) Y(b,y)` -/
def weakAssociativity (a b c : V) (r s t : ℤ) : Prop :=
  borcherdsSum1 Y a b c r s t = borcherdsSum2 Y a b c r s t

theorem associativity_left (a b c : V) (s t : ℤ) :
    borcherdsSum1 Y a b c 0 s t = (Y ((Y a).ncoeff t b)).ncoeff s c := by
  cases h : (Int.toNat (-t - order Y a b)) with
    | zero =>
      simp [borcherdsSum1, h, ncoeff_zero_if_neg_order_leq Y a b t (by lia)]
    | succ n =>
      rw [borcherdsSum1, h, Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, zero_add, Ring.choose_zero_right (0 : ℤ),
        one_smul, Nat.cast_zero, add_zero, sub_zero]
      intro i hi
      rw [Ring.choose_zero_pos ℤ (by lia), zero_smul]

theorem associativity_right (a b c : V) (s t : ℤ) : borcherdsSum2 Y a b c 0 s t +
    borcherdsSum3 Y a b c 0 s t = (Finset.range (-s - order Y b c).toNat).sum
    (fun i ↦ (Int.negOnePow i) • (Ring.choose (t : ℤ) i) •
      ncoeff (Y a) (t-i) (ncoeff (Y b) (s+i) c)) +
    (Finset.range (- order Y a c).toNat).sum (fun i ↦ (t+i+1).negOnePow •
    (Ring.choose t i) • ncoeff (Y b) (s+t-i) (ncoeff (Y a) i c)) := by
  unfold borcherdsSum2 borcherdsSum3
  simp only [neg_zero, zero_sub, zero_add]

theorem borcherdsId_at_zero_iff_associativity (a b c : V) (s t : ℤ) :
    borcherdsId Y a b c 0 s t ↔ associativity Y a b c s t := by
  unfold borcherdsId
  rw [associativity_left, associativity_right]
  exact Eq.congr rfl rfl

theorem commutator_right_2 (a b c : V) (r s : ℤ) : borcherdsSum2 Y a b c r s 0 =
    ncoeff (Y a) r (ncoeff (Y b) s c) := by
  cases h : (Int.toNat (-s - order Y b c)) with
  | zero =>
    simp [borcherdsSum2, h, ncoeff_zero_if_neg_order_leq Y b c s (by lia)]
  | succ n =>
    rw [borcherdsSum2, h, Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, add_zero, Ring.choose_zero_right (0 : ℤ),
        one_smul, Nat.cast_zero, Int.negOnePow_zero, one_smul, add_zero, sub_zero]
    intro i hi
    rw [Ring.choose_zero_pos ℤ (by lia), zero_smul, smul_zero]

theorem commutator_right_3 (a b c : V) (r s : ℤ) : borcherdsSum3 Y a b c r s 0 =
    -ncoeff (Y b) s (ncoeff (Y a) r c) := by
  unfold borcherdsSum3
  cases h : (Int.toNat (-r - order Y a c)) with
  | zero =>
    simp [ncoeff_zero_if_neg_order_leq Y a c r (by lia)]
  | succ n =>
    rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)),
      Finset.sum_range_one, add_zero, Ring.choose_zero_right (0 : ℤ), one_smul, Nat.cast_zero,
      add_zero, sub_zero, zero_add, add_zero, Int.negOnePow_one, Units.neg_smul, one_smul]
    intro i hi
    rw [Ring.choose_zero_pos ℤ (by lia), zero_smul, smul_zero]

theorem borcherdsId_at_zero_iff_commutatorFormula (a b c : V) (r s : ℤ) :
    borcherdsId Y a b c r s 0 ↔ commutatorFormula Y a b c r s := by
  unfold borcherdsId commutatorFormula borcherdsSum1
  rw [commutator_right_2, commutator_right_3, ← sub_eq_add_neg, neg_zero, zero_sub]
  simp_rw [zero_add]
  exact eq_comm

theorem borcherdsSum1_eq_zero (a b c : V) (r s t : ℤ) (h : -order Y a b ≤ t) :
    borcherdsSum1 Y a b c r s t = 0 := by
  unfold borcherdsSum1
  have hrange : Int.toNat (-t - order Y a b) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

theorem locality_left_eq_borcherdsSum2 (a b c : V) (r s : ℤ) :
    (Finset.sum (Finset.HasAntidiagonal.antidiagonal (Int.toNat (-s - order Y b c))) fun m ↦
    (Int.negOnePow m.2) • Nat.choose (Int.toNat (-s - order Y b c)) m.2 •
    (HVertexOperator.coeff (Y a) (-r - 1 - m.1))
    ((HVertexOperator.coeff (Y b) (-s - 1 - m.2)) c)) =
    borcherdsSum2 Y a b c r s (Int.toNat (-s - order Y b c)) := by
  unfold borcherdsSum2 ncoeff
  rw [Finset.Nat.antidiagonal_eq_map']
  simp_all only [Finset.sum_map, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.eventually_constant_sum ?_ (Nat.le_succ (Int.toNat (-s - order Y b c)))]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simp_all only [Finset.mem_range, neg_sub]
    congr 1
    rw [Ring.choose_natCast, natCast_zsmul]
    congr
    · refine congrArg (coeff (Y a)) ?_
      rw [sub_eq_sub_iff_add_eq_add, Int.sub_add_cancel, ← Int.sub_sub,
        Int.sub_eq_add_neg (b := r), add_comm _ (-r), Int.add_sub_assoc, add_assoc,
        eq_neg_add_iff_add_eq, Int.add_right_neg, ← Int.sub_eq_iff_eq_add', zero_sub_sub,
        ← Nat.cast_sub (le_of_lt hi), Nat.cast_inj]
      rfl
    · refine congrArg (coeff (Y b)) ?_
      rw [Int.neg_add, show -s + -i - 1 = -s - 1 - i by abel]
      congr
  intro i hi
  have h : (HVertexOperator.coeff (Y b) (-s - 1 - i)) c = 0 :=
    coeff_eq_zero_of_lt_order Y b c (-s - 1 - i) (by grind)
  rw [smul_eq_zero_of_right]
  rw [smul_eq_zero_of_right]
  grind only [Function.Embedding.coeFn_mk, = map_zero]

theorem locality_right_eq_borcherdsSum3 (a b c : V) (r s : ℤ) : Finset.sum
    (Finset.HasAntidiagonal.antidiagonal (Int.toNat (-r - order Y a c)))
      (fun m => -(Int.negOnePow m.2) • (Nat.choose (Int.toNat (-r - order Y a c)) m.2) •
      HVertexOperator.coeff (Y b) (-s - 1 - m.2) (HVertexOperator.coeff (Y a) (-r - 1 - m.1) c)) =
    borcherdsSum3 Y a b c r s (Int.toNat (-r - order Y a c)) := by
  unfold borcherdsSum3 ncoeff
  rw [Finset.Nat.antidiagonal_eq_map]
  simp only [neg_sub, Units.neg_smul, Finset.sum_map, Int.ofNat_toNat, LinearMap.coe_mk,
    AddHom.coe_mk]
  erw [Function.Embedding.coeFn_mk]
  simp only [neg_add_rev]
  rw [Finset.eventually_constant_sum ?_ (Nat.le_succ (Int.toNat (-r - order Y a c)))]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simp_all only [Finset.mem_range]
    rw [Nat.cast_sub (le_of_lt hi), show (max (-r - Y.order a c) 0) = -r - Y.order a c by lia,
      Int.negOnePow_sub, Int.negOnePow_add, mul_comm _ (Int.negOnePow 1),
      ← smul_smul (Int.negOnePow 1), Int.negOnePow_one, Int.negOnePow_add, Units.neg_smul, one_smul,
      neg_inj ]
    congr 1
    · grind
    · have : (-r - Y.order a c) = (-r - Y.order a c).toNat := by grind
      rw [this, Ring.choose_natCast, Nat.choose_symm (by grind), natCast_zsmul]
      grind
  intro i hi
  have h : (HVertexOperator.coeff (Y a) (-r - 1 - ↑i)) c = 0 :=
    coeff_eq_zero_of_lt_order Y a c (-r - 1 - i) (by grind)
  rw [h, LinearMap.map_zero, smul_zero, smul_zero, neg_zero]

/-!
theorem locality_if_Borcherds_sums_2_3_eq (a b : V) (h : ∀ (c : V) (r s : ℤ)
    (t : ℕ), Int.toNat (-s - order R b c) ≤ t → Int.toNat (-r - order R a c) ≤ t →
    borcherdsSum2 R a b c r s t = borcherdsSum3 R a b c r s t) : locality R a b := by
  unfold locality isLocal isLocalToOrderLeq
  --
--  rw [locality_right_eq_borcherdsSum3 a b c ]
  sorry
theorem Borcherds_sums_2_3_eq_if_locality (a b c : V) (r s t : ℤ)
    (h₂ : Int.toNat (-s - order R b c) ≤ t) (h₃ : Int.toNat (-r - order R a c) ≤ t)
    (h : locality R a b) : borcherdsSum2 R a b c r s t = borcherdsSum3 R a b c r s t := by
  --rw [← locality_right_eq_borcherdsSum3, ]
  sorry
theorem borcherdsId_at_large_t_iff_locality (a b c : V) (r s t : ℤ) (h : - order R a b ≤ t) :
    borcherdsId R a b c r s t ↔ locality R a b := by
  unfold borcherdsId locality isLocal
  rw [locality_left a b c r s t h]
  --need more
  exact eq_comm
-/

theorem weak_assoc_right (a b c : V) (r s t : ℤ) (h : r ≥ -order Y a c) :
    borcherdsSum3 Y a b c r s t = 0 := by
  unfold borcherdsSum3
  have hrange : Int.toNat (-r - order Y a c) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

-- need to revise weak associativity : pairs of fields are weakly associative

theorem borcherdsId_at_large_r_iff_weak_assoc (a b c : V) (r s t : ℤ) (h : r ≥ -order Y a c) :
    borcherdsId Y a b c r s t ↔ weakAssociativity Y a b c r s t := by
  unfold borcherdsId weakAssociativity
  rw [weak_assoc_right Y a b c r s t h, add_zero]

theorem toNat_eq_sub_toNat_add (t : ℤ) (n : ℕ) (h : Int.toNat t = Nat.succ n) :
    Int.toNat t = Int.toNat (t - 1) + 1 := by
  rw [Int.pred_toNat, h, Nat.succ_sub_succ_eq_sub, tsub_zero]

theorem borcherds1Recursion
    (a b c : V) (r s t : ℤ) : borcherdsSum1 Y a b c (r + 1) s t =
    borcherdsSum1 Y a b c r (s + 1) t + borcherdsSum1 Y a b c r s (t + 1) := by
  unfold borcherdsSum1
  cases h : (Int.toNat (-t - order Y a b)) with
  | zero =>
    have : (-(t + 1) - Y.order a b).toNat = 0 := by lia
    rw [this]
    simp
  | succ n =>
    simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul]
    rw [Finset.sum_add_distrib, add_assoc, add_comm]
    have h1 : (-1 + -t - order Y a b).toNat = n := by lia
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc r 1 s,
      Ring.choose_zero_right', pow_zero, CharP.cast_eq_zero, add_zero, sub_zero, one_smul,
      add_comm s 1, neg_add_rev, Int.reduceNeg, h1, add_assoc t 1, add_right_inj]
    congr
    ext n
    have h2 : r + (1 + s) - (n + 1) = r + s - n := by omega
    rw [h2, add_comm _ 1]

theorem borcherds2Recursion
    (a b c : V) (r s t : ℤ) : borcherdsSum2 Y a b c (r + 1) s t =
    borcherdsSum2 Y a b c r (s + 1) t + borcherdsSum2 Y a b c r s (t + 1) := by
  unfold borcherdsSum2
  cases h : (Int.toNat (-s - order Y b c)) with
    | zero =>
      have : (-(s + 1) - Y.order b c).toNat = 0 := by lia
      rw [this]
      simp
    | succ n =>
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      have h1 : (-(s + 1) - Y.order b c).toNat = n := by lia
      rw [h1, ← add_assoc]
      congr 1
      · rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦
          (add_eq_of_eq_neg_add (by congr 1 <;> simp [Int.negOnePow_succ] <;> lia)).symm
      · simp; lia

theorem borcherds3Recursion
    (a b c : V) (r s t : ℤ) : borcherdsSum3 Y a b c (r + 1) s t =
    borcherdsSum3 Y a b c r (s + 1) t + borcherdsSum3 Y a b c r s (t + 1) := by
  unfold borcherdsSum3
  cases h : (Int.toNat (-r - order Y a c)) with
    | zero =>
      have : (-(r + 1) - Y.order a c).toNat = 0 := by lia
      rw [this]
      simp
    | succ n =>
      rw [add_assoc]
      refine eq_add_of_sub_eq' ?_
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      have h1 : (-(r + 1) - Y.order a c).toNat = n := by lia
      rw [h1, Finset.sum_add_distrib, sub_eq_add_neg, neg_add, add_assoc, add_assoc]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro i hi
        congr 1
        · exact (Int.negOnePow_eq_iff _ _).mpr (by grind only [= Int.even_iff])
        · lia
      · congr 1
        · rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i hi ↦ by
            simp [← add_assoc, Int.negOnePow_succ, add_right_comm t 1]; lia
        · simp [Int.negOnePow_succ]; lia

lemma borcherdsId_shift_3 (a b c : V) (r s t : ℤ) (h1 : borcherdsId Y a b c (r + 1) s t)
    (h2 : borcherdsId Y a b c r (s + 1) t) :
    borcherdsId Y a b c r s (t + 1) := by
  rw [borcherdsId] at *
  rwa [borcherds1Recursion, h2, borcherds2Recursion, add_assoc, add_assoc, add_right_inj,
    borcherds3Recursion, add_left_comm, add_right_inj] at h1

lemma borcherdsId_shift_2 (a b c : V) (r s t : ℤ) (h1 : borcherdsId Y a b c (r + 1) s t)
    (h3 : borcherdsId Y a b c r s (t + 1)) :
    borcherdsId Y a b c r (s + 1) t := by
  rw [borcherdsId] at *
  rwa [borcherds1Recursion, h3, borcherds2Recursion, add_left_comm,
    add_comm _ (borcherdsSum2 Y a b c r s (t + 1)), add_assoc, add_right_inj, borcherds3Recursion,
    ← add_assoc, add_left_inj] at h1

lemma borcherdsId_shift_1 (a b c : V) (r s t : ℤ) (h2 : borcherdsId Y a b c r (s + 1) t)
    (h3 : borcherdsId Y a b c r s (t + 1)) :
    borcherdsId Y a b c (r + 1) s t := by
  rw [borcherdsId] at *
  rw [borcherds1Recursion, borcherds2Recursion, borcherds3Recursion, h2, h3]
  abel

lemma borcherdsId_of_1_le (a b c : V) (q r s t : ℤ) (h : ∀ u v : ℤ, borcherdsId Y a b c r u v)
    (hq : r ≤ q) :
    borcherdsId Y a b c q s t := by
  suffices ∀ (n : ℕ), borcherdsId Y a b c (r + n) s t by
    rw [show q = r + (q - r).toNat by lia]
    exact this (q - r).toNat
  intro n
  induction n generalizing s t with
  | zero =>
    rw [CharP.cast_eq_zero, add_zero]
    exact h s t
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact borcherdsId_shift_1 Y a b c (r + n) s t (ih (s + 1) t) (ih s (t + 1))

lemma borcherdsId_of_2_le (a b c : V) (q r s t : ℤ) (h : ∀ u v : ℤ, borcherdsId Y a b c u s v)
    (hq : s ≤ q) :
    borcherdsId Y a b c r q t := by
  suffices ∀ (n : ℕ), borcherdsId Y a b c r (s + n) t by
    rw [show q = s + (q - s).toNat by lia]
    exact this (q - s).toNat
  intro n
  induction n generalizing r t with
  | zero =>
    rw [CharP.cast_eq_zero, add_zero]
    exact h r t
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact borcherdsId_shift_2 Y a b c r (s + n) t (ih (r + 1) t) (ih r (t + 1))

lemma borcherdsId_of_3_le (a b c : V) (q r s t : ℤ) (h : ∀ u v : ℤ, borcherdsId Y a b c u v t)
    (hq : t ≤ q) :
    borcherdsId Y a b c r s q := by
  suffices ∀ (n : ℕ), borcherdsId Y a b c r s (t + n) by
    rw [show q = t + (q - t).toNat by lia]
    exact this (q - t).toNat
  intro n
  induction n generalizing r s with
  | zero =>
    rw [CharP.cast_eq_zero, add_zero]
    exact h r s
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact borcherdsId_shift_3 Y a b c r s (t + n) (ih (r + 1) s) (ih r (s + 1))

lemma borcherdsId_of_antidiag_1 (a b c : V) (r s t : ℤ)
    (h : ∃ (n : ℕ), ∀ (k : ℕ), k ≤ n → borcherdsId Y a b c (r - n) (s + k) (t + n - k)) :
    borcherdsId Y a b c r s t := by
  obtain ⟨n, hn⟩ := h
  have (m : ℕ) (hm : ∀ k ≤ m, borcherdsId Y a b c (r - m) (s + k) (t + m - k)) (k : ℕ)
      (hk : k < m) :
      borcherdsId Y a b c (r - m + 1) (s + k) (t + m - k - 1) := by
    apply borcherdsId_shift_1
    · rw [add_assoc, show t + m - k - 1 = t + m - (k + 1) by lia]
      exact hm (k + 1) <| Order.add_one_le_iff.mpr hk
    · rw [Int.sub_add_cancel]
      exact hm k hk.le
  have (m k : ℕ) (hm : m ≤ n) (hkm : k ≤ n - m) :
      borcherdsId Y a b c (r - n + m) (s + k) (t + n - m - k) := by
    induction m generalizing k with
    | zero =>
      simp only [CharP.cast_eq_zero, sub_zero, add_zero]
      exact hn k <| by lia
    | succ m ih =>
      rw [show (t + n - _ - k) = t + (n - m : ℕ) - k - 1 by lia,
        show r - n + ↑(m + 1) = r - (n - m : ℕ) + 1 by lia]
      have hkmn : k < n - m := by lia
      refine this (n - m) ?_ k hkmn
      intro l hl
      rw [show t + (n - m : ℕ) - l = t + n - m - l by lia, show r - (n - m : ℕ) = r - n + m by lia]
      exact ih l (by lia) (by lia)
  simpa using this n 0

lemma borcherdsId_of_antidiag_2 (a b c : V) (r s t : ℤ)
    (h : ∃ (n : ℕ), ∀ (k : ℕ), k ≤ n → borcherdsId Y a b c (r + k) (s - n) (t + n - k)) :
    borcherdsId Y a b c r s t := by
  obtain ⟨n, hn⟩ := h
  have (m : ℕ) (hm : ∀ k ≤ m, borcherdsId Y a b c (r + k) (s - m) (t + m - k)) (k : ℕ)
      (hk : k < m) :
      borcherdsId Y a b c (r + k) (s - m + 1) (t + m - k - 1) := by
    apply borcherdsId_shift_2
    · rw [add_assoc, show t + m - k - 1 = t + m - (k + 1) by lia]
      exact hm (k + 1) <| Order.add_one_le_iff.mpr hk
    · rw [Int.sub_add_cancel]
      exact hm k hk.le
  have (m k : ℕ) (hm : m ≤ n) (hkm : k ≤ n - m) :
      borcherdsId Y a b c (r + k) (s - n + m) (t + n - m - k) := by
    induction m generalizing k with
    | zero =>
      simp only [CharP.cast_eq_zero, sub_zero, add_zero]
      exact hn k <| by lia
    | succ m ih =>
      rw [show (t + n - _ - k) = t + (n - m : ℕ) - k - 1 by lia,
        show s - n + ↑(m + 1) = s - (n - m : ℕ) + 1 by lia]
      have hkmn : k < n - m := by lia
      refine this (n - m) ?_ k hkmn
      intro l hl
      rw [show t + (n - m : ℕ) - l = t + n - m - l by lia, show s - (n - m : ℕ) = s - n + m by lia]
      exact ih l (by lia) (by lia)
  simpa using this n 0

lemma borcherdsId_of_antidiag_3 (a b c : V) (r s t : ℤ)
    (h : ∃ (n : ℕ), ∀ (k : ℕ), k ≤ n → borcherdsId Y a b c (r + k) (s + n - k) (t - n)) :
    borcherdsId Y a b c r s t := by
  obtain ⟨n, hn⟩ := h
  have (m : ℕ) (hm : ∀ k ≤ m, borcherdsId Y a b c (r + k) (s + m - k) (t - m)) (k : ℕ)
      (hk : k < m) :
      borcherdsId Y a b c (r + k) (s + m - k - 1) (t - m + 1) := by
    apply borcherdsId_shift_3
    · rw [add_assoc, show s + m - k - 1 = s + m - (k + 1) by lia]
      exact hm (k + 1) <| Order.add_one_le_iff.mpr hk
    · rw [Int.sub_add_cancel]
      exact hm k hk.le
  have (m k : ℕ) (hm : m ≤ n) (hkm : k ≤ n - m) :
      borcherdsId Y a b c (r + k) (s + n - m - k) (t - n + m) := by
    induction m generalizing k with
    | zero =>
      simp only [CharP.cast_eq_zero, sub_zero, add_zero]
      exact hn k <| (Nat.sub_le_sub_iff_right hm).mp hkm
    | succ m ih =>
      rw [show (s + n - _ - k) = s + (n - m : ℕ) - k - 1 by lia,
        show t - n + ↑(m + 1) = t - (n - m : ℕ) + 1 by lia]
      have hkmn : k < n - m := by lia
      refine this (n - m) ?_ k hkmn
      intro l hl
      rw [show s + (n - m : ℕ) - l = s + n - m - l by lia, show t - (n - m : ℕ) = t - n + m by lia]
      exact ih l (by lia) (by lia)
  simpa using this n 0





-- theorem Borcherds_on_two_transverse_half_spaces_implies Borcherds_everywhere

/-
theorem vacuum_derivative_is_zero [AddCommGroup V] [UnboundedVertexMul V] [NonunitalVertexRing V] :
    T 1 1 = 0 := by
--  refine NonunitalVertexRing.borcherdsId vac vac vac -1 -1 -1
-- set u=v=w = vac, r=s=t=-1 to get
  vac_{-2}vac = vac_{-2}(vac_{-1}vac) + vac_{-2}(vac_{-1}vac) = 2vac_{-2}vac
-- theorem vacuum_products_vanish : Y n vac vac = 0 when n ≠-1: for n ≥ 0, this is from van_vac.
For n < -1, we use induction: u=v=w=vac, r=s = -1, t=n.
-- theorem left identity : Y n vac u = u if n = -1, and 0 if not := Borcherds with v = w = vac,
r = -1, t = 0.
-- theorem unit_left (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
theorem skew_symmetry_iff_Borcherds_at_zero
-/

/-

 Perhaps this theorem should wait until we have more API for formal power series.
theorem conv_pow_succ_X_sub_Y (A : Type*) [AddCommGroup A] (k l n : ℕ) (f : ℤ → ℤ → A) :
    (Finset.sum (Finset.antidiagonal (n + 1)) fun m ↦ (-1) ^ m.2 • Nat.choose (n + 1) m.2 •
    f (k - ↑m.1) (l - ↑m.2)) = Finset.sum (Finset.antidiagonal n) fun m ↦ (-1) ^ m.2 •
    Nat.choose n m.2 • f (k - ↑m.1 - 1) (l - ↑m.2) - Finset.sum (Finset.antidiagonal n) fun m ↦
    (-1) ^ m.2 • Nat.choose n m.2 • f (k - ↑m.1) (l - ↑m.2 - 1) := by
  -- left side is convolution with `(X-Y)^{n+1}`, right side is with `(X-Y)^n` then `(X-Y)`.
  sorry
-/

end stateField
