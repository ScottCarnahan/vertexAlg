/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.Binomial
public import VertexAlg.GroupActionEquiv
public import VertexAlg.toMathlib.NegOnePow
public import VertexAlg.toMathlib.PointwiseSMul


/-!
# Additions to Hahn series

## Main definitions
* `HahnSeries.leadingTerm`: The `single` whose coefficient is `leadingCoeff` and whose exponent is
  `orderTop`.
* `HahnSeries.equivDomain`: The equivalence between Hahn series induced by an order equivalence.

## TODO

-/

@[expose] public section

variable {α β σ Γ Γ₁ Γ₂ R S U V W X Y : Type*}

section Basic

namespace HahnSeries

variable [PartialOrder Γ] [Zero R]
@[simp]
theorem support_of_Subsingleton [Subsingleton R] {x : HahnSeries Γ R} :
    x.support = ∅ := by
  simp [Subsingleton.eq_zero x]

open Classical in
/-- A leading term of a Hahn series is a Hahn series with subsingleton support at minimal-order.
  This is uniquely defined if `Γ` is a linear order. -/
noncomputable def leadingTerm (x : HahnSeries Γ R) : HahnSeries Γ R :=
  if h : x = 0 then 0
    else single (x.isWF_support.min (support_nonempty_iff.2 h)) x.leadingCoeff

@[simp]
theorem leadingTerm_zero : leadingTerm (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem leadingTerm_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    leadingTerm x = single (x.isWF_support.min (support_nonempty_iff.2 hx)) x.leadingCoeff :=
  dif_neg hx

theorem leadingTerm_ne_iff {x : HahnSeries Γ R} : x ≠ 0 ↔ leadingTerm x ≠ 0 := by
  constructor
  · intro hx
    rw [leadingTerm_of_ne hx]
    simp_all only [ne_eq, single_eq_zero_iff]
    exact leadingCoeff_ne_zero.mpr hx
  · contrapose!
    intro hx
    rw [hx]
    exact leadingTerm_zero

theorem leadingCoeff_leadingTerm {x : HahnSeries Γ R} :
    leadingCoeff (leadingTerm x) = leadingCoeff x := by
  by_cases h : x = 0
  · rw [h, leadingTerm_zero]
  · rw [leadingTerm_of_ne h, leadingCoeff_of_single]

section Order

variable [Zero Γ]

@[simp]
theorem order_of_subsingleton [Subsingleton R] {x : HahnSeries Γ R} : x.order = 0 :=
  (Subsingleton.eq_zero x) ▸ order_zero

theorem ne_zero_of_order_ne {x : HahnSeries Γ R} (hx : x.order ≠ 0) : x ≠ 0 := by
  by_cases h : x = 0
  · simp [h] at hx
  · exact h

theorem order_eq_of_le {x : HahnSeries Γ R} {g : Γ} (hg : g ∈ x.support)
    (hx : ∀ g' ∈ x.support, g ≤ g') : order x = g := by
  rw [order_of_ne <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg,
    Set.IsWF.min_eq_of_le x.isWF_support hg hx]

theorem leadingTerm_eq {x : HahnSeries Γ R} :
    x.leadingTerm = single x.order (x.coeff x.order) := by
  by_cases h : x = 0
  · rw [h, leadingTerm_zero, order_zero, coeff_zero, single_eq_zero]
  · rw [leadingTerm_of_ne h, leadingCoeff_eq, order_of_ne h]

end Order

theorem coeff_ofFinsupp' (f : Γ →₀ R) : (ofFinsupp f).coeff = f := rfl

@[simp]
theorem ofFinsupp_single (g : Γ) (r : R) : ofFinsupp (Finsupp.single g r) = single g r := by
  ext g'
  by_cases h : g = g'
  · simp [h]
  · simp [coeff_single_of_ne fun a ↦ h a.symm, Finsupp.single_eq_of_ne fun a ↦ h a.symm]

section Domain

variable [PartialOrder Γ₁] [PartialOrder Γ₂]

open Function

@[simp]
theorem embDomain_comp {Γ₂ : Type*} [PartialOrder Γ₂] {f : Γ ↪o Γ₁} {f' : Γ₁ ↪o Γ₂} :
    (embDomain (R := R) f') ∘ (embDomain f) = embDomain (f.trans f') := by
  ext x g''
  by_cases hf' : g'' ∈ Set.range f'
  · obtain ⟨g', hg'⟩ := hf'
    rw [← hg', comp_apply, embDomain_coeff]
    by_cases hf : g' ∈ Set.range f
    · obtain ⟨g, hg⟩ := hf
      rw [← hg, show f' (f g) = (RelEmbedding.trans f f') g by rfl, embDomain_coeff,
        embDomain_coeff]
    · simp only [Set.mem_range, not_exists] at hf
      rw [embDomain_notin_image_support, embDomain_notin_image_support]
      · simp only [RelEmbedding.coe_trans, comp_apply, Set.mem_image, EmbeddingLike.apply_eq_iff_eq,
          not_exists, not_and]
        exact fun g _ ↦ hf g
      · simp only [Set.mem_image, not_exists, not_and]
        exact fun g _ ↦ hf g
  · simp only [Set.mem_range, not_exists] at hf'
    rw [embDomain_notin_image_support, comp_apply, embDomain_notin_image_support]
    · simp only [Set.mem_image, not_exists, not_and]
      exact fun g' _ ↦ hf' g'
    · simp only [RelEmbedding.coe_trans, comp_apply, Set.mem_image, not_exists, not_and]
      exact fun g _ ↦ hf' (f g)

/-- The equivalence of HahnSeries induced by an order isomorphism. -/
def equivDomain (f : Γ ≃o Γ₁) : HahnSeries Γ R ≃ HahnSeries Γ₁ R where
  toFun x :=
  { coeff g := x.coeff (f.symm g)
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support]
        rwa [OrderIso.image_eq_preimage_symm, Set.mem_preimage] at hb }
  invFun x :=
  { coeff g := x.coeff (f g)
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.symm.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support]
        rwa [OrderIso.image_eq_preimage_symm, Set.mem_preimage] at hb }
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem equivDomain_coeff {f : Γ ≃o Γ₁} {x : HahnSeries Γ R} {a : Γ₁} :
    (equivDomain f x).coeff a = x.coeff (f.symm a) := rfl

@[simp]
theorem equivDomain_symm_coeff {f : Γ ≃o Γ₁} {x : HahnSeries Γ₁ R} {a : Γ} :
    ((equivDomain f).symm x).coeff a = x.coeff (f a) := rfl

theorem equivDomain_eq_embDomain (f : Γ ≃o Γ₁) (x : HahnSeries Γ R) :
    equivDomain f x = embDomain f x := by
  ext g
  have : g = (RelIso.toRelEmbedding f) (f.symm g) := (OrderIso.symm_apply_eq f).mp rfl
  rw [equivDomain_coeff, this, embDomain_coeff, ← this]

end Domain

section LinearOrder

variable {Γ : Type*} [LinearOrder Γ]

theorem le_orderTop_iff {x : HahnSeries Γ R} {i : WithTop Γ} :
    i ≤ x.orderTop ↔ (∀ (j : Γ), j < i → x.coeff j = 0) := by
  refine ⟨fun hi j hj => coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le hj hi), fun hj => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  · specialize hj (x.isWF_support.min (support_nonempty_iff.2 hx))
    rw [orderTop_of_ne_zero hx]
    contrapose! hj
    exact ⟨hj, coeff_orderTop_ne <| orderTop_of_ne_zero hx⟩

end LinearOrder

end HahnSeries

end Basic

section Addition

namespace HahnSeries

variable [PartialOrder Γ] [Zero V]

@[simp]
theorem single_smul [Zero R] [SMulWithZero R V] {g : Γ} {r : R} {s : V} :
    single g (r • s) = r • single g s := by
  ext g'
  by_cases h : g = g'
  · simp [h]
  · simp [coeff_single_of_ne (fun a ↦ h a.symm)]

theorem inf_orderTop_le_orderTop_sum {Γ} [LinearOrder Γ] [AddCommMonoid R] {α : Type*}
    {x : α → HahnSeries Γ R} {s : Finset α} :
    (s.inf fun i => orderTop (x i)) ≤ (∑ i ∈ s, x i).orderTop := by
  refine le_orderTop_iff.mpr fun g hg => ?_
  simp_all only [WithTop.coe_lt_top, Finset.lt_inf_iff, coeff_sum]
  exact Finset.sum_eq_zero fun i hi ↦ coeff_eq_zero_of_lt_orderTop (hg i hi)

@[simp]
theorem zsmul_coeff [AddGroup R] {x : R⟦Γ⟧} {n : ℤ} : (n • x).coeff = n • x.coeff := by
  cases n with
  | ofNat n => simp [Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc _ => simp [negSucc_zsmul]

theorem sub_orderTop_ne_of_leadingCoeff_eq [AddGroup R] {x y : HahnSeries Γ R} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    (x - y).orderTop ≠ g := by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x ≠ 0 := by
    rw [← orderTop_ne_top, hxg]
    exact WithTop.coe_ne_top
  rw [orderTop_of_ne_zero hx, WithTop.coe_eq_coe] at hxg
  have hy : y ≠ 0 := by
    rw [← orderTop_ne_top, hyg]
    exact WithTop.coe_ne_top
  rw [orderTop_of_ne_zero hy, WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

@[simp]
lemma ofFinsuppLinearMap_apply (R) {V} [Semiring R] [AddCommMonoid V] [Module R V] (a : Γ →₀ V) :
    ofFinsuppLinearMap R a = ofFinsupp a := rfl

/-- `ofIterate` as a linear map. -/
@[simps]
def ofIterate.linearMap {V} [Semiring R] [AddCommMonoid V] [Module R V] [PartialOrder Γ₁] :
    HahnSeries Γ (HahnSeries Γ₁ V) →ₗ[R] HahnSeries (Γ ×ₗ Γ₁) V where
  toFun := ofIterate
  map_add' _ _ := by ext; simp [ofIterate]
  map_smul' _ _ := by ext; simp [ofIterate]

/-- `toIterate` as a linear map. -/
@[simps]
def toIterate.linearMap {V} [Semiring R] [AddCommMonoid V] [Module R V] [PartialOrder Γ₁] :
    HahnSeries (Γ ×ₗ Γ₁) V →ₗ[R] HahnSeries Γ (HahnSeries Γ₁ V) where
  toFun := toIterate
  map_add' _ _ := by ext; simp [toIterate]
  map_smul' _ _ := by ext; simp [toIterate]

section LeadingTerm

variable {Γ : Type*} [LinearOrder Γ]

theorem orderTop_le_orderTop_add [AddMonoid R] {x y : HahnSeries Γ R}
    (h : x.orderTop ≤ y.orderTop) : x.orderTop ≤ (x + y).orderTop :=
  le_of_eq_of_le (min_eq_left h).symm min_orderTop_le_orderTop_add

theorem nonzero_of_nonzero_add_leading [AddMonoid R] {x y : HahnSeries Γ R}
    (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  rw [hx, leadingTerm_zero, add_zero] at hxy
  exact hy (id hxy.symm)

variable [AddCancelCommMonoid R] {x y : HahnSeries Γ R}

theorem coeff_add_leading (hxy : x = y + x.leadingTerm) (h : x ≠ 0) :
    y.coeff (x.isWF_support.min (support_nonempty_iff.2 h)) = 0 := by
  let xo := x.isWF_support.min (support_nonempty_iff.2 h)
  have hx : x.coeff xo = y.coeff xo + x.leadingTerm.coeff xo := by
    nth_rw 1 [hxy, coeff_add]
  have hxx : (leadingTerm x).coeff xo = x.leadingTerm.leadingCoeff := by
    rw [leadingCoeff_leadingTerm, leadingTerm_of_ne h, coeff_single_same]
  rw [hxx, leadingCoeff_leadingTerm] at hx
  have : x.leadingCoeff = x.coeff xo := by simp [leadingCoeff, orderTop, h, xo]
  rwa [this, right_eq_add] at hx

theorem add_leading_orderTop_ne (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.orderTop ≠ y.orderTop := by
  intro h
  have hyne : y.leadingTerm ≠ 0 := leadingTerm_ne_iff.mp hy
  have hx : x ≠ 0 := nonzero_of_nonzero_add_leading hxy hy
  simp only [orderTop_of_ne_zero hx, orderTop_of_ne_zero hy,
    WithTop.coe_eq_coe] at h
  have := coeff_add_leading hxy hx
  rw [h] at this
  rw [leadingTerm_of_ne hy, ← h, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hy, this,
    single_eq_zero] at hyne
  exact hyne rfl

theorem coeff_eq_of_not_orderTop (hxy : x = y + x.leadingTerm) (g : Γ) (hg : ↑g ≠ x.orderTop) :
    y.coeff g = x.coeff g := by
  rw [hxy, coeff_add, leadingTerm]
  simp only [left_eq_add]
  split_ifs with hx
  · simp only [coeff_zero]
  · simp only [orderTop_of_ne_zero hx, ne_eq, WithTop.coe_eq_coe] at hg
    exact coeff_single_of_ne hg

theorem support_subset_add_single_support (hxy : x = y + x.leadingTerm) :
    y.support ⊆ x.support := by
  intro g hg
  by_cases hgx : g = orderTop x
  · intro hx
    apply (coeff_orderTop_ne hgx.symm) hx
  · exact fun hxg => hg (Eq.mp (congrArg (fun r ↦ r = 0)
    (coeff_eq_of_not_orderTop hxy g hgx).symm) hxg)

theorem orderTop_lt_add_single_support_orderTop (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.orderTop < y.orderTop := by
  refine lt_of_le_of_ne ?_ (add_leading_orderTop_ne hxy hy)
  rw [orderTop_of_ne_zero hy, orderTop_of_ne_zero <| nonzero_of_nonzero_add_leading hxy hy]
  exact WithTop.coe_le_coe.mpr <| Set.IsWF.min_le_min_of_subset <|
    support_subset_add_single_support hxy

theorem order_lt_add_single_support_order [Zero Γ] (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.order < y.order := by
  rw [← WithTop.coe_lt_coe, order_eq_orderTop_of_ne_zero hy, order_eq_orderTop_of_ne_zero <|
    nonzero_of_nonzero_add_leading hxy hy]
  exact orderTop_lt_add_single_support_orderTop hxy hy

end LeadingTerm

end HahnSeries

end Addition

section Multiplication

namespace HahnModule

section BaseStructure

section basic

variable [PartialOrder Γ] [SMul R V]

@[simp] theorem of_nsmul [AddCommMonoid V] (n : ℕ) (x : HahnSeries Γ V) :
    (of R) (n • x) = n • (of R) x := rfl
@[simp] theorem of_symm_nsmul [AddCommMonoid V] (n : ℕ) (x : HahnModule Γ R V) :
    (of R).symm (n • x) = n • (of R).symm x := rfl
@[simp] theorem of_zsmul {V} [AddCommGroup V] [SMul R V] (n : ℤ) (x : HahnSeries Γ V) :
    (of R) (n • x) = n • (of R) x := rfl
@[simp] theorem of_symm_zsmul {V} [AddCommGroup V] [SMul R V] (n : ℤ) (x : HahnModule Γ R V) :
    (of R).symm (n • x) = n • (of R).symm x := rfl

instance instBaseSMulZeroClass' {V} [Zero V] [SMulZeroClass R V] :
    SMulZeroClass R (HahnModule Γ R V) :=
  inferInstanceAs <| SMulZeroClass R (HahnSeries Γ V)

end basic

variable [PartialOrder Γ]

/-- The isomorphism between HahnSeries and HahnModules, as a linear map. -/
@[simps]
def lof (R : Type*) [Semiring R] [AddCommMonoid V] [Module R V] :
    HahnSeries Γ V ≃ₗ[R] HahnModule Γ R V where
  toFun := of R
  map_add' := of_add
  map_smul' := of_smul
  invFun := (of R).symm
  left_inv := congrFun rfl
  right_inv := congrFun rfl

set_option backward.isDefEq.respectTransparency false in
/-- HahnModule coefficient-wise map as a HahnSeries-linear map. -/
def map {R} [Semiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid U] [Module R U]
    (f : U →ₗ[R] V) :
    HahnModule Γ R U →ₗ[R] HahnModule Γ R V where
  toFun x := (of R) (HahnSeries.map ((of R).symm x) f)
  map_add' _ _ := by ext; simp
  map_smul' s x := by ext; simp

@[simp]
protected lemma map_coeff [Semiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid U] [Module R U]
    (x : HahnModule Γ R U) (f : U →ₗ[R] V) (g : Γ) :
    ((of R).symm (map f x)).coeff g = f (((of R).symm x).coeff g) := by
  simp [map]

set_option backward.isDefEq.respectTransparency false in
/-- The linear equivalence between Hahn modules induced by an order equivalence. -/
def equivDomain [Semiring R] [AddCommMonoid V] [Module R V] [PartialOrder Γ₁] (f : Γ ≃o Γ₁) :
    HahnModule Γ R V ≃ₗ[R] HahnModule Γ₁ R V where
  toFun x := (of R) (HahnSeries.equivDomain f ((of R).symm x))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  invFun x := (of R) (HahnSeries.equivDomain f.symm ((of R).symm x))
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

end BaseStructure

variable [PartialOrder Γ] [PartialOrder Γ₁] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
  [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [Semiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid U] [Module R U]

/-- HahnModule coefficient-wise map as a HahnSeries-linear map. -/
def hmap (f : U →ₗ[R] V) :
    HahnModule Γ₁ R U →ₗ[HahnSeries Γ R] HahnModule Γ₁ R V where
  toFun x := (of R) (HahnSeries.map ((of R).symm x) f)
  map_add' x y := by ext; simp
  map_smul' s x := by
    ext g
    simp only [Equiv.symm_apply_apply, HahnSeries.map_coeff, coeff_smul, map_sum, map_smul,
      RingHom.id_apply]
    refine Eq.symm <| Finset.sum_subset (fun gh hgh => ?_) (fun gh hgh hz => (by simp_all))
    simp_all only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, ne_eq, HahnSeries.map_coeff,
      not_false_eq_true, and_true, true_and]
    apply fun h => hgh.2.1 (LinearMap.map_zero (R := R) (f := f) ▸ congrArg f h)

@[simp]
protected lemma hmap_coeff (x : HahnModule Γ R U) (f : U →ₗ[R] V) (g : Γ) :
    ((of R).symm (hmap (Γ := Γ) f x)).coeff g = f (((of R).symm x).coeff g) := by
  simp [hmap]

noncomputable instance instGroupModule {V} [AddCommGroup V] [Module R V] : Module (HahnSeries Γ R)
    (HahnModule Γ₁ R V) where
  add_smul _ _ _ := add_smul Module.add_smul
  zero_smul _ := zero_smul'

theorem smul_comm {R} [CommSemiring R] [Module R V] (r : R) (x : HahnSeries Γ R)
    (y : HahnModule Γ₁ R V) :
    r • x • y = x • r • y := by
  rw [SMulCommClass.smul_comm]

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
/-- The map that tensors a Hahn series with a module on the right. -/
def rightTensorMap {R} [CommSemiring R] [Module R V] [Module R U] :
    HahnModule Γ₁ R U ⊗[R] V →ₗ[R] HahnModule Γ₁ R (U ⊗[R] V) :=
  TensorProduct.uncurry _ _ _ _
  { toFun := fun x => {
      toFun := fun v => (of R) {
        coeff := fun g => tmul R (((of R).symm x).coeff g) v
        isPWO_support' := by
          refine Set.IsPWO.mono ((of R).symm x).isPWO_support ?_
          intro g hg
          simp_all only [Function.mem_support, ne_eq, HahnSeries.mem_support]
          contrapose! hg
          exact hg ▸ zero_tmul U v }
      map_add' := by
        intro y z
        ext; simp [tmul_add]
      map_smul' := by
        intro r y
        ext; simp }
    map_add' := by
      intro y z
      ext; simp [add_tmul]
    map_smul' := by
      intro r y
      ext; simp [smul_tmul'] }

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
/-- The map that tensors a Hahn series with a module on the right. -/
def leftTensorMap {R} [CommSemiring R] [Module R V] [Module R U] :
    U ⊗[R] HahnModule Γ₁ R V →ₗ[R] HahnModule Γ₁ R (U ⊗[R] V) :=
  TensorProduct.uncurry _ _ _ _
  { toFun := fun u => {
      toFun := fun x => (of R) {
        coeff := fun g => tmul R u (((of R).symm x).coeff g)
        isPWO_support' := by
          refine Set.IsPWO.mono ((of R).symm x).isPWO_support ?_
          intro g hg
          simp_all only [Function.mem_support, ne_eq, HahnSeries.mem_support]
          contrapose! hg
          exact hg ▸ tmul_zero V u }
      map_add' := by
        intro y z
        ext; simp [tmul_add]
      map_smul' := by
        intro r y
        ext; simp }
    map_add' := by
      intro y z
      ext; simp [add_tmul]
    map_smul' := by
      intro r y
      ext; simp [smul_tmul'] }

open MonoidAlgebra Finsupp Finset in
omit [IsOrderedCancelAddMonoid Γ] in
theorem ofFinsupp_smul_coeff {R} [CommSemiring R] [Module R V] (f : AddMonoidAlgebra R Γ)
    (x : HahnModule Γ₁ R V) :
    ((HahnModule.of R).symm ((HahnSeries.ofFinsupp f) • x)).coeff =
      f • ((HahnModule.of R).symm x).coeff := by
  ext g
  rw [coeff_smul, AddMonoidAlgebra.smul_eq, HahnSeries.coeff_ofFinsupp']
  refine (Finset.sum_of_injOn (M := V) id (Set.injOn_id _) ?_ ?_ ?_).symm
  · intro gh h
    simpa [mem_coe, mem_vaddAntidiagonal] using h
  · intro gh h hn
    simp only [mem_vaddAntidiagonal] at h
    simp only [id_eq, Set.image_id', SetLike.mem_coe, mem_vaddAntidiagonal, mem_support_iff, ne_eq,
      Function.mem_support, h.2.2, and_true, not_and, not_not] at hn
    aesop
  · intro gh h
    simp

end HahnModule

namespace HahnSeries

/-- An algebra homomorphism from `AddMonoidAlgebra` -/
@[simps]
def ofAddMonoidAlgebra [PartialOrder Γ] [AddCancelCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommSemiring R] :
    AddMonoidAlgebra R Γ →ₐ[R] HahnSeries Γ R where
  toFun := ofFinsupp
  map_one' := by
    ext g
    by_cases h : g = 0 <;> simp [h, AddMonoidAlgebra.one_def]
  map_mul' x y := by
      ext g
      rw [← of_symm_smul_of_eq_mul,
        HahnModule.ofFinsupp_smul_coeff x (HahnModule.of R (ofFinsupp y)),
        Equiv.symm_apply_apply, coeff_ofFinsupp, coeff_ofFinsupp',
        AddMonoidAlgebra.smul_eq_addMonoidAlgebra_mul]
  map_zero' := rfl
  map_add' x y := by
    simp only [← ofFinsuppLinearMap_apply R, ← map_add]
    exact LinearMap.congr_fun rfl (x + y) --defeq problem here
  commutes' r := by
    ext g
    by_cases h : g = 0
    · simp [h, algebraMap_apply]
    · simp [algebraMap_apply, coeff_single_of_ne h]

end HahnSeries

namespace HahnModule



end HahnModule

namespace HahnSeries

section OrderLemmas

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]

theorem order_add_le_mul {x y : HahnSeries Γ R} (hxy : x * y ≠ 0) :
    x.order + y.order ≤ (x * y).order := by
  refine WithTop.coe_le_coe.mp ?_
  rw [WithTop.coe_add, order_eq_orderTop_of_ne_zero (ne_zero_and_ne_zero_of_mul hxy).1,
    order_eq_orderTop_of_ne_zero (ne_zero_and_ne_zero_of_mul hxy).2,
    order_eq_orderTop_of_ne_zero hxy]
  exact orderTop_add_le_mul

theorem leadingCoeff_pow_of_ne_zero {x : HahnSeries Γ R} {n : ℕ}
    (h : x.leadingCoeff ^ n ≠ 0) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at h
    specialize ih (left_ne_zero_of_mul h)
    rw [pow_succ, pow_succ, leadingCoeff_mul_of_ne_zero (ih ▸ h), ih]

theorem orderTop_pow_of_nonzero {x : HahnSeries Γ R} {n : ℕ} (h : x.leadingCoeff ^ n ≠ 0) :
    (x ^ n).orderTop = n • x.orderTop := by
  haveI : Nontrivial R := nontrivial_of_ne (x.leadingCoeff ^ n) 0 h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at h
    specialize ih (left_ne_zero_of_mul h)
    rw [pow_succ, orderTop_mul_of_ne_zero (leadingCoeff_pow_of_ne_zero (left_ne_zero_of_mul h) ▸ h),
      ih, succ_nsmul]

open Finset in
theorem orderTop_prod_le_sum {α : Type*} {R} [CommSemiring R] {x : α → HahnSeries Γ R}
    {s : Finset α} :
    ∑ i ∈ s, (x i).orderTop ≤ (∏ i ∈ s, x i).orderTop := by
  refine cons_induction ?_ (fun a hfa ha ih => ?_) s
  · rw [sum_empty, prod_empty, ← single_zero_one]
    exact LE.le.trans (Preorder.le_refl 0) orderTop_single_le
  · rw [sum_cons, prod_cons]
    exact (add_le_add_right ih (x a).orderTop).trans orderTop_add_le_mul

open Finset in
theorem order_prod_le_sum {α : Type*} {R} [CommSemiring R] {x : α → HahnSeries Γ R} {s : Finset α}
    (hx : ∀ t : Finset α, ∏ i ∈ t, x i ≠ 0) :
    ∑ i ∈ s, (x i).order ≤ (∏ i ∈ s, x i).order := by
  refine cons_induction ?_ (fun a t ha ih => ?_) s
  · simp only [sum_empty, prod_empty, order_one, le_refl]
  · rw [sum_cons, prod_cons]
    refine (add_le_add_right ih (x a).order).trans (order_add_le_mul ?_)
    rw [← prod_cons ha]
    exact hx _

theorem pow_leadingCoeff {x : HahnSeries Γ R} (hx : ¬IsNilpotent x.leadingCoeff) (n : ℕ) :
    (x ^ n).leadingCoeff = (x.leadingCoeff) ^ n := by
  induction n with
  | zero => simp
  | succ n ihn =>
    rw [pow_succ, leadingCoeff_mul_of_ne_zero, ihn, pow_succ]
    rw [ihn, ← pow_succ]
    by_contra
    simp_all [IsNilpotent]

end OrderLemmas

variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]

/-- An invertible Hahn series supported at an additive unit. -/
@[simps]
noncomputable def UnitSingle [Semiring R] {g : Γ} (hg : IsAddUnit g) {r : R} (hr : IsUnit r) :
    (HahnSeries Γ R)ˣ where
  val := single g r
  inv := single hg.addUnit.neg hr.unit.inv
  val_inv := by simp
  inv_val := by simp

variable [PartialOrder Γ'] [AddCommMonoid Γ'] [IsOrderedCancelAddMonoid Γ'] [EquivLike F Γ Γ']
  [AddMonoidHomClass F Γ Γ'] [OrderIsoClass F Γ Γ']

/-- A ring isomorphism on Hahn series induced by an additive order isomorphism. -/
def equivDomainRingHom [NonAssocSemiring R] (f : F) :
    HahnSeries Γ R ≃+* HahnSeries Γ' R where
  toFun x := equivDomain f x
  invFun x := (equivDomain f).symm x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by
    simp only [equivDomain_eq_embDomain]
    rw [embDomain_mul _ (fun g g' ↦ map_add f g g')]
  map_add' x y := by simp [equivDomain_eq_embDomain, embDomain_add]

@[simp]
theorem equivDomainRingHom_apply_apply [NonAssocSemiring R] (f : F) (x : HahnSeries Γ R) (g : Γ') :
    (equivDomainRingHom f x).coeff g = x.coeff (EquivLike.inv f g) := by
  rfl

@[simp]
theorem equivDomainRingHom'_symm_apply_apply [NonAssocSemiring R] (f : F) (x : HahnSeries Γ' R)
    (g : Γ) :
    ((equivDomainRingHom f).symm x).coeff g = x.coeff (f g) := by
  rfl

instance [Semiring R] (f : F) :
    RingHomCompTriple HahnSeries.C (HahnSeries.equivDomainRingHom (R := R) f).symm.toRingHom
      HahnSeries.C where
  comp_eq := by
    ext _ g
    have : f 0 = 0 := by exact map_zero f
    by_cases hg : g = 0
    · rw [hg]
      simp
    · have : (OrderIsoClass.toOrderIso f) g ≠ 0 := by
        contrapose! hg
        rw [show (OrderIsoClass.toOrderIso f) g = f g by rfl, ← this] at hg
        exact EmbeddingLike.injective' f hg
      simp [equivDomainRingHom, this, hg]

instance [Semiring R] (f : F) :
    RingHomCompTriple HahnSeries.C (HahnSeries.equivDomainRingHom (R := R) f).toRingHom
      HahnSeries.C where
  comp_eq := by
    have h : EquivLike.inv f 0 = 0 := EquivLike.inv_apply_eq.mpr (map_zero f).symm
    ext r g
    by_cases hg : g = 0
    · simp [h, hg]
    · have : EquivLike.inv f g ≠ 0 := by
        contrapose! hg
        rw [← h] at hg
        exact (EquivLike.right_inv f).injective hg
      simp [this, hg]

@[simp]
theorem equivDomainRingHom_single [NonAssocSemiring R] (f : F) (g : Γ) (r : R) :
    equivDomainRingHom f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  · have : EquivLike.inv f g' ≠ g := by
      contrapose! h
      exact EquivLike.inv_apply_eq.mp h
    simp [h, this]

@[simp]
theorem equivDomainRingHom_symm_single [NonAssocSemiring R] (f : F) (g : Γ') (r : R) :
    (equivDomainRingHom f).symm (single g r) = single (EquivLike.inv f g) r := by
  ext g'
  by_cases h : f g' = g
  · have hinv : EquivLike.inv f g = g' := EquivLike.inv_apply_eq.mpr h.symm
    have : OrderIsoClass.toOrderIso f g'= f g' := rfl
    simp [equivDomainRingHom, h, hinv, this]
  · have : EquivLike.inv f g ≠ g' := by
      contrapose! h
      rw [← h, EquivLike.apply_inv_apply]
    simp [h, coeff_single_of_ne this.symm]

@[simp]
theorem equivDomainRingHom_smul [NonAssocSemiring R] (f : F) (r : R) (x : HahnSeries Γ R) :
    equivDomainRingHom f (r • x) = r • equivDomainRingHom f x := by
  ext
  simp

end HahnSeries

namespace HahnModule

variable {Γ Γ' Γ₁ Γ₂ : Type*} [PartialOrder Γ] [PartialOrder Γ'] [PartialOrder Γ₁] [PartialOrder Γ₂]
  [VAdd Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [VAdd Γ' Γ₂] [IsOrderedCancelVAdd Γ' Γ₂] [MulZeroClass R]
  [AddCommMonoid V] [SMulWithZero R V]

open Finset Function in
theorem embDomain_smul (φ : Γ ↪o Γ') (f : Γ₁ ↪o Γ₂) (hf : ∀ (g : Γ) y, f (g +ᵥ y) = φ g +ᵥ f y)
    (x : HahnSeries Γ R) (y : HahnModule Γ₁ R V) :
    HahnSeries.embDomain f ((of R).symm (x • y)) =
      (of R).symm ((HahnSeries.embDomain φ x) •
        (of R) (HahnSeries.embDomain f ((of R).symm y))) := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_smul, HahnSeries.embDomain_coeff]
    trans
      ∑ ij ∈ (Finset.VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO x.isPWO_support
        ((of R).symm y).isPWO_support g)).map (φ.toEmbedding.prodMap f.toEmbedding),
          (HahnSeries.embDomain φ x).coeff ij.1 •
          (HahnSeries.embDomain f ((of R).symm y)).coeff ij.2
    · simp
    apply Finset.sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [mem_map, mem_vaddAntidiagonal, HahnSeries.mem_support, ne_eq,
        Embedding.coe_prodMap, RelEmbedding.coe_toEmbedding, Prod.exists, Prod.map_apply,
        Prod.mk.injEq] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := HahnSeries.support_embDomain_subset (left_ne_zero_of_smul h2)
      obtain ⟨j, _, rfl⟩ := HahnSeries.support_embDomain_subset (right_ne_zero_of_smul h2)
      simp only [mem_map, mem_vaddAntidiagonal, Function.Embedding.coe_prodMap,
        HahnSeries.mem_support, Prod.exists]
      simp only [mem_vaddAntidiagonal, HahnSeries.embDomain_coeff, HahnSeries.mem_support, ← hf,
        OrderEmbedding.eq_iff_eq, Equiv.symm_apply_apply, HahnSeries.embDomain_coeff] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [HahnSeries.embDomain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, h⟩ :=
      support_smul_subset_vadd_support <| (HahnSeries.mem_support _ g).mpr hg
    obtain ⟨i, _, rfl⟩ := HahnSeries.support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := HahnSeries.support_embDomain_subset hj
    exact ⟨i +ᵥ j, h ▸ hf i j⟩

end HahnModule

end Multiplication

section Summable

namespace HahnSeries.SummableFamily

theorem hsum_subsingleton [PartialOrder Γ] [AddCommMonoid R] [Subsingleton α]
    {s : SummableFamily Γ R α} (a : α) :
    s.hsum = s a := by
  haveI : Unique α := uniqueOfSubsingleton a
  let e : Unit ≃ α := Equiv.ofUnique Unit α
  have he : ∀u : Unit, e u = a := fun u ↦ (fun f ↦ (Equiv.apply_eq_iff_eq_symm_apply f).mpr) e rfl
  have hs : Equiv e.symm s = single (ι := Unit) default (s a) := by ext; simp [he]
  rw [← hsum_equiv e.symm, hs, hsum_single]

section Semiring

open Finset Function

open Classical in
theorem pi_PWO_iUnion_support [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    {t : Π i : σ, (α i) → HahnSeries Γ R}
    (ht : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO) :
    (⋃ a : (i : σ) → i ∈ s → α i,
      (∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1).support).IsPWO := by
  induction s using cons_induction with
  | empty =>
    simp only [prod_empty]
    have h : ⋃ (_ : (i : σ) → i ∈ (∅ : Finset σ) → α i) , support (1 : HahnSeries Γ R) ⊆ {0} := by
      simp
    exact Set.Subsingleton.isPWO <| Set.subsingleton_of_subset_singleton h
  | cons a s' has hp =>
    refine (isPWO_iUnion_support_prod_mul (ht a) hp).mono ?_
    intro g hg
    simp only [mem_cons, prod_cons, Set.mem_iUnion, mem_support, true_or, ↓reduceDIte] at hg
    obtain ⟨f, hf⟩ := hg
    simp only [Set.mem_iUnion, mem_support, Prod.exists]
    use f a (mem_cons_self a s'), fun i hi => f i (mem_cons_of_mem hi)
    have hor : ∏ i ∈ s', (if h : i = a ∨ i ∈ s' then t i (f i (mem_cons.mpr h)) else 1) =
        ∏ i ∈ s', if h : i ∈ s' then t i (f i (mem_cons_of_mem h)) else 1 := by
      refine prod_congr rfl fun x hx => ?_
      simp_all only [dite_true, or_true]
    exact hor ▸ hf

open Classical in
/-- delete this? -/
theorem cosupp_subset_iunion_cosupp_left [AddCommMonoid Γ] [PartialOrder Γ] [PartialOrder Γ₁]
    [VAdd Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁] [IsOrderedCancelAddMonoid Γ] [AddCommMonoid R]
    [AddCommMonoid V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ₁ V β) (g : Γ₁) {gh : Γ × Γ₁}
    (hgh : gh ∈ VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
      t.isPWO_iUnion_support g)) :
    Set.Finite.toFinset (s.finite_co_support (gh.1)) ⊆
    (VAddAntidiagonal g (Set.VAddAntidiagonal.finite_of_isPWO s.isPWO_iUnion_support
      t.isPWO_iUnion_support g)).biUnion
      fun (g' : Γ × Γ₁) => Set.Finite.toFinset (s.finite_co_support (g'.1)) := by
  intro a ha
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, mem_biUnion, Prod.exists, exists_and_right, exists_and_left]
  exact Exists.intro gh.1 ⟨⟨hgh.1, Exists.intro gh.2 hgh.2⟩, ha⟩

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

open Classical in
theorem pi_finite_co_support {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} (htp : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO)
    (htfc : ∀ i : σ, ∀ h : Γ, {a : α i | ((t i) a).coeff h ≠ 0}.Finite) :
    {a : (i : σ) → i ∈ s → α i |
      ((fun a ↦ ∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1) a).coeff g ≠ 0}.Finite := by
  induction s using cons_induction generalizing g with
  | empty => exact Set.Subsingleton.finite fun x _ y _ =>
    (funext₂ fun j hj => False.elim ((List.mem_nil_iff j).mp hj))
  | cons a s' has hp =>
    simp only [prod_cons, mem_cons, true_or, ↓reduceDIte, coeff_mul]
    have hor : ∀ b : (i : σ) → i ∈ (cons a s' has) → α i,
        ∏ i ∈ s', (if h : i ∈ cons a s' has then t i (b i h) else 1) =
        ∏ i ∈ s', if h : i ∈ s' then t i (b i (mem_cons_of_mem h)) else 1 :=
      fun b => prod_congr rfl fun x hx => (by simp [*])
    apply ((addAntidiagonal (htp a) (pi_PWO_iUnion_support s' α htp) g).finite_toSet.biUnion'
      _).subset _
    · exact fun ij _ => {b : (i : σ) → i ∈ (cons a s' has) → α i |
        (t a (b a (mem_cons_self a s'))).coeff ij.1 *
        (∏ i ∈ s', if h : i ∈ (cons a s' has) then (t i) (b i h) else 1).coeff ij.2 ≠ 0}
    · intro gh hgh
      simp_rw [hor _, ne_eq]
      refine Set.Finite.of_finite_image (f := fun (b : (i : σ) → i ∈ cons a s' has → α i) =>
        (b a (mem_cons_self a s'), fun (i : σ) (hi : i ∈ s') => b i (mem_cons_of_mem hi)))
        ((Set.Finite.prod (htfc a gh.1) (hp gh.2)).subset ?_) ?_
      · intro x hx
        simp_all only [Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
        obtain ⟨y, hy⟩ := hx
        constructor
        · have h : x.1 = y a (mem_cons_self a s') := by rw [← hy.2]
          exact left_ne_zero_of_mul (h ▸ hy.1)
        · have h : x.2 = fun i hi ↦ y i (mem_cons_of_mem hi) := by rw [← hy.2]
          simp_rw [h]
          exact right_ne_zero_of_mul hy.1
      · refine Injective.injOn ?_
        intro x y hxy
        simp_all only [dite_true, cons_eq_insert, mem_insert, or_true, mem_coe, mem_addAntidiagonal,
          Set.mem_iUnion, mem_support, ne_eq, Prod.mk.injEq]
        ext i hi
        by_cases hhi : i = a
        · exact hhi ▸ hxy.1
        · exact congrFun (congrFun hxy.2 i) (Or.resolve_left (mem_cons.mp hi) hhi)
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      have hhx := exists_ne_zero_of_sum_ne_zero hx
      simp only [mem_coe, mem_addAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
        mem_cons, Set.mem_setOf_eq, exists_prop, Prod.exists]
      use hhx.choose.1, hhx.choose.2
      refine ⟨⟨?_, ?_⟩, hhx.choose_spec.2⟩
      · use x a (mem_cons_self a s')
        exact left_ne_zero_of_mul hhx.choose_spec.2
      · refine ⟨?_, (Finset.mem_addAntidiagonal.mp hhx.choose_spec.1).2.2⟩
        use fun i hi => x i (mem_cons_of_mem hi)
        have h := right_ne_zero_of_mul hhx.choose_spec.2
        have hpr :
            ∏ x_1 ∈ s', (if h : x_1 = a ∨ x_1 ∈ s' then t x_1 (x x_1 (mem_cons.mpr h)) else 1) =
            ∏ x_1 ∈ s', (if h : x_1 ∈ s' then t x_1 (x x_1 (mem_cons_of_mem h)) else 1) :=
          prod_congr rfl fun i hi => (by simp [hi])
        simp_all

open Classical in
/-- A summable family made from pointwise multiplication along a finite collection of summable
families. -/
@[simps]
noncomputable def PiFamily (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) : (SummableFamily Γ R (Π i ∈ s, α i)) where
  toFun a := Finset.prod s fun i => if h : i ∈ s then (t i) (a i h) else 1
  isPWO_iUnion_support' := pi_PWO_iUnion_support s α fun i => (t i).isPWO_iUnion_support
  finite_co_support' g :=
    pi_finite_co_support s α g (fun i => (t i).isPWO_iUnion_support)
      (fun i g' => (t i).finite_co_support g')

@[simp]
theorem cons_pi_prod_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : (i : σ) → i ∈ cons a s has → α i) : (consPiProd α has f).1 = f a (mem_cons_self a s) :=
  rfl

@[simp]
theorem cons_pi_prod_not_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : (i : σ) → i ∈ cons a s has → α i) :
    (consPiProd α has f).2 = fun i hi => f i (mem_cons_of_mem hi) :=
  rfl

open Classical in
@[simp]
theorem prod_pi_cons_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : α a × ((i : σ) → i ∈ s → α i)) :
    prodPiCons α has f a (mem_cons_self a s) = f.1 := by
  simp [prodPiCons]

open Classical in
theorem piFamily_cons (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) {a : σ} (has : a ∉ s) :
    Equiv (consPiProdEquiv α has) (PiFamily (cons a s has) α t) = mul (t a) (PiFamily s α t) := by
  ext1 _
  simp only [consPiProdEquiv, Equiv_toFun, Equiv.coe_fn_symm_mk, PiFamily_toFun, mem_cons,
    prod_cons, true_or, ↓reduceDIte, prod_pi_cons_mem, mul_toFun]
  congr 1
  refine prod_congr rfl ?_
  intro i hi
  rw [dif_pos hi, dif_pos (Or.inr hi)]
  simp [prodPiCons, dif_neg (ne_of_mem_of_not_mem hi has)]

theorem hsum_pi_family (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) :
    (PiFamily s α t).hsum = ∏ i ∈ s, (t i).hsum := by
  induction s using cons_induction with
  | empty =>
    ext g
    simp only [coeff_hsum, PiFamily_toFun, notMem_empty, ↓reduceDIte, prod_const_one, coeff_one,
      prod_empty]
    classical
    refine finsum_eq_single (fun _ ↦ if g = 0 then 1 else 0)
      (fun i hi => False.elim ((List.mem_nil_iff i).mp hi)) ?_
    · intro f hf
      by_contra
      have hhf : f = fun i hi => False.elim ((List.mem_nil_iff i).mp hi) := by
        ext i hi
        exact False.elim ((List.mem_nil_iff i).mp hi)
      apply hf hhf
  | cons a s' has hp =>
    rw [prod_cons, ← hp, ← hsum_mul, ← piFamily_cons, hsum_equiv]

section Fintype

variable [Fintype σ]

open Classical in
theorem pi_PWO_iUnion_support_Fintype {R} [CommSemiring R] (α : σ → Type*)
    {t : Π i : σ, (α i) → HahnSeries Γ R}
    (ht : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO) :
    (⋃ a : (i : σ) → α i, (∏ i, (t i) (a i)).support).IsPWO := by
  induction Finset.univ (α := σ) using cons_induction with
  | empty =>
    simp only [prod_empty]
    refine Set.Subsingleton.isPWO ?_
    by_cases h : Nontrivial R
    · rw [support_one, Set.iUnion_singleton_eq_range]
      intro x hx y hy
      simp_all
    · simp [← @single_zero_one,
        ← subsingleton_iff_zero_eq_one.mpr (not_nontrivial_iff_subsingleton.mp h)]
  | cons a s has hp =>
    refine (isPWO_iUnion_support_prod_mul (ht a) hp).mono ?_
    intro g hg
    simp only [Set.mem_iUnion, mem_support, prod_cons] at hg
    obtain ⟨f, hf⟩ := hg
    simp only [Set.mem_iUnion, mem_support, ne_eq, Prod.exists]
    use f a, fun i => f i

open Classical in
/-- The equivalence between a pi type over a fintype and a pi type on `univ`. -/
@[simps]
def univ_equiv (α : σ → Type*) :
    ((i : σ) → α i) ≃ ((i : σ) → i ∈ Finset.univ → α i) where
  toFun a := fun i _ ↦ a i
  invFun a := fun i ↦ a i (Finset.mem_univ i)
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open Classical in
theorem univ_equiv_Family {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} (a : (i : σ) → α i) :
    a ∈ {a : (i : σ) → α i | (∏ i, (t i) (a i)).coeff g ≠ 0} ↔
      univ_equiv α a ∈ {a : (i : σ) → i ∈ Finset.univ → α i |
        (∏ i, (t i) (a i (Finset.mem_univ i))).coeff g ≠ 0} := by
  simp_all

/-- The equivalence between a pi-parametrized family and the corresponding finset-parametrized
family. -/
def univ_equiv_Hahn {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} :
    {a : (i : σ) → α i | (∏ i, (t i) (a i)).coeff g ≠ 0} ≃
    {a : (i : σ) → i ∈ Finset.univ → α i | (∏ i, (t i) (a i (Finset.mem_univ i))).coeff g ≠ 0} where
  toFun a := ⟨univ_equiv α a, (univ_equiv_Family α g a).mp (Subtype.coe_prop a)⟩
  invFun a := ⟨(univ_equiv α).symm a, (univ_equiv_Family α g _).mpr (by simp)⟩
  left_inv a := by simp
  right_inv a := by simp
/-!
open Classical in
/-- A summable family made from pointwise multiplication along a finite collection of summable
families. -/
@[simps]
def PiFamily' {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) : (SummableFamily Γ R (Π i, α i)) where
  toFun a := ∏ i, (t i) (a i)
  isPWO_iUnion_support' := pi_PWO_iUnion_support' α fun i => (t i).isPWO_iUnion_support
  finite_co_support' g :=
    pi_finite_co_support Finset.univ α g (fun i => (t i).isPWO_iUnion_support)
      (fun i g' => (t i).finite_co_support g')
-/
end Fintype

end Semiring

end HahnSeries.SummableFamily

end Summable

section HEval

open Finset

theorem sum_eq_top [AddCommMonoid Γ] (s : Finset σ) (f : σ → WithTop Γ)
    (h : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  induction s using cons_induction with
  | empty => simp_all only [notMem_empty, false_and, exists_false]
  | cons i s his ih =>
    obtain ⟨j, hj⟩ := h
    by_cases hjs : j ∈ s
    · simp only [sum_cons, WithTop.add_eq_top]
      exact Or.inr <| ih <| Exists.intro j ⟨hjs, hj.2⟩
    · classical
      have hij : j = i := eq_of_mem_insert_of_notMem (cons_eq_insert i s his ▸ hj.1) hjs
      rw [sum_cons, ← hij, hj.2, WithTop.add_eq_top]
      exact Or.inl rfl
-- #find_home! sum_eq_top --[Mathlib.Algebra.BigOperators.Group.Finset]

theorem add_ne_top [AddCommMonoid Γ] {x y : WithTop Γ} (hx : x ≠ ⊤)
    (hy : y ≠ ⊤) : x + y ≠ ⊤ := by
  by_contra h
  rw [WithTop.add_eq_top] at h
  simp_all only [ne_eq, or_self]
--#find_home! add_ne_top --[Mathlib.Algebra.Order.Monoid.Unbundled.WithTop]

theorem add_untop [AddCommMonoid Γ] {x y : WithTop Γ} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (x + y).untop (add_ne_top hx hy) = x.untop hx + y.untop hy :=
  (WithTop.untop_eq_iff (add_ne_top hx hy)).mpr (by simp)
--#find_home! add_untop --[Mathlib.Algebra.Order.Monoid.Unbundled.WithTop]

theorem sum_untop [AddCommMonoid Γ] (s : Finset σ) {f : σ → WithTop Γ}
    (h : ∀ i, ¬ f i = ⊤) (hs : ¬∑ i ∈ s, f i = ⊤) :
    (∑ i ∈ s, f i).untop hs = ∑ i ∈ s, ((f i).untop (h i)) := by
  induction s using cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [sum_cons]
    rw [sum_cons, WithTop.add_eq_top, not_or] at hs
    rw [add_untop (h i) hs.2]
    exact congrArg (HAdd.hAdd ((f i).untop (h i))) (ih hs.right)
--#find_home! sum_untop --[Mathlib.Algebra.BigOperators.Group.Finset]

namespace HahnSeries

namespace SummableFamily

theorem support_prod_subset_add_support [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R) (s : Finset σ) :
    haveI : AddCommMonoid (Set Γ) := Set.addCommMonoid
    (∏ i ∈ s, (x i)).support ⊆ ∑ i ∈ s, (x i).support := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, ← single_zero_one]
    exact support_single_subset
  · intros _ _ _ his _ hg
    simp_all only [prod_cons, mem_support, ne_eq, sum_cons]
    exact support_mul_subset.trans (Set.add_subset_add (fun ⦃a⦄ a ↦ a) his) hg

theorem support_MVpow_subset_closure_support [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    (∏ i ∈ x.support, (x i) ^ (n i)).support ⊆ AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine Finset.cons_induction ?_ ?_ x.support
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

theorem support_MVpow_subset_closure [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] {σ : Type*} (s : Finset σ) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    (∏ i ∈ s, (x i) ^ (n i)).support ⊆ AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

theorem isPWO_iUnion_support_MVpow_support [LinearOrder Γ] [AddCommMonoid Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (∏ i ∈ x.support, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono (Set.IsPWO.addSubmonoid_closure ?_ ?_)
    (Set.iUnion_subset fun n => support_MVpow_subset_closure x.support x n)
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · have h : ⋃ i, (x i).support =
        (⋃ i ∈ x.support, (x i).support) ∪ (⋃ i ∉ x.support, (x i).support) := by
      classical
      simp_rw [← Set.iUnion_ite, ite_id (x _).support]
    rw [h, Set.isPWO_union]
    constructor
    · exact (isPWO_bUnion x.support).mpr fun i _ ↦ isPWO_support (x i)
    · rw [show (⋃ i, ⋃ (_ : i ∉ x.support), (x i).support) = ∅ by simp_all]
      exact Set.isPWO_empty

theorem isPWO_iUnion_support_MVpow [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommSemiring R] {σ : Type*} [Fintype σ] (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (∏ i, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono ?_ (Set.iUnion_subset fun n => support_MVpow_subset_closure Finset.univ x n)
  refine Set.IsPWO.addSubmonoid_closure ?_ ?_
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · rw [show ⋃ i, (x i).support = ⋃ i ∈ univ, (x i).support by simp]
    exact (isPWO_bUnion univ).mpr fun i _ => isPWO_support (x i)

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

omit [IsOrderedCancelAddMonoid Γ] in
lemma supp_eq_univ_of_pos (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Set.univ (α := σ) := by
  have hy₁ : ∀ i : σ, y i ≠ 0 := fun i => ne_zero_of_order_ne (ne_of_gt (hy i))
  exact Set.eq_univ_of_univ_subset fun i _ => by simp_all

/-- A finsupp whose every element has positive order has fintype source. -/
@[reducible]
noncomputable def Fintype_of_pos_order (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : Fintype σ := by
  refine Set.fintypeOfFiniteUniv ?_
  rw [← supp_eq_univ_of_pos σ y hy]
  exact finite_toSet y.support

omit [IsOrderedCancelAddMonoid Γ] in
lemma supp_eq_univ_of_pos_fintype (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Finset.univ (α := σ) :=
  eq_univ_of_forall fun i => Finsupp.mem_support_iff.mpr (ne_zero_of_order_ne (ne_of_gt (hy i)))

variable [CommRing V] [Algebra R V]

theorem powerSeriesFamily_ext (x : HahnSeries Γ V) (f g : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily x g ↔
      ∀ n, powerSeriesFamily x f n = powerSeriesFamily x g n :=
  SummableFamily.ext_iff

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem coeff_sum {α} (s : Finset α) (f : α → HahnSeries Γ R) (g : Γ) :
    (Finset.sum s f).coeff g = Finset.sum s (fun i => (f i).coeff g) :=
  cons_induction_on s (by simp) fun i t hit hc => by rw [sum_cons, sum_cons, coeff_add, hc]

theorem finsum_prod {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), ∑ᶠ (j : ℕ),  f (i, j) = ∑ᶠ (i : ℕ × ℕ), f i :=
  Eq.symm (finsum_curry (fun ab ↦ f ab) (Finsupp.hasFiniteSupport f))

theorem finsum_antidiagonal_prod [AddCommMonoid α] [HasAntidiagonal α] (f : α × α →₀ R) :
    ∑ᶠ (i : α), (∑ j ∈ antidiagonal i, f j) =
    ∑ᶠ (i : α × α), f i := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := f.support) (fun i _ => by simp_all),
    finsum_eq_sum_of_support_subset _ (s := (f.support.image fun i => i.1 + i.2)) ?_, sum_sigma']
  · refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
    · exact fun x _ y _ hxy => by simp_all
    · intro x hx
      simp_all only [mem_coe, Finsupp.mem_support_iff, ne_eq, coe_sigma, coe_image,
        Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_antidiagonal, and_true]
      use x.1, x.2
    · intro x hx h
      simp_all only [mem_sigma, mem_image, Finsupp.mem_support_iff, ne_eq, Prod.exists,
        mem_antidiagonal, Set.mem_image, mem_coe, not_exists, not_and]
      have h0 : ∀ i j : α, ⟨i + j, (i, j)⟩ = x → f (i, j) = 0 := by
        intro i j
        contrapose!
        exact h i j
      refine h0 x.snd.1 x.snd.2 ?_
      simp_all only [Prod.mk.eta, Sigma.eta]
    · exact fun x _ => rfl
  · intro x hx
    simp_all only [Function.mem_support, ne_eq, coe_image, Set.mem_image, mem_coe,
      Finsupp.mem_support_iff, Prod.exists]
    have h1 := exists_ne_zero_of_sum_ne_zero hx
    use h1.choose.1, h1.choose.2
    refine ⟨h1.choose_spec.2, ?_⟩
    · rw [← @mem_antidiagonal]
      exact h1.choose_spec.1

--#find_home! finsum_antidiagonal_prod --[Mathlib.RingTheory.Adjoin.Basic]

end PowerSeriesFamily

section MVpowers


variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] [CommRing V]
  [Algebra R V] {x : HahnSeries Γ V} (hx : 0 < x.orderTop)

-- use Finsupp.sumFinsuppAddEquivProdFinsupp and maybe Finsupp.lsingle
-- see also Finsupp.restrictSupportEquiv

/-- An equiv between finsupp and maps from a finset. -/
noncomputable def equiv_map_on_finset_finsupp (s : Finset σ) :
    ((i : σ) → i ∈ s → ℕ) ≃ ({i // i ∈ s} →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i.1 i.2)
  invFun f := fun i hi => (Finsupp.equivFunOnFinite f) ⟨i, hi⟩
  left_inv := congrFun rfl
  right_inv f := by simp

/-- The equivalence between maps on a finite totality and finitely supported functions. -/
noncomputable def equiv_map_on_fintype_finsupp [Fintype σ] :
    ((i : σ) → i ∈ Finset.univ → ℕ) ≃ (σ →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i (mem_univ i))
  invFun f := fun i _ => (Finsupp.equivFunOnFinite f) i
  left_inv f := by simp
  right_inv f := by simp

/-- A multivariable family given by all possible unit-coefficient monomials -/
noncomputable def mvPowers [Fintype σ] (y : σ →₀ HahnSeries Γ V) :
    SummableFamily Γ V (σ →₀ ℕ) :=
  Equiv equiv_map_on_fintype_finsupp (PiFamily Finset.univ (fun _ => ℕ)
    (fun i => powers (y i)))

@[simp]
theorem mvPowers_apply {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (n : σ →₀ ℕ) :
    (mvPowers y) n = ∏ i, y i ^ n i := by
  simp [mvPowers, equiv_map_on_fintype_finsupp, hy]

open Classical in
theorem mvpow_finite_co_support {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (g : Γ) :
    {a : (σ →₀ ℕ) | (∏ i, y i ^ a i).coeff g ≠ 0}.Finite := by
  have h : ∀ a : (σ →₀ ℕ), (∏ i : σ, y i ^ a i) = ∏ x : σ,
      if _ : x ∈ univ then y x ^ a x else 1 :=
    fun a => by simp
  suffices {a : ((i : σ) → i ∈ univ → ℕ) | ((fun b => ∏ x : σ,
      if h : x ∈ univ then y x ^ b x h else 1) a).coeff g ≠ 0}.Finite from by
    simp_rw [h]
    refine Set.Finite.of_surjOn (fun a => Finsupp.onFinset univ (fun i => a i (mem_univ i))
      (fun i _ ↦ mem_univ i)) (fun a ha => ?_) this
    simp_all only [dite_eq_ite, ite_true, implies_true, dite_true, mem_univ, ne_eq,
      Set.mem_setOf_eq, Set.mem_image]
    use fun i _ => a i
    exact ⟨ha, by ext; simp⟩
  exact pi_finite_co_support Finset.univ _ g (fun i => isPWO_iUnion_support_powers
    (zero_le_orderTop_iff.mp <| le_of_lt (hy i)))
    (fun i g => by simp only [pow_finite_co_support (hy i) g])

/-- A summable family given by substituting a multivariable power series into positive order
elements. -/
noncomputable abbrev mvPowerSeriesFamily [Fintype σ] (y : σ →₀ HahnSeries Γ V)
    (f : MvPowerSeries σ R) :
    SummableFamily Γ V (σ →₀ ℕ) :=
  smulFamily (fun n => MvPowerSeries.coeff n f) (mvPowers y)

theorem mvPowerSeriesFamily_toFun [Fintype σ] (y : σ →₀ HahnSeries Γ V)
    (hy : ∀ i, 0 < (y i).orderTop) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    mvPowerSeriesFamily y f n =
      (MvPowerSeries.coeff n f) • ∏ i, (y i) ^ (n i) := by
  simp [hy]

theorem mvPowerSeriesFamilyAdd [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (f g : MvPowerSeries σ R) :
    mvPowerSeriesFamily y (f + g) = mvPowerSeriesFamily y f + mvPowerSeriesFamily y g := by
  ext1 n
  simp [add_smul]

theorem mvPowerSeriesFamilySMul [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (r : R) (f : MvPowerSeries σ R) :
    mvPowerSeriesFamily y (r • f) =
      (HahnSeries.single (0 : Γ) r) • (mvPowerSeriesFamily y f) := by
  ext1 n
  simp only [smulFamily_toFun, map_smul, smul_eq_mul, smul_apply, HahnModule.of_smul,
    HahnModule.single_zero_smul_eq_smul, HahnModule.of_symm_smul, Equiv.symm_apply_apply, mul_smul]

/-!
open Classical in
theorem mvPowerSeriesFamily_supp_subset {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (a b : MvPowerSeries σ R) (g : Γ) :
    ((mvPowerSeriesFamily y hy (a * b)).coeff g).support ⊆
    (((mvPowerSeriesFamily y hy a).mul (mvPowerSeriesFamily y hy b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, mvPowerSeriesFamily_toFun, coeff_smul, smul_eq_mul, mul_toFun,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset, coe_image,
    Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image, Function.mem_support,
    Prod.exists]
  intro n hn
  simp_rw [MvPowerSeries.coeff_mul, ← ne_eq, sum_smul, mul_smul] at hn
  have he : ∃p ∈ antidiagonal n, ¬((MvPowerSeries.coeff R p.1) a •
      (MvPowerSeries.coeff R p.2) b • ((mvPowers y hy) n).coeff g) = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← mul_assoc, mul_comm ((MvPowerSeries.coeff R he.choose.2) b)]
  simp_rw [mvPowers_apply, ← prod_mul_distrib, ← pow_add]
  convert he.choose_spec.2
  · exact Eq.symm (mvPowers_apply y hy n)
  · exact Eq.symm (mvPowers_apply y hy n)
  · simp [mvPowers, equiv_map_on_fintype_finsupp]
    congr 1
    funext i
    have h : he.choose.1 i + he.choose.2 i = n i := by
      rw [← Finsupp.add_apply, mem_antidiagonal.mp he.choose_spec.1]
    congr
    convert h
    · exact Iff.symm mem_antidiagonal
    · exact Eq.symm (mvPowers_apply y hy n)
    · exact Iff.symm mem_antidiagonal
    · exact Eq.symm (mvPowers_apply y hy n)
theorem prod_mul {σ M : Type*} [Fintype σ] [CommMonoid M] (i : (σ →₀ ℕ) × (σ →₀ ℕ)) (y : σ → M) :
    (∏ i_1 : σ, y i_1 ^ i.1 i_1) * ∏ i_1 : σ, y i_1 ^ i.2 i_1 = ∏ x : σ, y x ^ (i.1 + i.2) x := by
  rw [← prod_mul_distrib, prod_congr rfl]
  intro _ _
  rw [Finsupp.add_apply, pow_add]
theorem mvPowerSeries_family_prod_eq_family_mul {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (a b : MvPowerSeries σ R) :
    (mvPowerSeriesFamily y hy (a * b)).hsum =
    ((mvPowerSeriesFamily y hy a).mul (mvPowerSeriesFamily y hy b)).hsum := by
  ext g
  classical
  simp only [mvPowerSeriesFamily_toFun, MvPowerSeries.coeff_mul, Finset.sum_smul,
    ← Finset.sum_product, coeff_hsum_eq_sum, mul_toFun, mvPowers_apply]
  rw [sum_subset (mvPowerSeriesFamily_supp_subset y hy a b g)]
  · rw [← HahnSeries.sum_coeff, sum_sigma', sum_coeff]
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
    · intro ij _ kl _
      simp_all
    · intro ij hij
      simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul,
        Set.Finite.coe_toFinset, Function.mem_support, ne_eq, coe_sigma, coe_image,
        Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe, mem_antidiagonal, and_true]
      use ij.1, ij.2
    · intro i hi his
      simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul, mem_sigma,
        mem_image, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists,
        mem_antidiagonal, Set.Finite.coe_toFinset, Set.mem_image, not_exists, not_and]
      have hisc : ∀ j k : σ →₀ ℕ, ⟨j + k, (j, k)⟩ = i → (MvPowerSeries.coeff R k) b *
          ((MvPowerSeries.coeff R j) a * ((∏ p, y p ^ j p) * (∏ q, y q ^ k q)).coeff g) = 0 := by
        intro m n
        contrapose!
        exact his m n
      rw [mul_comm ((MvPowerSeries.coeff R i.snd.1) a), ← hi.2, mul_assoc]
      have hp : ∀ j k : σ →₀ ℕ, ∏ i_1 : σ, y i_1 ^ (j + k) i_1 =
          (∏ i' : σ, y i' ^ j i') * ∏ j' : σ, y j' ^ k j' := by
        intro j k
        rw [prod_mul (j, k)]
      rw [hp]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
    · intro i _
      simp only
      rw [smul_mul_smul_comm]
      congr 2
      exact prod_mul i y
  · intro i hi his
    simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul, mem_image,
      Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, Decidable.not_not,
      HahnSeries.sum_coeff]
    rw [MvPowerSeries.coeff_mul, sum_mul] at his
    exact his
-/

end MVpowers

end SummableFamily

end HahnSeries

namespace PowerSeries
open HahnSeries SummableFamily
variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : R⟦Γ⟧)

theorem heval_of_orderTop_not_pos (hx : ¬ 0 < x.orderTop) (a : PowerSeries R) :
    heval x a = constantCoeff a • 1 := by
  simp [powerSeriesFamily_of_not_orderTop_pos hx, powerSeriesFamily_hsum_zero] --2nd should be simp

end PowerSeries

namespace MvPowerSeries

open HahnSeries SummableFamily

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] {σ : Type*}
  [Fintype σ] (y : σ →₀ HahnSeries Γ R) (hy : ∀ i, 0 < (y i).orderTop)
/-!
/-- The `R`-algebra homomorphism from `R[[X₁,…,Xₙ]]` to `HahnSeries Γ R` given by sending each power
series variable `Xᵢ` to a positive order element. -/
@[simps]
def heval {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R) :
    MvPowerSeries σ R →ₐ[R] HahnSeries Γ R where
  toFun f := (mvPowerSeriesFamily y f).hsum
  map_one' := by
    classical
    simp only [hsum, mvPowerSeriesFamily_toFun, MvPowerSeries.coeff_one, ite_smul, one_smul,
      zero_smul, mvPowers_apply]
    ext g
    simp_rw [finsum_eq_single (fun i =>
      (if i = 0 then ∏ i_1 : σ, (if 0 < (y i_1).orderTop then y i_1 else 0) ^ i i_1 else 0).coeff g)
      (0 : σ →₀ ℕ) (fun n hn => by simp_all)]
    rw [if_true, Fintype.prod_eq_one (fun i_1 ↦
      (if 0 < (y i_1).orderTop then y i_1 else 0) ^ (0 : σ →₀ ℕ) i_1) (congrFun rfl)]
  map_mul' a b := by
    simp only [← hsum_family_mul]
    exact mvPowerSeries_family_prod_eq_family_mul y hy a b
  map_zero' := by
    simp only [hsum, mvPowerSeriesFamily_toFun, map_zero, mvPowers_apply, zero_smul, coeff_zero,
      finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    ext g
    simp only [coeff_hsum, map_add, mvPowers_apply, coeff_smul,
      smul_eq_mul, add_mul, coeff_add', Pi.add_apply]
    rw [← finsum_add_distrib (finite_co_support (mvPowerSeriesFamily y a) g)
      (finite_co_support (mvPowerSeriesFamily y b) g)]
    exact finsum_congr fun s => by rw [mvPowerSeriesFamilyAdd, add_apply, coeff_add]
  commutes' r := by
    simp only [MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
      algebraMap_apply, C_apply]
    ext g
    classical
    simp only [coeff_hsum, mvPowerSeriesFamily_toFun, mvPowers_apply, coeff_smul, smul_eq_mul]
    rw [finsum_eq_single _ 0 (fun s hs => by simp [hs, MvPowerSeries.coeff_C])]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one']
theorem heval_mul {a b : MvPowerSeries σ R} :
    heval y (a * b) = (heval y a) * heval y b :=
  map_mul (heval y) a b
theorem heval_unit (u : (MvPowerSeries σ R)ˣ) : IsUnit (heval y u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval y hy u.inv
  rw [← heval_mul, Units.val_inv, map_one]
theorem heval_coeff (f : MvPowerSeries σ R) (g : Γ) :
    (heval y f).coeff g = ∑ᶠ n, ((mvPowerSeriesFamily y f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl
theorem heval_coeff_zero (f : MvPowerSeries σ R) :
    (heval y f).coeff 0 = MvPowerSeries.constantCoeff σ R f := by
  rw [heval_coeff, finsum_eq_single (fun n => ((mvPowerSeriesFamily y f).coeff 0) n) 0,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp_all
  · intro n hn
    simp_all only [ne_eq, coeff_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply, coeff_smul,
      smul_eq_mul]
    refine mul_eq_zero_of_right ((MvPowerSeries.coeff R n) f) (coeff_eq_zero_of_lt_orderTop ?_)
    refine lt_of_lt_of_le ?_ (sum_orderTop_le_orderTop_prod _)
    by_cases h : ∑ i, (y i ^ n i).orderTop = ⊤
    · simp [h]
    · have hi : ∀ i, ¬(y i ^ n i).orderTop = ⊤ := by
        intro i
        contrapose h
        simp_all only [Decidable.not_not]
        exact sum_eq_top univ _ <| Exists.intro i ⟨mem_univ i, h⟩
      refine (WithTop.lt_untop_iff h).mp ?_
      rw [sum_untop univ hi h]
      rw [Finsupp.ext_iff, Mathlib.Tactic.PushNeg.not_forall_eq] at hn
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hn
      refine sum_pos' ?_ ?_
      · intro i _
        by_cases hni : n i = 0
        · rw [WithTop.le_untop_iff, hni, pow_zero]
          by_cases hz : (1 : HahnSeries Γ R) = 0
          · simp [hz]
          · rw [WithTop.coe_zero, zero_le_orderTop_iff, order_one]
        · rw [WithTop.le_untop_iff]
          refine LE.le.trans ?_ orderTop_nsmul_le_orderTop_pow
          rw [WithTop.coe_zero]
          exact nsmul_nonneg (le_of_lt (hy i)) (n i)
      · obtain ⟨i, hni⟩ := hn
        use i
        constructor
        · exact mem_univ i
        · rw [WithTop.lt_untop_iff]
          refine lt_of_lt_of_le ?_ orderTop_nsmul_le_orderTop_pow
          rw [WithTop.coe_zero]
          exact (nsmul_pos_iff hni).mpr (hy i)
-/
end MvPowerSeries

end HEval

section Binomial

namespace MonoidAlgebra

variable [Ring R]

/-- A unit monomial minus a unit monomial. -/
noncomputable def single_sub_single (g g' : Γ) : MonoidAlgebra R Γ := single g 1 - single g' 1

@[simp]
theorem single_sub_single_of_subsingleton [Subsingleton R] (g g' : Γ) :
    single_sub_single g g' = (0 : MonoidAlgebra R Γ) :=
  Subsingleton.eq_zero (single_sub_single g g')

@[simp]
theorem single_sub_single_eq_zero_iff [Nontrivial R] (g g' : Γ) :
    single_sub_single g g' = (0 : MonoidAlgebra R Γ) ↔ g = g' := by
  refine ⟨?_, fun h ↦ (by simp [single_sub_single, h])⟩
  intro h
  by_contra hgg'
  rw [single_sub_single, sub_eq_zero, MonoidAlgebra.ext_iff] at h
  specialize h g
  classical
  rw [single_apply, single_apply] at h
  simp [Ne.symm hgg'] at h

theorem single_sub_single_neg (g g' : Γ) :
    - single_sub_single g g' (R := R) = single_sub_single g' g := by
  simp [single_sub_single]

open Finset in
theorem single_sub_single_pow [CommMonoid Γ] (g g' : Γ) (n : ℕ) :
    (single_sub_single g g' (R := R)) ^ n = ∑ i ∈ antidiagonal n,
      Int.negOnePow (i.2) • n.choose (i.1) • single (g ^ (i.1) * g' ^ i.2) 1 := by
  rw [single_sub_single, Ring.sub_eq_add_neg, Commute.add_pow']
  · refine sum_congr rfl ?_
    intro i hi
    rw [← Int.negOnePow_smul_pow, mul_smul_comm, single_pow, one_pow, single_pow, single_mul_single,
      one_pow, one_mul, smul_comm]
  · exact Commute.neg_right (single_commute_single (Commute.all g g') rfl)

end MonoidAlgebra

namespace HahnSeries

section BinomialPow

variable (A : Type*) [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R] [Module R Γ] [CommRing A] [Algebra R A]

theorem pos_orderTop_single_sub {g g' : Γ} (h : g < g') (a : A) :
    0 < (single (g' - g) a).orderTop := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [orderTop_single ha, WithTop.coe_pos]
    exact sub_pos.mpr h
--#find_home! pos_orderTop_single_sub --[Mathlib.RingTheory.HahnSeries.Multiplication]

/-- A Hahn series formally expanding `(X g - X g') ^ r` where `r` is an element of a binomial ring.
-/
noncomputable def binomialPow (g g' : Γ) (r : R) : HahnSeries Γ A :=
  single (r • g) (1 : A) *
    (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r))

theorem binomialPow_apply (g g' : Γ) (r : R) :
    binomialPow A g g' r = single (r • g) 1 *
      (PowerSeries.heval ((single (g' - g)) (-1 : A)) (PowerSeries.binomialSeries A r)) :=
  rfl

theorem binomialPow_apply_of_not_gt {g g' : Γ} (h : ¬ g < g') (r : R) :
    binomialPow A g g' r = single (r • g) (1 : A) := by
  cases subsingleton_or_nontrivial A
  · have _ : Subsingleton (HahnSeries Γ A) := instSubsingleton
    exact Subsingleton.elim _ _
  · have : ¬ 0 < (single (g' - g) (-1 : A)).orderTop := by
      rw [orderTop_single (neg_ne_zero.mpr one_ne_zero), WithTop.coe_pos, sub_pos]
      exact h
    rw [binomialPow_apply, PowerSeries.heval_of_orderTop_not_pos _ this]
    simp

@[simp]
theorem binomialPow_zero {g g' : Γ} :
    binomialPow A g g' (0 : R) = 1 := by
  by_cases h : g < g'
  · rw [binomialPow_apply, zero_smul, single_zero_one, one_mul, PowerSeries.binomialSeries_zero,
      OneHomClass.map_one]
  · simp [binomialPow_apply_of_not_gt A h (0 : R)]

@[simp]
theorem binomialPow_add {g g' : Γ} (r r' : R) :
    binomialPow A g g' r * binomialPow A g g' r' =
      binomialPow A g g' (r + r') := by
  simp only [binomialPow, PowerSeries.binomialSeries_add, PowerSeries.heval_mul, add_smul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, single_mul_single, mul_one, add_comm, ← mul_assoc]

theorem binomialPow_one {g g' : Γ} (h : g < g') :
    binomialPow A g g' (Nat.cast (R := R) 1) = ((single g) (1 : A) - (single g') 1) := by
  rw [binomialPow_apply, PowerSeries.binomialSeries_nat 1, pow_one, map_add,
    PowerSeries.heval_X _ (pos_orderTop_single_sub A h (-1)), Nat.cast_one, one_smul,
    show (1 : PowerSeries A) = PowerSeries.C 1 from (RingHom.map_one (PowerSeries.C)).symm,
    PowerSeries.heval_C, one_smul, mul_add, mul_one, single_mul_single, one_mul, single_neg,
    add_sub_cancel, sub_eq_add_neg]

/-needs new Mathlib
theorem ofAddMonoidAlgebra_single_sub_single {g g' : Γ} (h : g < g') :
    ofAddMonoidAlgebra (AddMonoidAlgebra.single g (1 : A) - AddMonoidAlgebra.single g' 1) =
      binomialPow A g g' (Nat.cast (R := R) 1) := by
  rw [binomialPow_one A h, map_sub]
  simp
-/

theorem binomialPow_nat {g g' : Γ} (h : g < g') (n : ℕ) :
    binomialPow A g g' (n : R) = ((single g (1 : A)) - single g' 1) ^ n := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero, map_one, binomialPow_apply]
  | succ n ih =>
    rw [Nat.cast_add, ← binomialPow_add, _root_.pow_add, ih, binomialPow_one A h, pow_one]

theorem binomialPow_one_add {g₀ g₁ g₂ : Γ} (h₀₁ : g₀ < g₁) (h₁₂ : g₁ < g₂) :
    binomialPow A g₀ g₁ (Nat.cast (R := R) 1) + binomialPow A g₁ g₂ (Nat.cast (R := R) 1) =
      binomialPow A g₀ g₂ (Nat.cast (R := R) 1) := by
  rw [binomialPow_one A h₀₁, binomialPow_one A h₁₂, binomialPow_one A (h₀₁.trans h₁₂),
    sub_add_sub_cancel]

theorem binomialPow_coeff_eq {g g' : Γ} (h : g < g') (r : R) (n : ℕ) :
    (binomialPow A g g' r).coeff (r • g + n • (g' - g)) =
      Int.negOnePow n • Ring.choose r n • 1 := by
  simp only [binomialPow_apply, PowerSeries.heval_apply]
  rw [add_comm, HahnSeries.coeff_single_mul_add, one_mul]
  simp only [SummableFamily.coeff_hsum, SummableFamily.smulFamily_toFun,
    PowerSeries.binomialSeries_coeff, smul_eq_mul, coeff_smul]
  rw [finsum_eq_single _ n, SummableFamily.powers_of_orderTop_pos
    (pos_orderTop_single_sub A h (-1 : A)) n, single_pow, coeff_single_same,
    ← Int.cast_negOnePow_natCast, mul_comm, ← smul_eq_mul]
  · norm_cast
  · intro m hmn
    rw [SummableFamily.powers_of_orderTop_pos (pos_orderTop_single_sub A h (-1 : A)) m, single_pow,
      coeff_single_of_ne, mul_zero]
    obtain h' | h' | h' := lt_trichotomy m n
    · exact ne_of_gt <| nsmul_lt_nsmul_left (sub_pos.mpr h) h'
    · exact (hmn h').elim
    · exact ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) h'

theorem binomialPow_coeff_eq_zero {g g' g'' : Γ} (h : g < g') (r : R)
    (hg'' : ∀ (n : ℕ), ¬r • g + n • (g' - g) = g'') :
    (binomialPow (A := A) g g' r).coeff g'' = 0 := by
  simp only [binomialPow_apply, PowerSeries.heval_apply]
  rw [← sub_add_cancel g'' (r • g), HahnSeries.coeff_single_mul_add, one_mul]
  simp only [SummableFamily.coeff_hsum, SummableFamily.smulFamily_toFun,
    PowerSeries.binomialSeries_coeff, smul_assoc, one_smul, coeff_smul]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro m
  refine smul_eq_zero_of_right (Ring.choose r m) ?_
  rw [SummableFamily.powers_of_orderTop_pos (pos_orderTop_single_sub A h (-1 : A)) m, single_pow,
    coeff_single_of_ne]
  contrapose! hg''
  use m
  rw [sub_eq_iff_eq_add'] at hg''
  rw [hg'']

end BinomialPow

/-! We consider integral powers of binomials with invertible leading term.  Also, we consider more
binomial ring powers of binomials with leading term 1, when the coefficient ring is an algebra over
the binomial ring in question.  Question: how to approach switching to consider locality in vertex
algebras?  -/

section Binomial

theorem pos_addUnit_neg_add [AddMonoid Γ] [LT Γ]
    [CovariantClass Γ Γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1]
    [ContravariantClass Γ Γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x < x_1] {g g' : Γ} (hg : IsAddUnit g)
    (hgg' : g < g') : 0 < hg.addUnit.neg + g' := by
  refine (lt_add_iff_pos_right g).mp ?_
  rw [← add_assoc, AddUnits.neg_eq_val_neg, IsAddUnit.add_val_neg, zero_add]
  exact hgg'

--#find_home pos_addUnit_neg_add --Mathlib.Algebra.Order.Group.Units

theorem one_sub_single_sub_one_orderTop_pos [PartialOrder Γ] [AddCommMonoid Γ] [CommRing R] {g : Γ}
    (hg : 0 < g) (r : R) :
    0 < ((1 - single g r) - 1).orderTop := by
  refine lt_of_lt_of_le (WithTop.coe_pos.mpr hg) ?_
  simp only [sub_sub_cancel_left, orderTop_neg, orderTop_single_le]

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

omit [IsOrderedCancelAddMonoid Γ] in
theorem minus_one_orderTop_pos [Nontrivial R] (x : HahnSeries Γ R) :
    0 < (x - 1).orderTop ↔ x.orderTop = 0 ∧ x.leadingCoeff = 1 := by
  constructor
  · intro hx
    rw [show x = (x - 1) + 1 by exact Eq.symm (sub_add_cancel x 1), add_comm,
      ← orderTop_one (R := R) (Γ := Γ), ← leadingCoeff_one (R := R) (Γ := Γ)]
    constructor
    · exact orderTop_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
    · exact leadingCoeff_add_eq_left (Γ := Γ) (R := R) (orderTop_one (R := R) (Γ := Γ) ▸ hx)
  · intro h
    refine lt_of_le_of_ne (le_of_eq_of_le (by simp_all)
      (min_orderTop_le_orderTop_sub (Γ := Γ) (R := R))) <| Ne.symm <|
      sub_orderTop_ne_of_leadingCoeff_eq h.1 orderTop_one ?_
    rw [h.2, leadingCoeff_one]

/-- The monoid of elements close to 1, i.e., subtracting 1 yields positive `orderTop`. -/
@[simps]
def onePlusPosOrderTop (Γ) (R) [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommRing R] :
    Submonoid (HahnSeries Γ R) where
  carrier := { x : HahnSeries Γ R | 0 < (x - 1).orderTop}
  mul_mem' := by
    intro x y hx hy
    obtain (_|_) := subsingleton_or_nontrivial R
    · simp
    · simp_all only [Set.mem_setOf_eq, minus_one_orderTop_pos]
      have h1 : x.leadingCoeff * y.leadingCoeff = 1 := by rw [hx.2, hy.2, mul_one]
      constructor
      · rw [orderTop_mul_of_ne_zero (h1 ▸ one_ne_zero), hx.1, hy.1, add_zero]
      · rw [leadingCoeff_mul_of_ne_zero (h1 ▸ one_ne_zero), h1]
  one_mem' := by simp

@[simp]
theorem mem_onePlusPosOrderTop_iff (x : HahnSeries Γ R) :
    x ∈ onePlusPosOrderTop Γ R ↔ 0 < (x - 1).orderTop := by
  exact Eq.to_iff rfl

theorem one_plus_single_mem_onePlusPosOrderTop {g : Γ} (hg : 0 < g) (r : R) :
    1 + single g r ∈ onePlusPosOrderTop Γ R := by
  refine (mem_onePlusPosOrderTop_iff _).mpr ?_
  rw [add_sub_cancel_left]
  exact lt_of_lt_of_le (WithTop.coe_pos.mpr hg) orderTop_single_le

theorem isUnit_one_sub_single {g : Γ} (hg : 0 < g) (r : R) : IsUnit (1 - single g r) := by
  refine isUnit_of_orderTop_pos ?_
  rw [sub_sub_cancel_left, orderTop_neg]
  exact lt_of_lt_of_le (WithTop.coe_pos.mpr hg) orderTop_single_le

/-
theorem one_sub_single_npow_coeff {g : Γ} (hg : 0 < g) (r : R) (n k : ℕ) :
    ((1 - single g r) ^ n).coeff (k • g) = (-1) ^ k • Nat.choose n k • r ^ k := by
  rw [← meval_X hg, ← RingHom.map_one (meval hg r), ← RingHom.map_sub, ← RingHom.map_pow]
  by_cases hn : n = 0
  · by_cases hk : k = 0
    · simp [hn, hk]
    · rw [hn, Nat.choose_eq_zero_of_lt (Nat.zero_lt_of_ne_zero hk)]
      have hkg : k • g ≠ 0 • g := fun h => hk (StrictMono.injective (nsmul_left_strictMono hg) h)
      simp_all
  · have hm : (1 : PowerSeries R) - PowerSeries.X = PowerSeries.rescale (-1 : R)
        ((1 : PowerSeries R) + PowerSeries.X) := by
      simp [Mathlib.Tactic.RingNF.add_neg]
    rw [meval_apply_coeff, hm, ← RingHom.map_pow, PowerSeries.coeff_rescale, show 1 +
      PowerSeries.X = Polynomial.coeToPowerSeries.ringHom ((1 : Polynomial R) + Polynomial.X) by
      simp, ← RingHom.map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      Polynomial.coeff_one_add_X_pow R n k, mul_rotate']
    simp
theorem one_sub_single_negSuccPow_coeff {g : Γ} (hg : 0 < g) (r : R) (n k : ℕ) :
    ((isUnit_one_sub_single hg r).unit ^ (Int.negSucc n)).val.coeff (k • g) =
      Nat.choose (n + k) k • r ^ k := by
  have hm : ((isUnit_one_sub_single hg r).unit ^ (Int.negSucc n)).val =
      (meval hg r) (PowerSeries.invOneSubPow n).val := by
    rw [@zpow_negSucc]
    sorry
  sorry
-/
-- theorem one_sub_single_npow_coeff_notin_range

/-- An invertible binomial, i.e., one with invertible leading term. -/
noncomputable def UnitBinomial {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a)
    (b : R) :
    (HahnSeries Γ R)ˣ :=
  (UnitSingle hg ha) *
    IsUnit.unit (isUnit_one_sub_single (pos_addUnit_neg_add hg hgg') (ha.unit.inv * -b))

theorem unitBinomial_eq_single_add_single {g g' : Γ} {hg : IsAddUnit g} {hgg' : g < g'} {a : R}
    {ha : IsUnit a} {b : R} : UnitBinomial hg hgg' ha b = single g a + single g' b := by
  simp only [UnitBinomial, AddUnits.neg_eq_val_neg, Units.inv_eq_val_inv, Units.val_mul,
    val_UnitSingle, IsUnit.unit_spec, mul_sub, mul_one, single_mul_single]
  rw [← add_assoc, IsAddUnit.add_val_neg, zero_add, ← mul_assoc, IsUnit.mul_val_inv, one_mul,
    sub_eq_iff_eq_add, add_assoc, ← single_add, add_neg_cancel, single_eq_zero, add_zero]

theorem orderTop_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R}
    (ha : IsUnit a) (b : R) : (UnitBinomial hg hgg' ha b).val.orderTop = g := by
  rw [unitBinomial_eq_single_add_single, orderTop_add_eq_left, orderTop_single (IsUnit.ne_zero ha)]
  · refine lt_of_lt_of_le ?_ orderTop_single_le
    rw [(orderTop_single (IsUnit.ne_zero ha))]
    exact WithTop.coe_lt_coe.mpr hgg'

theorem order_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hg' : g < g') {a : R}
    (ha : IsUnit a) (b : R) : (UnitBinomial hg hg' ha b).val.order = g := by
  rw [← WithTop.coe_eq_coe, order_eq_orderTop_of_ne_zero (Units.ne_zero (UnitBinomial hg hg' ha b))]
  exact orderTop_unitBinomial hg hg' ha b

theorem leadingCoeff_unitBinomial [Nontrivial R] {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g')
    {a : R} (ha : IsUnit a) (b : R) : (UnitBinomial hg hgg' ha b).val.leadingCoeff = a := by
  rw [leadingCoeff_eq, order_unitBinomial, unitBinomial_eq_single_add_single, coeff_add,
    coeff_single_same, coeff_single_of_ne (ne_of_lt hgg'), add_zero]

--theorem unitBinomial_npow_coeff

-- coefficients of powers - use embDomain_coeff and embDomain_notin_range from Basic

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem orderTop_single_add_single {g g' : Γ} (hgg' : g < g') {a : R} (ha : a ≠ 0) (b : R) :
    (single g a + single g' b).orderTop = g := by
  rw [← orderTop_single ha]
  exact orderTop_add_eq_left (lt_of_eq_of_lt (orderTop_single ha)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le))

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem coeff_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} :
    (single g a + single g' b).coeff g = a := by
  simp_all [ne_of_lt hgg']

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem single_add_single_ne {g g' : Γ} (hgg' : g < g') {a : R} (ha : a ≠ 0) (b : R) :
    single g a + single g' b ≠ 0 :=
  ne_zero_of_coeff_ne_zero (ne_of_eq_of_ne (coeff_single_add_single hgg') ha)

-- Do I need this?
omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem single_add_single_support {g g' : Γ} {a b : R} :
    (single g a + single g' b).support ⊆ {g} ∪ {g'} := by
  refine (support_add_subset _ _).trans ?_
  simp_all only [Set.union_singleton, Set.union_subset_iff]
  refine { left := fun _ hk => Set.mem_insert_of_mem g' (support_single_subset hk), right := ?_ }
  rw [Set.pair_comm]
  refine Set.subset_pair_iff.mpr ?_
  intro k hk
  exact Set.mem_insert_of_mem g (support_single_subset hk)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem leadingCoeff_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).leadingCoeff = a := by
  have hn := single_add_single_ne hgg' ha b
  have ho := orderTop_single_add_single hgg' ha b
  rw [orderTop_of_ne_zero hn, WithTop.coe_eq_coe] at ho
  rw [leadingCoeff_of_ne_zero hn, untop_orderTop_of_ne_zero hn, ho, coeff_single_add_single hgg']

omit [IsOrderedCancelAddMonoid Γ] in
theorem order_single_add_single {g g' : Γ} (hgg' : g < g') {a b : R} (ha : a ≠ 0) :
    (single g a + single g' b).order = g := by
  refine WithTop.coe_eq_coe.mp ?_
  rw [order_eq_orderTop_of_ne_zero (single_add_single_ne hgg' ha b),
    orderTop_single_add_single hgg' ha]
/-!
theorem isUnit_single_add_single {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') (a : Units R)
    (b : R) : IsUnit (single g a.val + single g' b) := by
  by_cases ha : a.val = 0
  · have hz : (0 : R) = 1 :=
      isUnit_zero_iff.mp (Eq.mpr (congrArg (fun h ↦ IsUnit h) ha.symm) a.isUnit)
    rw [← MulAction.one_smul (α := R) ((single g) a.val + (single g') b), ← hz, zero_smul,
      isUnit_zero_iff, ← single_zero_one, ← hz, single_eq_zero]
  · have hlead := (leadingCoeff_single_add_single (b := b) hgg' ha) ▸ Units.isUnit a
    have hord := (order_single_add_single (b := b) hgg' ha) ▸ hg
    exact isUnit_of_isUnit_leadingCoeff_AddUnitOrder (Γ := Γ) (R := R) hlead hord
/-- A binomial Hahn series with unit leading coefficient -/
abbrev UnitBinomial' {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a) (b : R) :
    (HahnSeries Γ R)ˣ :=
  IsUnit.unit (isUnit_single_add_single hg hgg' (IsUnit.unit ha) b)
theorem UnitBinomial_val {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a)
    (b : R) : (UnitBinomial' hg hgg' ha b).val = single g (IsUnit.unit ha).val + single g' b :=
  rfl
theorem UnitBinimial_inv_coeff {g g' : Γ} (hg : IsAddUnit g) (hgg' : g < g') {a : R} (ha : IsUnit a)
    (b : R) : (UnitBinomial hg hgg' ha b).inv = sorry := --hsum
  sorry -- induction, telescoping.
/-- A function for describing coefficients of powers of invertible binomials. -/
def UnitBinomialPow_coeff_aux {a : R} (ha : IsUnit a) (b : R) (n : ℤ) :
    ℕ → R := fun k => (IsUnit.unit ha) ^ (n - k) • b ^ k • Ring.choose n k
-/
end Binomial

section OneSubSingle -- may be superfluous

--theorem xxx [CommRing R] : IsUnit (1 : R) := by exact isUnit_one

-- if k ∈ Monoid.closure g, then ... else 0

variable [LinearOrder Γ] [AddCommMonoid Γ] [CommRing R]

theorem supp_one_sub_single {g : Γ} (r : R) :
    (1 - single g r).support ⊆ {0, g} := by
  rw [sub_eq_add_neg, ← single_neg]
  refine (support_add_subset _ _).trans ?_
  simp only [Set.union_subset_iff]
  constructor
  · by_cases h : Nontrivial R
    · rw [support_one]
      exact Set.singleton_subset_iff.mpr (Set.mem_insert 0 {g})
    · rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at h
      exact Set.compl_subset_compl.mp fun ⦃a⦄ _ a_2 ↦ a_2 (h (coeff 1 a) 0)
  · exact support_single_subset.trans (Set.subset_insert 0 {g})

theorem orderTop_one_sub_single [Nontrivial R] {g : Γ} (hg : 0 < g) (r : R) :
    (1 - single g r).orderTop = 0 := by
  rw [orderTop_sub, orderTop_one]
  rw [orderTop_one]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hg) orderTop_single_le

theorem leadingCoeff_one_sub_single {g : Γ} (hg : 0 < g) (r : R) :
    (1 - single g r).leadingCoeff = 1 := by
  by_cases h : Nontrivial R
  · rw [leadingCoeff_sub, leadingCoeff_one]
    rw [orderTop_one]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hg) orderTop_single_le
  · rw [not_nontrivial_iff_subsingleton] at h
    exact Subsingleton.eq_one (leadingCoeff (1 - (single g) r))

theorem coeff_mul_one_sub_single [IsOrderedCancelAddMonoid Γ] {x : HahnSeries Γ R} {g g' : Γ}
    {r : R} :
    (x * (1 - single g r)).coeff (g + g') = x.coeff (g + g') - r * x.coeff g' := by
  rw [mul_one_sub, coeff_sub, sub_right_inj, add_comm, coeff_mul_single_add, mul_comm]

/-!
theorem support_one_sub_single_npow_zero {g : Γ} {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {0, g} :=
  (support_pow_subset_closure (1 - (single g) r) n).trans
    (AddSubmonoid.closure_mono (supp_one_sub_single r))
theorem support_one_sub_single_npow (g : Γ) (r : R) {n : ℕ} :
    ((1 - single g r) ^ n).support ⊆ AddSubmonoid.closure {g} :=
  support_one_sub_single_npow_zero.trans AddSubmonoid.closure_insert_zero
-/

theorem _root_.AddSubmonoid.neg_not_in_closure [IsOrderedAddMonoid Γ] {g g' : Γ} (hg : 0 ≤ g)
    (hg' : g' < 0) : ¬ g' ∈ AddSubmonoid.closure {g} := by
  rw [AddSubmonoid.mem_closure_singleton, not_exists]
  intro k hk
  have hgk : 0 ≤ k • g :=
    nsmul_nonneg hg k
  rw [hk] at hgk
  exact (lt_self_iff_false 0).mp (lt_of_le_of_lt hgk hg')
--#find_home AddSubmonoid.neg_not_in_closure --[Mathlib.GroupTheory.Submonoid.Membership]

/-!
theorem coeff_one_sub_single_pow_of_neg {g g' : Γ} (hg : 0 ≤ g) (hg' : g' < 0) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff g' = 0 := by
  by_contra h
  rw [← ne_eq, ← mem_support] at h
  apply (AddSubmonoid.neg_not_in_closure hg hg')
    (Set.mem_of_subset_of_mem (support_one_sub_single_npow g r) h)
theorem coeff_one_sub_single_pow_of_add_eq_zero {g g' : Γ} (hg : 0 < g) (hgg' : g + g' = 0) {r : R}
    {n : ℕ} : ((1 - single g r) ^ n).coeff g' = 0 := by
  have hg' : g' < 0 := by
    rw [← hgg']
    exact (lt_add_iff_pos_left g').mpr hg
  exact coeff_one_sub_single_pow_of_neg (le_of_lt hg) hg'
-/
open Finset in
theorem coeff_single_mul_of_no_add [IsOrderedCancelAddMonoid Γ] {x : HahnSeries Γ R} {a b : Γ}
    {r : R} (hab : ¬∃c, c + a = b) :
    (x * single a r).coeff b = 0 := by
  rw [coeff_mul]
  trans Finset.sum ∅ fun (ij : Γ × Γ) => x.coeff ij.fst * (single a r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp_all [mem_addAntidiagonal, coeff_single]
  · exact rfl
--#find_home! coeff_single_mul_of_no_add --[Mathlib.RingTheory.HahnSeries.Multiplication]
/-!
theorem coeff_zero_one_sub_single_npow {g : Γ} (hg : 0 < g) {r : R} {n : ℕ} :
    ((1 - single g r) ^ n).coeff 0 = 1 := by
  by_cases hr : r = 0; · rw [hr, single_eq_zero, sub_zero, one_pow, one_coeff, if_pos rfl]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    by_cases hg' : ∃ g' : Γ, g + g' = 0
    · rw [← hg'.choose_spec, coeff_mul_one_sub_single, hg'.choose_spec, ih, sub_eq_self,
        coeff_one_sub_single_pow_of_add_eq_zero hg hg'.choose_spec, mul_zero]
    · rw [mul_one_sub, coeff_sub, Pi.sub_apply, ih, sub_eq_self, coeff_single_mul_of_no_add]
      simp_all [add_comm]
theorem coeff_one_sub_single_npow {g : Γ} (hg : 0 < g) (r : R) {k n : ℕ}:
    ((1 - single g r) ^ n).coeff (k • g) = (-1) ^ k • (Nat.choose n k) • (r ^ k) := by
  induction' n with n ihn generalizing k
  · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
    induction' k with k
    · simp
    · simp only [Nat.zero_eq, pow_zero, one_coeff, Int.reduceNeg, Nat.choose_zero_succ, zero_smul,
      smul_zero, ite_eq_right_iff]
      have hkg : ¬ Nat.succ k • g = 0 :=
        ne_comm.mp <| ne_of_lt <| (nsmul_pos_iff (Nat.succ_ne_zero k)).mpr hg
      simp_all only [Nat.zero_eq, pow_zero, one_coeff, nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, IsEmpty.forall_iff]
  · induction' k with k
    · simp only [Nat.zero_eq, zero_smul, Int.reduceNeg, pow_zero, Nat.choose_zero_right, one_smul]
      exact coeff_zero_one_sub_single_npow hg
    · have hkg : Nat.succ k • g = g + k • g := by
        rw [← Nat.add_one, add_smul, one_smul, add_comm _ g]
      rw [pow_succ, hkg, coeff_mul_one_sub_single, ← hkg, ihn, ihn, Nat.choose_succ_succ,
        sub_eq_add_neg, neg_mul_eq_mul_neg, pow_succ', pow_succ']
      simp only [Int.reduceNeg, neg_mul, one_mul, nsmul_eq_mul, neg_smul, zsmul_eq_mul,
        Int.cast_pow, Int.cast_neg, Int.cast_one, mul_neg, Nat.cast_add]
      ring_nf
--redundant
theorem zero_lt_orderTop_single {g : Γ} (hg : 0 < g) (r : R) : 0 < (single g r).orderTop :=
  lt_orderTop_single hg
theorem one_sub_single_inv_eq_powers {g : Γ} (hg : 0 < g) {r : R} :
    (IsUnit.unit (isUnit_one_sub_single hg r)).inv =
    (SummableFamily.powers (zero_lt_orderTop_single hg r)).hsum := by
  rw [Units.inv_eq_val_inv, ← Units.mul_eq_one_iff_inv_eq, IsUnit.unit_spec]
  exact SummableFamily.one_sub_self_mul_hsum_powers (zero_lt_orderTop_single hg r)
theorem coeff_one_sub_single_inv {g : Γ} (hg : 0 < g) {r : R} {k : ℕ} :
    (IsUnit.unit (isUnit_one_sub_single hg r)).inv.coeff (k • g) = r ^ k := by
  rw [one_sub_single_inv_eq_powers hg, SummableFamily.coeff_hsum, SummableFamily.coe_powers,
    finsum_eq_single (fun i => ((single g) r ^ i).coeff (k • g)) k]
  · simp only [single_pow, coeff_single_same]
  intro i hi
  rw [single_pow, coeff_single_of_ne]
  rw [ne_iff_lt_or_gt] at hi
  cases hi with
  | inl hik => exact Ne.symm (ne_of_lt (nsmul_lt_nsmul_left hg hik))
  | inr hki => exact ne_of_lt (nsmul_lt_nsmul_left hg hki)
theorem coeff_one_sub_single_neg_pow {g : Γ} (hg : 0 < g) {r : R} {n k : ℕ} :
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ (-n : ℤ)).val.coeff (k • g) =
    Nat.choose (n + k - 1) k • (-r) ^ k := by
  induction' n with n ihn generalizing k
  · simp only [Nat.zero_eq, Nat.cast_zero, neg_zero, zpow_zero, Units.val_one, one_coeff,
      nsmul_eq_mul]
    induction' k with k ihk
    · simp
    · simp only [zero_add, Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.choose_succ_self,
      Nat.cast_zero, zero_mul, ite_eq_right_iff]
      intro hkg
      have h : 0 < Nat.succ k • g := nsmul_pos hg (Ne.symm (NeZero.ne' (Nat.succ k)))
      simp_all
  · simp_all only [nsmul_eq_mul, neg_add_rev, Nat.succ_add_sub_one]
    sorry
-- change this to cases, do induction in separate results?
theorem coeff_one_sub_single_zpow {g : Γ} (hg : 0 < g) {r : R} {n : ℤ} : ∀(k : ℕ),
    ((IsUnit.unit (isUnit_one_sub_single hg r)) ^ n).val.coeff (k • g) =
      (-r) ^ k • Ring.choose n k := by
  refine Int.induction_on n ?_ ?_ ?_
  · exact fun k => by
      rw [zpow_zero]
      by_cases hk : k = 0
      · simp [hk]
      · simp [Ring.choose_zero_pos ℤ k (Nat.pos_iff_ne_zero.mpr hk)]
        have hkg : 0 < k • g := (nsmul_pos_iff hk).mpr hg
        have hkg' : ¬ k • g = 0 := fun h => by simp_all only [lt_self_iff_false]
        exact fun a ↦ (hkg' a).elim
  · intro n h k
    norm_cast
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [coeff_one_sub_single_npow hg, Ring.choose_eq_Nat_choose, smul_algebra_smul_comm,
      ← smul_pow, smul_eq_mul, mul_comm]
    simp
  · intro n h
    simp_all only [zpow_neg, zpow_natCast, smul_eq_mul]
    sorry
-/

end OneSubSingle

end HahnSeries

end Binomial
