/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
Extra lemmas

Do we want to refactor `BinomialRing` to have a `choose` field, with suitable properties? It seems
like it would be a challenge without subtraction.
-/

@[expose] public section

namespace Ring

open Finset

variable {R : Type*}

section

variable [NonAssocRing R] [Pow R ℕ] [BinomialRing R]

-- remove the ' in PR
theorem choose_add_smul_choose' [NatPowAssoc R] (r : R) (n k : ℕ) :
    (Nat.choose (n + k) k) • choose r (n + k) = choose r k * choose (r - k) n := by
  rw [choose_smul_choose _ (Nat.le_add_left k n), Nat.add_sub_cancel]

theorem choose_add_smul_choose_add [NatPowAssoc R] (r : R) (n k : ℕ) :
    (Nat.choose (n + k) k) • choose (r + k) (n + k) = choose (r + k) k * choose r n := by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n), Nat.add_sub_cancel,
    add_sub_cancel_right]
--  rw [choose_add_smul_choose (r + k), add_sub_cancel_right]

theorem choose_natCast_of_lt [NatPowAssoc R] {r : R} {n k : ℕ} (hr : r = k) (hk : k < n) :
    Ring.choose r n = 0 := by
  rw [hr, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero]

end

section

variable [Ring R] [BinomialRing R]

theorem choose_eq_sum_choose_smul {r : R} {n k : ℕ} (h : k ≤ n) :
    choose r n = ∑ m ∈ range (k + 1), k.choose m • choose (r - k) (n - m) := by
  nth_rw 1 [← add_sub_cancel (k : R) r]
  rw [add_choose_eq _ (Nat.cast_commute k (r - ↑k)), Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (sum_of_injOn id (Set.injOn_id (SetLike.coe (range (k + 1)))) ?_ ?_ ?_).symm
  · intro m hm
    simp_all only [coe_range, Set.mem_Iio, Nat.succ_eq_add_one, id_eq]
    exact lt_add_of_lt_add_right hm h
  · intro i hi hk
    simp_all only [Nat.succ_eq_add_one, mem_range, id_eq, Set.image_id', coe_range, Set.mem_Iio,
      not_lt]
    rw [choose_natCast, Nat.choose_eq_zero_iff.mpr hk, Nat.cast_zero, zero_mul]
  · intro i hi
    simp only [nsmul_eq_mul, id_eq, choose_natCast]

theorem choose_mul_choose (r : R) {n k : ℕ} (h : k ≤ n) :
    choose r k * choose r n = ∑ m ∈ range (k+1),
      k.choose m • (n + k - m).choose k • choose r (n + k - m) := by
  rw [choose_eq_sum_choose_smul h, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [choose_smul_choose r (by simp only [mem_range] at hi; omega),
    show n + k - i - k = n - i by omega, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_comm,
    mul_assoc]

theorem choose_mul_choose_multinomial (r : R) {n k : ℕ} (h : k ≤ n) :
    choose r k * choose r n = ∑ m ∈ range (k+1),
      Nat.multinomial Finset.univ ![n - m, k - m, m] • choose r (n + k - m) := by
  rw [choose_mul_choose r h]
  refine sum_congr rfl fun i hi => ?_
  rw [← smul_assoc]
  congr 1
  simp only [mem_range] at hi
  rw [Nat.multinomial_univ_three, show n - i + (k - i) + i = n + k - i by omega, nsmul_eq_mul]
  refine Nat.eq_div_of_mul_eq_right (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero
    (n - i)) (Nat.factorial_ne_zero (k - i))) (Nat.factorial_ne_zero i)) ?_
  norm_cast
  rw [← Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k - i by omega), show
    n + k - i - k = n - i by omega, ← Nat.choose_mul_factorial_mul_factorial (show i ≤ k by omega)]
  ring

/-!
theorem mul_choose (r s:R) (n : ℕ) :
    choose (r*s) n = ∑ j_1 + 2j_2 + \cdots + nj_n = n (fun j ↦ choose (∑ j_i) (j_i) *
      choose s (∑ j_i) * ∏ choose r j_i := by
  sorry

theorem binomial_series_smul [AddCommGroup A] [CommAlgebra R A] [Ideal A I]
    [AdicComplete A I] : [Module R (1+I)] where
  smul r (1+x) := ∑ (i ∈ ℕ) (fun i => (Ring.choose r i) • x^i)
  etc.  -- Need to define I-adically complete CommRing first, and group structure on 1+I.
-/

end

end Ring
