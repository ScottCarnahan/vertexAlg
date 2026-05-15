/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
Extra lemmas about Laurent polynomials
-/

@[expose] public section

-- TODO: linear map from R[T;T⁻¹] ⊗[R] M to M via unit in R.
-- TODO: R-algebra maps from R[T;T⁻¹] to S are in bijection with units in S.

section Algebra

variable {R S : Type*}

open LaurentPolynomial

variable [Semiring R] [Semiring S] [Module R S] [SMulCommClass R S S]
(f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_T_pow_mul (n : ℤ) : (T n * f).smeval x = (x ^ n).val * f.smeval x := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [mul_add, smeval_add, hp, hq, ← mul_add, smeval_add]
  | C_mul_T m r =>
    rw [T_mul, mul_T_assoc, smeval_C_mul_T_n, smeval_C_mul_T_n, add_comm, zpow_add, Units.val_mul,
      ← smul_eq_mul, smul_comm, smul_eq_mul]

@[simp]
theorem smeval_mul [IsScalarTower R S S] : (f * g).smeval x = f.smeval x * g.smeval x := by
  induction f using LaurentPolynomial.induction_on' with
  | add _ _ hp hq=>
    rw [add_mul, smeval_add, smeval_add, hp, hq, add_mul]
  | C_mul_T n r =>
    rw [smeval_C_mul, mul_assoc, smeval_C_mul, smeval_T_pow, smeval_T_pow_mul, smul_mul_assoc]

end Algebra
