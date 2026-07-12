/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Group.NatPowAssoc

/-!
# Integer powers of (-1)
Add a lemma
-/

@[expose] public section

assert_not_exists Field
assert_not_exists TwoSidedIdeal

namespace Int

@[simp]
lemma negOnePow_smul_pow {R : Type*} [Ring R] (x : R) (n : ℕ) :
    negOnePow n • x ^ n = (- x) ^ n := by
  rw [neg_pow, Units.smul_def, coe_negOnePow_natCast, zsmul_eq_mul, cast_pow, cast_neg, cast_one]

end Int
