/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

@[expose] public section

assert_not_exists Field
assert_not_exists TwoSidedIdeal

namespace Int

@[simp]
lemma negOnePow_smul_pow {R : Type*} [Ring R] (x : R) (n : ℕ) :
    Int.negOnePow n • x ^ n = (- x) ^ n := by
  rw [neg_pow, Units.smul_def, coe_negOnePow_natCast, zsmul_eq_mul, cast_pow, cast_neg, cast_one]

end Int
