/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Basic

/-!
Add to `Mathlib.Algebra.DirectSum.Basic`
-/

@[expose] public section

variable {B : Type*} [MulOneClass B]

@[to_additive]
lemma ne_one_or_ne_one_of_mul {a b : B} (h : a * b ≠ 1) :
    a ≠ 1 ∨ b ≠ 1 := by
  by_contra; simp_all
