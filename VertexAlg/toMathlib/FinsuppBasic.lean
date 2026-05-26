/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
remove when merged
-/

@[expose] public section

@[to_additive]
theorem Finsupp.prod_eq_one {α M N : Type*} [Zero M] [CommMonoid N] {f : α →₀ M}
    {g : α → M → N} (h₀ : ∀ b, f b ≠ 0 → g b (f b) = 1) :
    f.prod g = 1 := by
  exact Finset.prod_eq_one fun b hb ↦ h₀ b (Finsupp.mem_support_iff.mp hb)
--#find_home! Finsupp.prod_eq_one --[Mathlib.Algebra.BigOperators.Finsupp.Basic]
