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

namespace DirectSum

variable {ι : Type*} {β : ι → Type*} [∀ i, AddCommGroup (β i)]

@[simp]
theorem neg_apply (g : ⨁ i, β i) (i : ι) : (- g) i = - (g i) :=
  rfl

end DirectSum
