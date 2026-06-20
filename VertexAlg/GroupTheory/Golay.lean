/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Golay-24 code
The Golay-24 code is a subgroup `C` of `(ℤ/2ℤ)²⁴` of order `2¹²`, distinguished by
the following properties:
* It is doubly even, meaning the number of odd coordinates is a multiple of `4`.
* Its minimal weight is `8`, meaning any nonzero element has at least `8` odd coordinates.
These properties uniquely characterize `C` up to permutation of the 24 basis elements.
## Main definitions
* `GroupTheory.Code.Golay24` : The Golay 24 code
## Main results

## TODO

## References
* [J. H. Conway, N. J. S. Sloane, *Sphere Packings, Lattices, and Groups*][conwaysloane19**]]
## Tags
binary code, golay code

-/

@[expose] public section

namespace Projectivization

variable {K : Type*} [Field K]

open scoped LinearAlgebra.Projectivization

/-- Produce a point on the projective line from an element of the field. -/
def ofLine (x : K) : (ℙ K (Fin 2 → K)) :=
  Projectivization.mk K (fun i ↦ if i = 0 then 1 else x)
    (Function.ne_iff.mpr (Exists.intro 0 (by simp)))

end Projectivization

namespace Golay24
open scoped LinearAlgebra.Projectivization
open Projectivization

instance : Fact (Nat.Prime 23) := by decide

/-- The Golay codeword made of quadratic residues mod 23. -/
def Q : Set (ℙ (ZMod 23) (Fin 2 → ZMod 23)) :=
  {ofLine 0, ofLine 1, ofLine 2, ofLine 3, ofLine 4, ofLine 6, ofLine 8, ofLine 9, ofLine 12,
    ofLine 13, ofLine 16, ofLine 18}



end Golay24
