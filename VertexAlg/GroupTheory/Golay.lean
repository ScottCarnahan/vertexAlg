/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
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

lemma ofLine_injective : Function.Injective (ofLine (K := K)) := by
  intro x y h
  simp only [ofLine, Fin.isValue, mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  rw [funext_iff] at ha
  have ha0 := ha 0
  simp only [Fin.isValue, Pi.smul_apply, ↓reduceIte] at ha0
  simpa [Units.val_eq_one.mp <| (eq_one_iff_eq_one_of_mul_eq_one ha0).mpr rfl] using (ha 1).symm

lemma ofLine_apply_ne (x : K) :
    ofLine x ≠ Projectivization.mk K (fun i ↦ if i = 0 then 0 else 1)
      (Function.ne_iff.mpr (by use 1; simp)) := by
  simp [ofLine, mk_eq_mk_iff, funext_iff]
/-
lemma mem_ofLine_or (x : (ℙ K (Fin 2 → K))) :
    x = Projectivization.mk K (fun i ↦ if i = 0 then 0 else 1)
      (Function.ne_iff.mpr (by use 1; simp)) ∨ ∃ y, x = ofLine y := by
  by_cases h : x = Projectivization.mk K (fun i ↦ if i = 0 then 0 else 1)
      (Function.ne_iff.mpr (by use 1; simp))
  · left
    exact h
  · right

    sorry
-/
end Projectivization

namespace Golay24
open scoped LinearAlgebra.Projectivization
open Projectivization

instance instFactPrimeOfNatNat : Fact (Nat.Prime 23) := by decide

instance instFiniteProjectivization : Finite (ℙ (ZMod 23) (Fin 2 → ZMod 23)) :=
  Nat.finite_of_card_ne_zero (by simp [Projectivization.card_of_finrank_two (ZMod 23)
    (Fin 2 → ZMod 23) (Module.finrank_fin_fun (ZMod 23))])

/-- The Projective line is a fintype. (maybe do this computably?) -/
noncomputable local instance instFintypeProjectivization :
    Fintype (ℙ (ZMod 23) (Fin 2 → ZMod 23)) :=
  Fintype.ofFinite (ℙ (ZMod 23) (Fin 2 → ZMod 23))
/-
instance : Compl (Finset (ℙ (ZMod 23) (Fin 2 → ZMod 23))) where
  compl a :=

noncomputable instance : DecidableEq (ℙ (ZMod 23) (Fin 2 → ZMod 23)) := by
  intro a b
  by_cases hi : a = Projectivization.mk (ZMod 23) (fun i ↦ if i = 0 then 0 else 1)
      (Function.ne_iff.mpr (by use 1; simp))
  · by_cases hj : b = Projectivization.mk (ZMod 23) (fun i ↦ if i = 0 then 0 else 1)
      (Function.ne_iff.mpr (by use 1; simp))
    · have : a = b := by rwa [← hj] at hi
      exact isTrue this
    · rw [← hi] at hj
      exact isFalse <| Ne.symm hj
  · sorry
-/
/-- The Golay codeword made of quadratic residues mod 23. -/
def Q : Finset (ℙ (ZMod 23) (Fin 2 → ZMod 23)) :=
  Finset.map ⟨ofLine, ofLine_injective⟩
    ⟨[(0 : ZMod 23), 1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18], by decide⟩

instance instSMulFinsetProjectivization {G K V : Type*} [AddCommGroup V] [DivisionRing K]
    [Module K V] [DecidableEq (ℙ K V)] [Group G] [DistribMulAction G V] [SMulCommClass G K V] :
    SMul G (Finset (ℙ K V)) :=
  Finset.smulFinset

/-- Make an element of a `ZMod 2` vector space from a finite subset. -/
def ofFinset {ι : Type*} [DecidableEq ι] (s : Finset ι) : ι → ZMod 2 :=
  fun a ↦ if a ∈ s then 1 else 0
--#find_home! ofFinset --[Mathlib.Algebra.Field.ZMod]
/-
noncomputable def N (s : Finset (ZMod 23)) : (ℙ (ZMod 23) (Fin 2 → ZMod 23)) → ZMod 2 :=
    ∑ i ∈ s, ofFinset (Matrix.GeneralLinearGroup.upperRightHom i • Qᶜ)
-/


/-- An equivalence from `Fin 24` to the projective line over `ZMod 23`. I could try to make this
more general, but the correct approach is API for hyperplane complements. -/
noncomputable def toFin : Fin 24 ≃ ℙ (ZMod 23) (Fin 2 → ZMod 23) := by
  refine
  Equiv.ofBijective ?_ ?_
  · exact fun i ↦ if i ≠ 23 then ofLine i else Projectivization.mk (ZMod 23)
      (fun i ↦ if i = 0 then 0 else 1) (Function.ne_iff.mpr (by use 1; simp))
  · refine Function.Injective.bijective_of_nat_card_le ?_ ?_
    · intro i j h
      · by_cases hi : i = 23
        · simp only [hi, Fin.isValue, ne_eq, not_true_eq_false, ↓reduceIte, ite_not,
          left_eq_ite_iff] at h
          contrapose! h
          constructor
          · grind
          · exact (ofLine_apply_ne _).symm
        · by_cases hj : j = 23
          · simp only [Fin.isValue, ne_eq, hi, not_false_eq_true, ↓reduceIte, hj,
            not_true_eq_false] at h
            exact ((ofLine_apply_ne (i : ZMod 23)) h).elim
          · have hiv : i.val < 23 := by grind
            have hjv : j.val < 23 := by grind
            simp only [Fin.isValue, ne_eq, hi, not_false_eq_true, ↓reduceIte, hj] at h
            have := ofLine_injective (K := ZMod 23) h
            refine Fin.eq_of_val_eq ?_
            rw [ZMod.natCast_eq_natCast_iff] at this
            grind only [Nat.mod_eq_of_modEq]
    · refine le_of_eq ?_
      rw [Projectivization.card_of_finrank_two (ZMod 23)
        (Fin 2 → ZMod 23) (Module.finrank_fin_fun (ZMod 23))]
      norm_num

end Golay24
