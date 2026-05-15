/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Hom.Monoid
public import VertexAlg.RevLex

/-!
Add things to `Mathlib.Algebra.Order.Monoid.Prod` (unlikely to happen)
-/

@[expose] public section

namespace Prod.RevLex

@[to_additive]
instance [One α] : One (RevLex α) where
  one := toRevLex 1

@[to_additive (attr := simp)]
theorem toRevLex_one [One α] : toRevLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofRevLex_one [One α] : (ofRevLex 1 : α) = 1 := rfl

@[to_additive]
instance [h : Mul α] : Mul (RevLex α) where
  mul a b := toRevLex (ofRevLex a * ofRevLex b)

@[to_additive (attr := simp)]
theorem toRevLex_mul [Mul α] (a b : α) : toRevLex (a * b) = toRevLex a * toRevLex b := rfl

@[to_additive (attr := simp)]
theorem ofRevLex_mul [Mul α] (a b : RevLex α) : ofRevLex (a * b) = ofRevLex a * ofRevLex b := rfl

@[to_additive]
instance [Monoid α] [Monoid β] : Monoid (α ×ᵣ β) where
  mul_assoc a b c := by
    simp_rw [HMul.hMul, Mul.mul, ofRevLex_toRevLex, mul_assoc]
  one_mul a := by
    simp_rw [HMul.hMul, Mul.mul]
    simp
  mul_one a := by
    simp_rw [HMul.hMul, Mul.mul]
    simp

@[to_additive]
instance [CommMonoid α] [CommMonoid β] : CommMonoid (α ×ᵣ β) where
  mul_comm a b := by
    simp_rw [HMul.hMul, Mul.mul, mul_comm]

@[to_additive]
instance [CommGroup α] [CommGroup β] : CommGroup (α ×ᵣ β) where
  inv a := toRevLex ((ofRevLex a)⁻¹)
  inv_mul_cancel a := ofRevLex_inj.mp (by simp)

@[to_additive]
instance isOrderedMonoid [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CommMonoid β] [PartialOrder β] [MulLeftStrictMono β] :
    IsOrderedMonoid (α ×ᵣ β) where
  mul_le_mul_left _ _ hxy z :=
    (le_iff.1 hxy).elim
      (fun hxy => left _ _ <| mul_lt_mul_left hxy (ofRevLex z).2)
      (fun hxy => le_iff.2 <| Or.inr
      ⟨by simp only [ofRevLex_mul, snd_mul, hxy.1],
        (by rw [ofRevLex_mul, fst_mul]; exact mul_le_mul_left hxy.2 (ofRevLex z).1)⟩)

@[to_additive]
instance isOrderedCancelMonoid [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (α ×ᵣ β) where
  mul_le_mul_left _ _ := mul_le_mul_left
  le_of_mul_le_mul_left _ _ _ hxyz := (le_iff.1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => le_iff.2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

/-- An ordered multiplicative isomorphism given by `lexEquiv`. -/
@[to_additive /-- An ordered additive isomorphism given by `lexEquiv`. -/]
def lexEquivMulHom (α β) [PartialOrder α] [Monoid α] [PartialOrder β] [Monoid β] :
    α ×ₗ β ≃*o β ×ᵣ α :=
  ⟨⟨lexEquiv α β, fun x y ↦ by simp; rfl⟩, OrderIso.le_iff_le (lexEquiv α β)⟩

end Prod.RevLex
