import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Basis elements and coordinates of the incidence algebra

For a finite poset `P` and a commutative ring `K` we work with mathlib's
`IncidenceAlgebra K P`.  This file gives the matrix-unit basis `single a b` (`a ≤ b`) and the
coordinate formulas for products that the proof of the main theorem of braided-sym-inc uses.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- The product of two incidence functions as a sum over all of `P`. -/
theorem mul_apply_univ (f g : IncidenceAlgebra K P) (r s : P) :
    (f * g) r s = ∑ x, f r x * g x s := by
  rw [IncidenceAlgebra.mul_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  rw [Finset.mem_Icc] at hx
  by_cases h : r ≤ x
  · have h2 : ¬ x ≤ s := fun h2 => hx ⟨h, h2⟩
    rw [IncidenceAlgebra.apply_eq_zero_of_not_le h2 g, mul_zero]
  · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h f, zero_mul]

/-- The matrix unit `e_{ab}` for `a ≤ b`. -/
def single (a b : P) (h : a ≤ b) : IncidenceAlgebra K P where
  toFun x y := if x = a ∧ y = b then 1 else 0
  eq_zero_of_not_le' x y hxy := by
    by_cases hc : x = a ∧ y = b
    · exact absurd (hc.1 ▸ hc.2 ▸ h) hxy
    · simp [hc]

@[simp] theorem single_apply (a b : P) (h : a ≤ b) (x y : P) :
    (single a b h : IncidenceAlgebra K P) x y = if x = a ∧ y = b then 1 else 0 := rfl

/-- Right multiplication by a matrix unit picks a column. -/
theorem mul_single_apply (f : IncidenceAlgebra K P) (c d : P) (h : c ≤ d) (r s : P) :
    (f * single (K := K) c d h) r s = if s = d then f r c else 0 := by
  rw [mul_apply_univ]
  simp only [single_apply]
  by_cases hs : s = d
  · simp [hs]
  · simp [hs]

/-- Left multiplication by a matrix unit picks a row. -/
theorem single_mul_apply (a b : P) (h : a ≤ b) (f : IncidenceAlgebra K P) (r s : P) :
    (single (K := K) a b h * f) r s = if r = a then f b s else 0 := by
  rw [mul_apply_univ]
  simp only [single_apply]
  by_cases hr : r = a
  · simp [hr]
  · simp [hr]

end Research.BraidedSymInc
