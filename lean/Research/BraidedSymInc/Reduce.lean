import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Research.BraidedSymInc.Alpha

/-!
# Reduction of the Leibniz rule to matrix units

A linear map on the incidence algebra is a derivation as soon as the Leibniz rule holds on every
pair of matrix units.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- Scalars pass through the right factor of a product. -/
theorem mul_smul_comm' (t : K) (x y : IncidenceAlgebra K P) : x * (t • y) = t • (x * y) := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [mul_apply_univ, IncidenceAlgebra.constSMul_apply, mul_apply_univ, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [IncidenceAlgebra.constSMul_apply, smul_eq_mul]
  ring

/-- A submodule that contains all matrix units is everything. -/
theorem mem_of_units (S : Submodule K (IncidenceAlgebra K P))
    (h : ∀ a b (hab : a ≤ b), (single (K := K) a b hab) ∈ S) (f : IncidenceAlgebra K P) :
    f ∈ S := by
  classical
  rw [eq_sum_single f]
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))
  by_cases hab : a ≤ b
  · rw [dite_eq_left hab]
    exact Submodule.smul_mem _ _ (h a b hab)
  · rw [dite_eq_right hab]
    exact S.zero_mem

/-- The Leibniz rule on matrix units gives the Leibniz rule everywhere. -/
theorem derivation_of_units (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P)
    (h : ∀ a b c d (hab : a ≤ b) (hcd : c ≤ d),
      D (single (K := K) a b hab * single (K := K) c d hcd)
        = D (single a b hab) * single c d hcd + single a b hab * D (single c d hcd))
    (f g : IncidenceAlgebra K P) : D (f * g) = D f * g + f * D g := by
  -- first: g a matrix unit, f arbitrary
  have hstep : ∀ c d (hcd : c ≤ d) (f : IncidenceAlgebra K P),
      D (f * single (K := K) c d hcd) = D f * single c d hcd + f * D (single c d hcd) := by
    intro c d hcd f
    let S : Submodule K (IncidenceAlgebra K P) :=
      { carrier := {f | D (f * single (K := K) c d hcd) = D f * single c d hcd + f * D (single c d hcd)}
        add_mem' := by
          intro x y hx hy
          change D ((x + y) * single c d hcd) = D (x + y) * single c d hcd + (x + y) * D (single c d hcd)
          have hx' : D (x * single (K := K) c d hcd) = D x * single c d hcd + x * D (single c d hcd) := hx
          have hy' : D (y * single (K := K) c d hcd) = D y * single c d hcd + y * D (single c d hcd) := hy
          rw [add_mul, map_add, hx', hy', map_add, add_mul, add_mul]
          abel
        zero_mem' := by
          change D (0 * single (K := K) c d hcd) = D 0 * single c d hcd + 0 * D (single c d hcd)
          rw [zero_mul, map_zero, zero_mul, zero_mul, add_zero]
        smul_mem' := by
          intro t x hx
          change D ((t • x) * single (K := K) c d hcd)
            = D (t • x) * single c d hcd + (t • x) * D (single c d hcd)
          have hx' : D (x * single (K := K) c d hcd) = D x * single c d hcd + x * D (single c d hcd) := hx
          rw [smul_mul_assoc, map_smul, hx', map_smul, smul_add, smul_mul_assoc, smul_mul_assoc] }
    exact mem_of_units S (fun a b hab => h a b c d hab hcd) f
  -- then g arbitrary
  let T : Submodule K (IncidenceAlgebra K P) :=
    { carrier := {g | D (f * g) = D f * g + f * D g}
      add_mem' := by
        intro x y hx hy
        change D (f * (x + y)) = D f * (x + y) + f * D (x + y)
        have hx' : D (f * x) = D f * x + f * D x := hx
        have hy' : D (f * y) = D f * y + f * D y := hy
        rw [mul_add, map_add, hx', hy', map_add, mul_add, mul_add]
        abel
      zero_mem' := by
        change D (f * 0) = D f * 0 + f * D 0
        rw [mul_zero, map_zero, mul_zero, mul_zero, add_zero]
      smul_mem' := by
        intro t x hx
        change D (f * (t • x)) = D f * (t • x) + f * D (t • x)
        have hx' : D (f * x) = D f * x + f * D x := hx
        rw [mul_smul_comm', map_smul, hx', map_smul, smul_add, mul_smul_comm', mul_smul_comm'] }
  exact mem_of_units T (fun c d hcd => hstep c d hcd f) g

end Research.BraidedSymInc
