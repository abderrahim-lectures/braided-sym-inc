import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Research.BraidedSymInc.Reduce

/-!
# Coordinates of the Leibniz defect on diagonal idempotents

Fix an order involution `τ` of a finite poset `P` and a linear map `D` of the incidence algebra
that commutes with `alpha τ` and satisfies the defect relation `E(x,y) + α(E(y,x)) = 0`
(`Good τ D`).  This file records the coordinate form of that relation on the pair
`(ε_x, ε_y)`, which is equation (coeff) of braided-sym-inc.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- Leibniz defect of a linear map. -/
def dfct (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P) (f g : IncidenceAlgebra K P) :
    IncidenceAlgebra K P := D (f * g) - D f * g - f * D g

/-- A linear map that commutes with `alpha τ` and satisfies the defect relation. -/
structure Good (τ : P ≃o P) (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P) : Prop where
  comm : ∀ f, D (alpha τ f) = alpha τ (D f)
  rel : ∀ f g, dfct D f g + alpha τ (dfct D g f) = 0

/-- The diagonal idempotent `ε_x`. -/
abbrev eps (x : P) : IncidenceAlgebra K P := single (K := K) x x le_rfl

theorem eps_mul_eps_of_ne {x y : P} (h : x ≠ y) :
    (eps x * eps y : IncidenceAlgebra K P) = 0 := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [mul_single_apply, IncidenceAlgebra.zero_apply]
  by_cases hs : s = y
  · rw [ite_eq_left hs, single_apply, ite_eq_right (fun hc => h hc.2.symm)]
  · rw [ite_eq_right hs]

/-- Equation (coeff): the relation on the pair `(ε_x, ε_y)`, entry `(r, s)`. -/
theorem coeffEq {τ : P ≃o P}
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    {x y : P} (hxy : x ≠ y) (r s : P) :
    (if s = y then D (eps x) r y else 0) + (if r = x then D (eps y) x s else 0)
      + (if τ s = x then D (eps y) (τ r) x else 0)
      + (if τ r = y then D (eps x) y (τ s) else 0) = 0 := by
  have h := G.rel (eps (K := K) x) (eps y)
  have h' := congrArg (fun f : IncidenceAlgebra K P => f r s) h
  simp only [IncidenceAlgebra.add_apply, IncidenceAlgebra.zero_apply, dfct,
    eps_mul_eps_of_ne hxy, eps_mul_eps_of_ne hxy.symm, map_zero,
    IncidenceAlgebra.sub_apply, alpha_apply, mul_single_apply, single_mul_apply] at h'
  linear_combination -h'

end Research.BraidedSymInc
