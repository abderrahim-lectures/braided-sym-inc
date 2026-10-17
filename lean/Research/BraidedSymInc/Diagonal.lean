import Research.BraidedSymInc.Normalize

/-!
# Steps 2 and 3: `D₁(ε_x)` has no off-diagonal entry and is zero

`normD_offdiag` is the end of Step 2: after subtracting `ad_c`, the image of `ε_x` is diagonal.
`eps_zero` is Step 3: a diagonal `D₁(ε_x)` that satisfies the relation is zero when `2` is
invertible.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

theorem eps_mul_self (x : P) : (eps x * eps x : IncidenceAlgebra K P) = eps x := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [mul_single_apply]
  by_cases hs : s = x
  · subst hs
    rw [ite_eq_left rfl]
  · rw [ite_eq_right hs, single_apply, ite_eq_right (fun h => hs h.2)]

open scoped Classical in
omit [Fintype P] [LocallyFiniteOrder P] in
theorem cMat_apply (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P) (r s : P) :
    cMat D r s = if r < s then D (eps (K := K) s) r s else 0 := rfl

open scoped Classical in
/-- End of Step 2: the entries of `(D - ad_c)(ε_x)` off the diagonal vanish. -/
theorem normD_offdiag {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D) (x r s : P)
    (hrs : r ≠ s) : (D - adC (cMat D)) (eps (K := K) x) r s = 0 := by
  by_cases hle : r ≤ s
  · rw [LinearMap.sub_apply, adC_apply, IncidenceAlgebra.sub_apply, IncidenceAlgebra.sub_apply,
      mul_single_apply, single_mul_apply, cMat_apply, cMat_apply]
    have hlt : r < s := lt_of_le_of_ne hle hrs
    by_cases hsx : s = x
    · subst hsx
      rw [ite_eq_left rfl, ite_eq_left hlt, ite_eq_right hrs]
      ring
    · by_cases hrx : r = x
      · subst hrx
        rw [ite_eq_right hsx, ite_eq_left rfl, ite_eq_left hlt]
        have := antisym hτ G hlt
        linear_combination this
      · rw [ite_eq_right hsx, ite_eq_right hrx, support_eps hτ G hle hrx hsx hrs]
        ring
  · exact IncidenceAlgebra.apply_eq_zero_of_not_le hle _

end Research.BraidedSymInc
