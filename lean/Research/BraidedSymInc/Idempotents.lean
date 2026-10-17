import Research.BraidedSymInc.Diagonal

/-!
# Step 3: `D₁` vanishes on the diagonal idempotents

Let `D` satisfy `Good τ D` with `2` invertible, and suppose `D(ε_x)` has no off-diagonal
entry.  Then `D(ε_x) = 0` for every `x`.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- The off-diagonal diagonal entries `D(ε_x)_{yy}` for `y ≠ x` vanish. -/
theorem diag_offpoint {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    (h2 : IsUnit (2 : K)) {x y : P} (hxy : x ≠ y) : D (eps (K := K) x) y y = 0 := by
  have h := coeffEq G (x := x) (y := y) hxy y y
  by_cases hτy : τ y = y
  · have hn : ¬ (τ y = x) := fun hc => hxy (hc.symm.trans hτy)
    rw [hτy] at h
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hxy), ite_eq_right (fun hc : y = x => hxy hc.symm)]
      at h
    have h' : (2 : K) * D (eps x) y y = 0 := by linear_combination h
    exact (h2.mul_right_eq_zero).mp h'
  · rw [ite_eq_left rfl, ite_eq_right (Ne.symm hxy), ite_eq_right hτy] at h
    by_cases hc : τ y = x
    · rw [ite_eq_left hc] at h
      have hτx : τ x = y := by rw [← hc, hτ]
      have e := equi hτ G x y y
      rw [hτx, hc] at e
      rw [hc] at h
      rw [e] at h
      have h' : (2 : K) * D (eps x) y y = 0 := by linear_combination h
      exact (h2.mul_right_eq_zero).mp h'
    · rw [ite_eq_right hc] at h
      linear_combination h

/-- Step 3: `D(ε_x) = 0` when `D(ε_x)` has no off-diagonal entry. -/
theorem eps_zero {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    (h2 : IsUnit (2 : K)) (H : ∀ x r s, r ≠ s → D (eps (K := K) x) r s = 0) (x : P) :
    D (eps (K := K) x) = 0 := by
  have hdiag : D (eps (K := K) x) x x = 0 := by
    have h := G.rel (eps (K := K) x) (eps x)
    have h' := congrArg (fun f : IncidenceAlgebra K P => f x x) h
    simp only [IncidenceAlgebra.add_apply, IncidenceAlgebra.zero_apply, dfct, eps_mul_self,
      IncidenceAlgebra.sub_apply, alpha_apply, mul_single_apply, single_mul_apply] at h'
    by_cases hτx : τ x = x
    · rw [hτx] at h'
      simp only [ite_true] at h'
      have h'' : (2 : K) * D (eps x) x x = 0 := by linear_combination (-1 : K) * h'
      exact (h2.mul_right_eq_zero).mp h''
    · have h0 : D (eps (K := K) x) (τ x) (τ x) = 0 :=
        diag_offpoint hτ G h2 (fun e => hτx e.symm)
      simp only [ite_true, ite_eq_right hτx, h0] at h'
      linear_combination (-1 : K) * h'
  apply IncidenceAlgebra.ext
  intro r s _
  rw [IncidenceAlgebra.zero_apply]
  by_cases hrs : r = s
  · subst hrs
    by_cases hrx : r = x
    · subst hrx
      exact hdiag
    · exact diag_offpoint hτ G h2 (fun e => hrx e.symm)
  · exact H x r s hrs

end Research.BraidedSymInc
