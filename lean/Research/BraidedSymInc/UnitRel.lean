import Research.BraidedSymInc.Idempotents

/-!
# The relation on the pair `(ε_x, e_{cd})`

Equation (step4) of braided-sym-inc in coordinates.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

theorem eps_mul_single_self {c d : P} (h : c ≤ d) :
    (eps c * single (K := K) c d h : IncidenceAlgebra K P) = single c d h := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [single_mul_apply, single_apply, single_apply]
  by_cases hr : r = c
  · subst hr
    rw [ite_eq_left rfl]
  · rw [ite_eq_right hr, ite_eq_right (fun hc => hr hc.1)]

theorem eps_mul_single_ne {x c d : P} (h : c ≤ d) (hx : x ≠ c) :
    (eps x * single (K := K) c d h : IncidenceAlgebra K P) = 0 := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [single_mul_apply, IncidenceAlgebra.zero_apply]
  by_cases hr : r = x
  · rw [ite_eq_left hr, single_apply, ite_eq_right (fun hc => hx hc.1)]
  · rw [ite_eq_right hr]

theorem single_mul_eps_self {c d : P} (h : c ≤ d) :
    (single (K := K) c d h * eps d : IncidenceAlgebra K P) = single c d h := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [mul_single_apply, single_apply, single_apply]
  by_cases hs : s = d
  · subst hs
    rw [ite_eq_left rfl]
  · rw [ite_eq_right hs, ite_eq_right (fun hc => hs hc.2)]

theorem single_mul_eps_ne {x c d : P} (h : c ≤ d) (hx : x ≠ d) :
    (single (K := K) c d h * eps x : IncidenceAlgebra K P) = 0 := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [mul_single_apply, IncidenceAlgebra.zero_apply]
  by_cases hs : s = x
  · rw [ite_eq_left hs, single_apply, ite_eq_right (fun hc => hx hc.2)]
  · rw [ite_eq_right hs]

/-- Equation (step4): coordinate form of the relation for `(ε_x, e_{cd})`. -/
theorem rel_unit {τ : P ≃o P} {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P}
    (G : Good τ D) (hz : ∀ x, D (eps (K := K) x) = 0) {c d : P} (h : c ≤ d) (x r s : P) :
    (if x = c then D (single (K := K) c d h) r s else 0)
      - (if r = x then D (single (K := K) c d h) x s else 0)
      + (if x = d then D (single (K := K) c d h) (τ r) (τ s) else 0)
      - (if τ s = x then D (single (K := K) c d h) (τ r) x else 0) = 0 := by
  have hrel := G.rel (eps (K := K) x) (single c d h)
  have h' := congrArg (fun f : IncidenceAlgebra K P => f r s) hrel
  have e1 : D (eps (K := K) x * single c d h) = if x = c then D (single c d h) else 0 := by
    by_cases hxc : x = c
    · subst hxc
      rw [eps_mul_single_self, ite_eq_left rfl]
    · rw [eps_mul_single_ne h hxc, map_zero, ite_eq_right hxc]
  have e2 : D (single (K := K) c d h * eps x) = if x = d then D (single c d h) else 0 := by
    by_cases hxd : x = d
    · subst hxd
      rw [single_mul_eps_self, ite_eq_left rfl]
    · rw [single_mul_eps_ne h hxd, map_zero, ite_eq_right hxd]
  simp only [IncidenceAlgebra.add_apply, IncidenceAlgebra.zero_apply, dfct, hz x, zero_mul,
    mul_zero, IncidenceAlgebra.sub_apply, alpha_apply, e1, e2, mul_single_apply,
    single_mul_apply] at h'
  by_cases hxc : x = c
  · by_cases hxd : x = d
    · rw [ite_eq_left hxc, ite_eq_left hxd] at h' ⊢
      linear_combination h'
    · rw [ite_eq_left hxc, ite_eq_right hxd] at h' ⊢
      try simp only [IncidenceAlgebra.zero_apply] at h'
      linear_combination h'
  · by_cases hxd : x = d
    · rw [ite_eq_right hxc, ite_eq_left hxd] at h' ⊢
      try simp only [IncidenceAlgebra.zero_apply] at h'
      linear_combination h'
    · rw [ite_eq_right hxc, ite_eq_right hxd] at h' ⊢
      try simp only [IncidenceAlgebra.zero_apply] at h'
      linear_combination h'

end Research.BraidedSymInc
