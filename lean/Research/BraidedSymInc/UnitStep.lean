import Research.BraidedSymInc.UnitRel

/-!
# Step 4: `D₁ (e_{cd})` is a multiple of `e_{cd}`

For `c < d` and `D(ε_x) = 0` for all `x`, the entries `D(e_{cd})_{rs}` vanish unless
`(r, s) = (c, d)`.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

theorem unit_support {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    (h2 : IsUnit (2 : K)) (hz : ∀ x, D (eps (K := K) x) = 0) {c d : P} (hcd : c < d)
    (r s : P) (hne : ¬ (r = c ∧ s = d)) : D (single (K := K) c d hcd.le) r s = 0 := by
  obtain ⟨H, hH⟩ : ∃ H : IncidenceAlgebra K P, H = D (single (K := K) c d hcd.le) := ⟨_, rfl⟩
  rw [← hH]
  have R : ∀ x r s : P, (if x = c then H r s else 0) - (if r = x then H x s else 0)
      + (if x = d then H (τ r) (τ s) else 0) - (if τ s = x then H (τ r) x else 0) = 0 := by
    intro x r s
    have := rel_unit G hz hcd.le x r s
    rw [hH]
    exact this
  -- the row and column of a point outside {c, d}
  have outside : ∀ x : P, x ≠ c → x ≠ d → (∀ s, H x s = 0) ∧ (∀ r, H r x = 0) := by
    intro x hxc hxd
    have R' : ∀ r s : P, (if r = x then H x s else 0) + (if τ s = x then H (τ r) x else 0) = 0 := by
      intro r s
      have := R x r s
      rw [ite_eq_right hxc, ite_eq_right hxd] at this
      linear_combination -this
    have col : ∀ u, u ≠ τ x → H u x = 0 := by
      intro u hu
      have := R' (τ u) (τ x)
      have hne1 : τ u ≠ x := fun e => hu (by rw [← e, hτ])
      rw [ite_eq_right hne1, ite_eq_left (hτ x), hτ] at this
      linear_combination this
    have row : ∀ s, s ≠ τ x → H x s = 0 := by
      intro s hs
      have := R' x s
      have hne1 : τ s ≠ x := fun e => hs (by rw [← e, hτ])
      rw [ite_eq_left rfl, ite_eq_right hne1] at this
      linear_combination this
    have mid : H x (τ x) = 0 ∧ H (τ x) x = 0 := by
      by_cases hτx : τ x = x
      · have := R' x x
        rw [ite_eq_left rfl, ite_eq_left hτx, hτx] at this
        have h' : (2 : K) * H x x = 0 := by linear_combination this
        have h0 := (h2.mul_right_eq_zero).mp h'
        rw [hτx]
        exact ⟨h0, h0⟩
      · constructor
        · apply IncidenceAlgebra.apply_eq_zero_of_not_le
          intro hle
          exact hτx (order_inv hτ hle)
        · apply IncidenceAlgebra.apply_eq_zero_of_not_le
          intro hle
          have h3 : x ≤ τ x := by
            have := τ.monotone hle
            rwa [hτ] at this
          exact hτx (order_inv hτ h3)
    constructor
    · intro s
      by_cases hs : s = τ x
      · rw [hs]
        exact mid.1
      · exact row s hs
    · intro r
      by_cases hr : r = τ x
      · rw [hr]
        exact mid.2
      · exact col r hr
  have hdc : d ≠ c := hcd.ne'
  -- τ c is neither c's partner d
  have hτcd : τ c ≠ d := by
    intro e
    have hle : c ≤ τ c := e ▸ hcd.le
    exact hdc (e.symm.trans (order_inv hτ hle) |>.symm ▸ rfl)
  have hdd : H d d = 0 := by
    have := R c d d
    rw [ite_eq_left rfl, ite_eq_right hdc, ite_eq_right hcd.ne] at this
    have hn : ¬ (τ d = c) := fun e => hτcd (by rw [← e, hτ])
    rw [ite_eq_right hn] at this
    linear_combination this
  have hcc : H c c = 0 := by
    have := R c (τ c) (τ c)
    rw [ite_eq_left rfl, ite_eq_right hcd.ne] at this
    rw [hτ, ite_eq_left rfl] at this
    by_cases hτc : τ c = c
    · rw [hτc] at this
      rw [ite_eq_left rfl] at this
      linear_combination (-1 : K) * this
    · rw [ite_eq_right hτc] at this
      have h0 : H (τ c) (τ c) = 0 := (outside (τ c) hτc hτcd).1 (τ c)
      rw [h0] at this
      linear_combination (-1 : K) * this
  -- conclude
  by_cases hle : r ≤ s
  · by_cases hr : r = c ∨ r = d
    · by_cases hs : s = c ∨ s = d
      · rcases hr with hr | hr <;> rcases hs with hs | hs
        · rw [hr, hs]
          exact hcc
        · exact absurd ⟨hr, hs⟩ hne
        · rw [hr, hs] at hle
          exact absurd hle (not_le_of_gt hcd)
        · rw [hr, hs]
          exact hdd
      · push Not at hs
        exact (outside s hs.1 hs.2).2 r
    · push Not at hr
      exact (outside r hr.1 hr.2).1 s
  · exact IncidenceAlgebra.apply_eq_zero_of_not_le hle _

end Research.BraidedSymInc
