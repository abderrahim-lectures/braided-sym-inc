import Research.BraidedSymInc.Coord

/-!
# Step 1: the support of `D (ε_x)`

Lemma `lem:support` of braided-sym-inc: an entry `D(ε_x) r s` with `r ≤ s` can be nonzero only
if `r = x`, `s = x` or `r = s`.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

omit [Fintype P] [DecidableEq P] [LocallyFiniteOrder P] in
/-- Lemma `lem:order`: `x ≤ τ x` forces `τ x = x` for an order involution. -/
theorem order_inv {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) {x : P} (h : x ≤ τ x) : τ x = x := by
  have h2 : τ x ≤ τ (τ x) := τ.monotone h
  rw [hτ x] at h2
  exact le_antisymm h2 h

/-- Lemma `lem:support`. -/
theorem support_eps {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    {x r s : P} (hrs : r ≤ s) (hr : r ≠ x) (hs : s ≠ x) (hne : r ≠ s) :
    D (eps (K := K) x) r s = 0 := by
  -- first relation: the pair (x, s), entry (r, s)
  have h1 := coeffEq G (x := x) (y := s) (Ne.symm hs) r s
  -- second relation: the pair (r, x), entry (r, s)
  have h2 := coeffEq G (x := r) (y := x) hr r s
  by_contra hF
  rw [ite_eq_left rfl, ite_eq_right hr] at h1
  rw [ite_eq_right hs, ite_eq_left rfl] at h2
  have hA : τ s = x ∨ τ r = s := by
    by_contra hc
    push Not at hc
    rw [ite_eq_right hc.1, ite_eq_right hc.2] at h1
    exact hF (by linear_combination h1)
  have hB : τ s = r ∨ τ r = x := by
    by_contra hc
    push Not at hc
    rw [ite_eq_right hc.1, ite_eq_right hc.2] at h2
    exact hF (by linear_combination h2)
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · exact hr (hB.symm.trans hA)
    · exact hne (τ.injective (hB.trans hA.symm))
  · have hle : r ≤ τ r := hA ▸ hrs
    have := order_inv hτ hle
    exact hne (this.symm.trans hA)

end Research.BraidedSymInc
