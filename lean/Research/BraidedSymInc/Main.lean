import Research.BraidedSymInc.UnitStep

/-!
# Theorem 1.1 of braided-sym-inc

Let `P` be a finite poset, `K` a commutative ring with `2` invertible and `τ` an order
involution of `P`.  A linear map `D` of the incidence algebra that commutes with `alpha τ` and
satisfies `E(x,y) + α(E(y,x)) = 0` (that is, a braided-symmetric derivation commuting with
`α`, by `bs_iff_defect`) is a derivation.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

theorem single_mul_single_ne {a b c d : P} (hab : a ≤ b) (hcd : c ≤ d) (hbc : b ≠ c) :
    (single (K := K) a b hab * single c d hcd : IncidenceAlgebra K P) = 0 := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [single_mul_apply, IncidenceAlgebra.zero_apply]
  by_cases hr : r = a
  · rw [ite_eq_left hr, single_apply, ite_eq_right (fun hc => hbc hc.1)]
  · rw [ite_eq_right hr]

theorem single_mul_single_eq {a b d : P} (hab : a ≤ b) (hbd : b ≤ d) :
    (single (K := K) a b hab * single b d hbd : IncidenceAlgebra K P) = single a d (hab.trans hbd) := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [single_mul_apply, single_apply, single_apply]
  by_cases hr : r = a
  · subst hr
    rw [ite_eq_left rfl]
    by_cases hs : s = d
    · rw [ite_eq_left ⟨rfl, hs⟩, ite_eq_left ⟨rfl, hs⟩]
    · rw [ite_eq_right (fun hc => hs hc.2), ite_eq_right (fun hc => hs hc.2)]
  · rw [ite_eq_right hr, ite_eq_right (fun hc => hr hc.1)]

/-- After Steps 2 to 4, `D₁` is a scalar multiple of the identity on each matrix unit. -/
theorem unit_form {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    (h2 : IsUnit (2 : K)) (hz : ∀ x, D (eps (K := K) x) = 0) {a b : P} (hab : a ≤ b) :
    D (single (K := K) a b hab) = (D (single a b hab) a b) • single a b hab := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [IncidenceAlgebra.constSMul_apply, single_apply, smul_eq_mul]
  by_cases hrs : r = a ∧ s = b
  · obtain ⟨h1, h3⟩ := hrs
    subst h1
    subst h3
    rw [ite_eq_left ⟨rfl, rfl⟩, mul_one]
  · rw [ite_eq_right hrs, mul_zero]
    rcases eq_or_lt_of_le hab with hEq | hlt
    · subst hEq
      have e : D (single (K := K) a a hab) = 0 := hz a
      rw [e, IncidenceAlgebra.zero_apply]
    · exact unit_support hτ G h2 hz hlt r s hrs

/-- The Leibniz rule for `D₁` on pairs of matrix units. -/
theorem leibniz_units {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D)
    (h2 : IsUnit (2 : K)) (hz : ∀ x, D (eps (K := K) x) = 0) {a b c d : P}
    (hab : a ≤ b) (hcd : c ≤ d) :
    D (single (K := K) a b hab * single c d hcd)
      = D (single a b hab) * single c d hcd + single a b hab * D (single c d hcd) := by
  have uab := unit_form hτ G h2 hz hab
  have ucd := unit_form hτ G h2 hz hcd
  by_cases hbc : b = c
  · subst hbc
    by_cases hab' : a = b
    · subst hab'
      have e : D (single (K := K) a a hab) = 0 := hz a
      have e2 : (single (K := K) a a hab : IncidenceAlgebra K P) = eps a := rfl
      rw [e, e2, eps_mul_single_self, zero_mul, zero_add, ucd, mul_smul_comm', eps_mul_single_self]
    · by_cases hbd : b = d
      · subst hbd
        have e : D (single (K := K) b b hcd) = 0 := hz b
        have e2 : (single (K := K) b b hcd : IncidenceAlgebra K P) = eps b := rfl
        rw [e, e2, single_mul_eps_self, mul_zero, add_zero, uab, smul_mul_assoc,
          single_mul_eps_self]
      · have hlt1 : a < b := lt_of_le_of_ne hab hab'
        have hlt2 : b < d := lt_of_le_of_ne hcd hbd
        have hda : d ≠ a := fun e => absurd (lt_trans hlt1 hlt2) (by rw [e]; exact lt_irrefl a)
        have hrel := G.rel (single (K := K) a b hab) (single b d hcd)
        have hz2 : dfct D (single (K := K) b d hcd) (single a b hab) = 0 := by
          unfold dfct
          rw [single_mul_single_ne hcd hab hda, map_zero, uab, ucd, smul_mul_assoc,
            mul_smul_comm', single_mul_single_ne hcd hab hda]
          simp only [smul_zero, sub_self]
        rw [hz2, map_zero, add_zero] at hrel
        unfold dfct at hrel
        rw [sub_sub, sub_eq_zero] at hrel
        rw [hrel, add_comm]
  · rw [single_mul_single_ne hab hcd hbc, map_zero, uab, ucd, smul_mul_assoc, mul_smul_comm',
      single_mul_single_ne hab hcd hbc]
    simp only [smul_zero, add_zero]

end Research.BraidedSymInc
