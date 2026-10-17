import Research.BraidedSymInc.Main

/-!
# Theorem 1.1 of braided-sym-inc (formalized)

For a finite poset `P`, a commutative ring `K` with `2` invertible, and an order involution `τ`,
a linear map `D` of `IncidenceAlgebra K P` that commutes with `alpha τ` satisfies the
Leibniz rule for the twisted product `x ⋆ y = x * y + α (y * x)` if and only if it is a
derivation.  This is `BSDer(A,α)^α = Der(A)^α`.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- A braided-symmetric derivation that commutes with `α` is a derivation. -/
theorem derivation_of_braided {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) (h2 : IsUnit (2 : K))
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P}
    (hcomm : ∀ f, D (alpha τ f) = alpha τ (D f))
    (hbs : ∀ f g, D (twist (alpha τ) f g) = twist (alpha τ) (D f) g + twist (alpha τ) f (D g)) :
    ∀ f g, D (f * g) = D f * g + f * D g := by
  have hrel : ∀ f g, dfct D f g + alpha τ (dfct D g f) = 0 := by
    have := (bs_iff_defect (alpha τ) D.toAddMonoidHom hcomm).mp hbs
    intro f g
    exact this f g
  have G : Good τ D := ⟨hcomm, hrel⟩
  classical
  have G1 : Good τ (D - adC (cMat D)) := good_normD G (alpha_cMat hτ G)
  have H : ∀ x r s, r ≠ s → (D - adC (cMat D)) (eps (K := K) x) r s = 0 :=
    fun x r s hrs => normD_offdiag hτ G x r s hrs
  have hz : ∀ x, (D - adC (cMat D)) (eps (K := K) x) = 0 := eps_zero hτ G1 h2 H
  have hD1 : ∀ f g, (D - adC (cMat D)) (f * g)
      = (D - adC (cMat D)) f * g + f * (D - adC (cMat D)) g :=
    derivation_of_units (D - adC (cMat D))
      (fun a b c d hab hcd => leibniz_units hτ G1 h2 hz hab hcd)
  have hD : ∀ f, D f = (D - adC (cMat D)) f + (cMat D * f - f * cMat D) := by
    intro f
    rw [LinearMap.sub_apply, adC_apply]
    abel
  intro f g
  rw [hD (f * g), hD f, hD g, hD1 f g]
  noncomm_ring

/-- Theorem 1.1: `BSDer(A,α)^α = Der(A)^α` for incidence algebras. -/
theorem braided_iff_derivation {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) (h2 : IsUnit (2 : K))
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P}
    (hcomm : ∀ f, D (alpha τ f) = alpha τ (D f)) :
    (∀ f g, D (twist (alpha τ) f g) = twist (alpha τ) (D f) g + twist (alpha τ) f (D g)) ↔
      ∀ f g, D (f * g) = D f * g + f * D g := by
  constructor
  · exact derivation_of_braided hτ h2 hcomm
  · intro hder
    exact derivation_is_bs (alpha τ) D.toAddMonoidHom hcomm hder

/-- The map `α` of an order involution is an involution. -/
theorem alpha_alpha {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) (f : IncidenceAlgebra K P) :
    alpha τ (alpha τ f) = f := by
  apply IncidenceAlgebra.ext
  intro a b _
  rw [alpha_apply, alpha_apply, hτ a, hτ b]

/-- `α` is injective. -/
theorem alpha_injective {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) :
    Function.Injective (alpha (K := K) τ) := by
  intro f g h
  have h' := congrArg (alpha (K := K) τ) h
  rw [alpha_alpha hτ, alpha_alpha hτ] at h'
  exact h'

omit [Fintype P] in
/-- With `2` invertible in `K`, the incidence algebra has no `2`-torsion. -/
theorem incidence_two_torsion_free (h2 : IsUnit (2 : K)) (f : IncidenceAlgebra K P)
    (hf : f + f = 0) : f = 0 := by
  obtain ⟨u, hu⟩ := h2.exists_left_inv
  have h3 : (2 : K) • f = 0 := by
    rw [two_smul]
    exact hf
  have h4 : f = (u * 2) • f := by
    rw [hu, one_smul]
  rw [h4, mul_smul, h3, smul_zero]

/-- Theorem 1.1 without the commuting hypothesis: `BSDer(A,α) = Der(A)^α`.
A braided-symmetric derivation commutes with `α` automatically. -/
theorem braided_iff_derivation_comm {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) (h2 : IsUnit (2 : K))
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} :
    (∀ f g, D (twist (alpha τ) f g) = twist (alpha τ) (D f) g + twist (alpha τ) f (D g)) ↔
      ((∀ f g, D (f * g) = D f * g + f * D g) ∧ ∀ f, D (alpha τ f) = alpha τ (D f)) := by
  constructor
  · intro hbs
    have hcomm : ∀ f, D (alpha τ f) = alpha τ (D f) :=
      bs_comm (alpha τ) D.toAddMonoidHom (alpha_injective hτ)
        (incidence_two_torsion_free h2) hbs
    exact ⟨derivation_of_braided hτ h2 hcomm hbs, hcomm⟩
  · intro hh
    exact derivation_is_bs (alpha τ) D.toAddMonoidHom hh.2 hh.1

end Research.BraidedSymInc
