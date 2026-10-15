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

end Research.BraidedSymInc
