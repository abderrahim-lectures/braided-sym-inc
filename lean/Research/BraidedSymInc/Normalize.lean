import Research.BraidedSymInc.Support
import Mathlib.Tactic.NoncommRing

/-!
# Step 2: removing an inner derivation

For `D` with `Good τ D` we define `c = ∑_{r<s} D(ε_s)_{rs} e_{rs}` and `D₁ = D - ad_c`.
Then `Good τ D₁` holds and `D₁(ε_x)` has no off-diagonal entry.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

theorem alpha_eps {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x) (x : P) :
    alpha τ (eps (K := K) x) = eps (τ x) := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [alpha_apply, single_apply, single_apply]
  have e1 : τ r = x ↔ r = τ x := ⟨fun h => by rw [← h, hτ], fun h => by rw [h, hτ]⟩
  have e2 : τ s = x ↔ s = τ x := ⟨fun h => by rw [← h, hτ], fun h => by rw [h, hτ]⟩
  exact if_congr (and_congr e1 e2) rfl rfl

/-- Equivariance of the coefficients: `F_{τx}(τr, τs) = F_x(r, s)`. -/
theorem equi {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D) (x r s : P) :
    D (eps (K := K) (τ x)) (τ r) (τ s) = D (eps x) r s := by
  have h := G.comm (eps (K := K) x)
  rw [alpha_eps hτ] at h
  rw [h, alpha_apply, hτ, hτ]

/-- The entries `D(ε_x)_{xs}` and `D(ε_s)_{xs}` cancel for `x < s`. -/
theorem antisym {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D) {x s : P}
    (hxs : x < s) : D (eps (K := K) x) x s + D (eps s) x s = 0 := by
  have h := coeffEq G (x := x) (y := s) hxs.ne x s
  rw [ite_eq_left rfl, ite_eq_left rfl] at h
  have h3 : (if τ s = x then D (eps (K := K) s) (τ x) x else 0) = 0 := by
    by_cases hc : τ s = x
    · rw [ite_eq_left hc]
      have e : τ x = s := by rw [← hc, hτ]
      rw [e]
      exact IncidenceAlgebra.apply_eq_zero_of_not_le (not_le_of_gt hxs) _
    · rw [ite_eq_right hc]
  have h4 : (if τ x = s then D (eps (K := K) x) s (τ s) else 0) = 0 := by
    by_cases hc : τ x = s
    · rw [ite_eq_left hc]
      have e : τ s = x := by rw [← hc, hτ]
      rw [e]
      exact IncidenceAlgebra.apply_eq_zero_of_not_le (not_le_of_gt hxs) _
    · rw [ite_eq_right hc]
  rw [h3, h4] at h
  linear_combination h

open scoped Classical in
/-- The inner correction `c = ∑_{r<s} D(ε_s)_{rs} e_{rs}`. -/
noncomputable def cMat (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P) : IncidenceAlgebra K P where
  toFun r s := if r < s then D (eps (K := K) s) r s else 0
  eq_zero_of_not_le' r s h := by
    rw [ite_eq_right (fun hlt => h hlt.le)]

/-- The inner derivation `f ↦ c f - f c` as a linear map. -/
def adC (c : IncidenceAlgebra K P) : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P where
  toFun f := c * f - f * c
  map_add' f g := by
    rw [mul_add, add_mul]
    abel
  map_smul' t f := by
    rw [mul_smul_comm', smul_mul_assoc, smul_sub, RingHom.id_apply]

theorem adC_apply (c f : IncidenceAlgebra K P) : adC c f = c * f - f * c := rfl

open scoped Classical in
theorem alpha_cMat {τ : P ≃o P} (hτ : ∀ x, τ (τ x) = x)
    {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P} (G : Good τ D) :
    alpha τ (cMat D) = cMat D := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [alpha_apply]
  change (if τ r < τ s then D (eps (K := K) (τ s)) (τ r) (τ s) else 0)
    = (if r < s then D (eps (K := K) s) r s else 0)
  rw [equi hτ G s r s]
  by_cases h : r < s
  · rw [ite_eq_left h, ite_eq_left (τ.lt_iff_lt.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (τ.lt_iff_lt.mp h'))]

theorem dfct_sub (D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P)
    (c f g : IncidenceAlgebra K P) : dfct (D - adC c) f g = dfct D f g := by
  unfold dfct
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, adC_apply, adC_apply,
    adC_apply]
  noncomm_ring

theorem good_normD {τ : P ≃o P} {D : IncidenceAlgebra K P →ₗ[K] IncidenceAlgebra K P}
    (G : Good τ D) {c : IncidenceAlgebra K P} (hc : alpha τ c = c) :
    Good τ (D - adC c) := by
  constructor
  · intro f
    rw [LinearMap.sub_apply, LinearMap.sub_apply, G.comm, adC_apply, adC_apply]
    simp only [map_sub, map_mul, hc]
  · intro f g
    rw [dfct_sub, dfct_sub]
    exact G.rel f g

end Research.BraidedSymInc
