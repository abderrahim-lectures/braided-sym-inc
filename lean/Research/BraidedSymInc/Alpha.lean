import Research.BraidedSymInc.Criterion
import Research.BraidedSymInc.Basis

/-!
# The automorphism induced by an order involution, and basis expansion

`alpha τ` is the ring endomorphism `f ↦ (a, b) ↦ f (τ a) (τ b)` of the incidence algebra.
`eq_sum_single` expands an element in the matrix units.
-/

namespace Research.BraidedSymInc

open Finset

variable {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [LocallyFiniteOrder P]
variable {K : Type*} [CommRing K]

/-- Relabel an incidence function by an order automorphism. -/
def alphaFun (τ : P ≃o P) (f : IncidenceAlgebra K P) : IncidenceAlgebra K P where
  toFun a b := f (τ a) (τ b)
  eq_zero_of_not_le' a b hab :=
    f.eq_zero_of_not_le' (fun h => hab (τ.le_iff_le.mp h))

/-- The ring endomorphism induced by an order automorphism. -/
def alpha (τ : P ≃o P) : IncidenceAlgebra K P →+* IncidenceAlgebra K P where
  toFun := alphaFun τ
  map_one' := by
    apply IncidenceAlgebra.ext
    intro a b _
    change (1 : IncidenceAlgebra K P) (τ a) (τ b) = (1 : IncidenceAlgebra K P) a b
    rw [IncidenceAlgebra.one_apply, IncidenceAlgebra.one_apply]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun h' => h (τ.injective h'))]
  map_mul' f g := by
    apply IncidenceAlgebra.ext
    intro a b _
    show (f * g) (τ a) (τ b) = (alphaFun τ f * alphaFun τ g) a b
    rw [mul_apply_univ, mul_apply_univ]
    exact (Equiv.sum_comp τ.toEquiv (fun x => f (τ a) x * g x (τ b))).symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem alpha_apply (τ : P ≃o P) (f : IncidenceAlgebra K P) (a b : P) :
    alpha τ f a b = f (τ a) (τ b) := rfl

/-- Evaluation of a finite sum of incidence functions, entrywise. -/
theorem sum_apply' {ι : Type*} (s : Finset ι) (F : ι → IncidenceAlgebra K P) (r t : P) :
    (∑ i ∈ s, F i) r t = ∑ i ∈ s, F i r t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, IncidenceAlgebra.zero_apply]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, IncidenceAlgebra.add_apply, ih]

open scoped Classical in
/-- Entry of one term of the matrix-unit expansion. -/
theorem expansion_entry (f : IncidenceAlgebra K P) (r s a b : P) :
    (if h : a ≤ b then f a b • single (K := K) a b h else 0 : IncidenceAlgebra K P) r s
      = if a = r ∧ b = s then f a b else 0 := by
  by_cases h : a ≤ b
  · rw [dif_pos h, IncidenceAlgebra.constSMul_apply, single_apply, smul_eq_mul]
    by_cases hc : a = r ∧ b = s
    · obtain ⟨h1, h2⟩ := hc
      subst h1
      subst h2
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, mul_one]
    · have hc' : ¬ (r = a ∧ s = b) := fun he => hc ⟨he.1.symm, he.2.symm⟩
      rw [if_neg hc', if_neg hc, mul_zero]
  · rw [dif_neg h, IncidenceAlgebra.zero_apply]
    by_cases hc : a = r ∧ b = s
    · rw [if_pos hc, IncidenceAlgebra.apply_eq_zero_of_not_le h f]
    · rw [if_neg hc]

open scoped Classical in
/-- Expansion of an incidence function in the matrix units. -/
theorem eq_sum_single (f : IncidenceAlgebra K P) :
    f = ∑ a, ∑ b, (if h : a ≤ b then f a b • single (K := K) a b h else 0) := by
  apply IncidenceAlgebra.ext
  intro r s _
  rw [sum_apply']
  have h1 : ∀ a, (∑ b, (if h : a ≤ b then f a b • single (K := K) a b h else 0 :
      IncidenceAlgebra K P)) r s = ∑ b, (if a = r ∧ b = s then f a b else 0) := by
    intro a
    rw [sum_apply']
    exact Finset.sum_congr rfl (fun b _ => expansion_entry f r s a b)
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  rw [Finset.sum_eq_single r]
  · rw [Finset.sum_eq_single s]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro b _ hb
      rw [if_neg (fun h => hb h.2)]
    · intro h
      exact absurd (Finset.mem_univ s) h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => ha h.1)]
  · intro h
    exact absurd (Finset.mem_univ r) h

end Research.BraidedSymInc
