import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-!
# Defect criterion for braided-symmetric derivations (Lemma 2.3 of braided-sym-inc)

Let `A` be a ring and `α : A →+* A` a ring endomorphism.  The twisted product is
`x ⋆ y = x * y + α (y * x)`.  An additive map `D` that commutes with `α` satisfies
the Leibniz rule for `⋆` exactly when its Leibniz defect `E(x,y) = D(xy) - D(x)y - xD(y)`
satisfies `E(x,y) + α(E(y,x)) = 0`.  In particular every derivation commuting with
`α` is braided-symmetric.
-/

namespace Research.BraidedSymInc

variable {A : Type*} [Ring A]

/-- Leibniz defect of an additive map. -/
def defect (D : A →+ A) (x y : A) : A := D (x * y) - D x * y - x * D y

/-- The twisted product `x ⋆ y = x * y + α (y * x)`. -/
def twist (α : A →+* A) (x y : A) : A := x * y + α (y * x)

/-- Key identity: the Leibniz discrepancy for the twisted product is the defect expression. -/
theorem leibniz_discrepancy (α : A →+* A) (D : A →+ A) (hD : ∀ x, D (α x) = α (D x))
    (x y : A) :
    D (twist α x y) - (twist α (D x) y + twist α x (D y))
      = defect D x y + α (defect D y x) := by
  simp only [twist, defect, map_add, map_sub, hD]
  simp only [map_mul]
  abel

/-- Lemma 2.3: the braided-symmetric Leibniz rule is equivalent to the defect relation. -/
theorem bs_iff_defect (α : A →+* A) (D : A →+ A) (hD : ∀ x, D (α x) = α (D x)) :
    (∀ x y, D (twist α x y) = twist α (D x) y + twist α x (D y)) ↔
      ∀ x y, defect D x y + α (defect D y x) = 0 := by
  constructor
  · intro h x y
    rw [← leibniz_discrepancy α D hD x y, h x y, sub_self]
  · intro h x y
    have := leibniz_discrepancy α D hD x y
    rw [h x y] at this
    exact sub_eq_zero.mp this

/-- Every derivation that commutes with `α` is braided-symmetric. -/
theorem derivation_is_bs (α : A →+* A) (D : A →+ A) (hD : ∀ x, D (α x) = α (D x))
    (hder : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∀ x y, D (twist α x y) = twist α (D x) y + twist α x (D y) := by
  rw [bs_iff_defect α D hD]
  intro x y
  have h1 : defect D x y = 0 := by
    simp only [defect, hder x y]
    abel
  have h2 : defect D y x = 0 := by
    simp only [defect, hder y x]
    abel
  rw [h1, h2, map_zero, add_zero]

end Research.BraidedSymInc
