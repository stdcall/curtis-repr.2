import Mathlib.Tactic.Abel

/-!
Two additive steps in the localization proof of Section38D.
The module and lattice constructions supplying the hypotheses are not
formalized here. In particular these are not proofs of the full
localization sequence or of the existence of its boundary map.
-/

namespace CurtisReinerII.Localization

variable {A : Type*} [AddCommGroup A]

/-- The identical intersection defect cancels between the two rows. -/
theorem common_defect_cancellation
    (m₂ l₂ n₂ m₁ l₁ n₁ h : A)
    (lower : m₂ = l₂ + n₂ + h)
    (upper : m₁ = l₁ + n₁ + h) :
    m₂ - m₁ = (l₂ - l₁) + (n₂ - n₁) := by
  rw [lower, upper]
  abel

/-- Transitivity determines the sign of the final boundary representative. -/
theorem relative_boundary_sign
    (q_p p_image q_image : A)
    (transitivity : q_image = q_p + p_image)
    (image_zero : q_image = 0) :
    q_p = -p_image := by
  have relation : q_p + p_image = 0 := transitivity.symm.trans image_zero
  exact eq_neg_of_add_eq_zero_left relation

end CurtisReinerII.Localization

#print axioms CurtisReinerII.Localization.common_defect_cancellation
#print axioms CurtisReinerII.Localization.relative_boundary_sign
