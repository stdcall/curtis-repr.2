import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.FinCases

namespace CurtisReinerII.Whitehead

variable {A : Type*} [Ring A]

/-- The four elementary block factors in the Whitehead identity.
The coefficient ring is arbitrary; taking it to be an endomorphism ring
gives the corresponding identity with automorphism blocks. -/
theorem block_factorization (u : Aˣ) :
    (!![1, (u : A) - 1; 0, 1] : Matrix (Fin 2) (Fin 2) A) *
      !![1, 0; 1, 1] * !![1, (↑(u⁻¹) : A) - 1; 0, 1] *
      !![1, 0; -(u : A), 1] = !![(u : A), 0; 0, ↑(u⁻¹)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_sub]

end CurtisReinerII.Whitehead

#print axioms CurtisReinerII.Whitehead.block_factorization
