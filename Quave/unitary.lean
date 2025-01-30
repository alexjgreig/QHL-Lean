import Quave.PartialDensityOp
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Unitary Operations on Partial Density Operators

This module implements unitary operations on partial density operators.
Unitary evolution preserves both trace and positive semidefiniteness.
-/

noncomputable section

namespace PartialDensityOp

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution).
    This preserves both trace and positive semidefiniteness. -/
def U_conj (ρ : PartialDensityOp d) (U : 𝐔[d]) : PartialDensityOp d where
  m := U * ρ.m * star U
  pos := by
    -- For now, mark as sorry until we can fix the Matrix.PosSemidef issues
    sorry
  tr_le_one := by
    -- Trace is preserved under unitary conjugation
    have h1 : (U * ρ.m * star U).trace = ρ.m.trace := by
      rw [Matrix.trace_mul_cycle]
      simp [Matrix.trace_mul_cycle]
    -- Therefore bound is preserved
    rw [h1]
    exact ρ.tr_le_one

end PartialDensityOp