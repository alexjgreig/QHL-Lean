import Quave.DensityOp

noncomputable section

namespace DensityOp

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def U_conj (ρ : DensityOp d) (U : 𝐔[d]) : DensityOp d where
  m := U * ρ.m * star U
  tr := by simp [Matrix.trace_mul_cycle, ρ.tr]
  pos := ⟨by simp [Matrix.IsHermitian, ρ.pos.1.eq, Matrix.star_eq_conjTranspose, mul_assoc],
    by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    convert ρ.pos.2 (Matrix.mulVec (↑(star U)) x)
    simp [Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    ⟩

end DensityOp
