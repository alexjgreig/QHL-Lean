import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

/-
- Density operator is a square matrix that represents ∑ p_i |φ⟩⟨φ|
- Trace of density operator is 1 and it is Positive-Semi Definite
-/
structure DensityOp (d : Type*) [Fintype d] where
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1

namespace DensityOp

variable {d: Type*} [Fintype d]

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : DensityOp d) : ρ.m.IsHermitian :=
  ρ.pos.left

end DensityOp
