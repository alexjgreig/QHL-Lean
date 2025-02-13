import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Partial Density Operators

This module implements partial density operators for quantum states in qWhile+.

## Mathematical Background

A partial density operator ρ has the following properties:
1. Trace(ρ) ≤ 1 (sub-normalization)
2. ρ is positive semidefinite
3. ρ is Hermitian (follows from positive semidefinite)

For a quantum state described by ρ:
* tr(ρ) gives the probability of reaching this state
* ρ/tr(ρ) gives the normalized state when reached
-/

noncomputable section

open Classical BigOperators ComplexConjugate Kronecker Matrix
open scoped Matrix ComplexOrder



namespace partialdensityop

/-- A partial density operator represents a quantum state with probability tr(ρ) ≤ 1.
    When normalized by tr(ρ), it gives the actual quantum state. -/
structure PartialDensityOp (d : Type*) [Fintype d] where
  /-- The underlying matrix representation -/
  m : Matrix d d ℂ
  /-- Proof that the matrix is positive semidefinite -/
  pos : m.PosSemidef
  /-- Proof that the trace is at most 1 (sub-normalization) -/
  tr_le_one : m.trace.re ≤ 1

variable {d d₁ d₂: Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂]

/-- Every partial density operator is Hermitian (self-adjoint) -/
theorem Hermitian (ρ : PartialDensityOp d) : ρ.m.IsHermitian :=
  ρ.pos.left

/-- Get the probability of reaching this state -/
def prob (ρ : PartialDensityOp d) : ℝ := ρ.m.trace.re

/-- Get the normalized state ρ/tr(ρ) when probability is non-zero -/
def normalize (ρ : PartialDensityOp d) (h : prob ρ ≠ 0) : PartialDensityOp d where
  m := (1/(prob ρ)) • ρ.m
  pos := sorry  -- TODO: Need to prove (1/prob)•ρ is PSD
  tr_le_one := sorry  -- TODO: Need to prove trace becomes 1

def prod (ρ₁ : PartialDensityOp d₁) (ρ₂ : PartialDensityOp d₂) : PartialDensityOp (d₁ × d₂) where
  m := ρ₁.m ⊗ₖ ρ₂.m
  pos := by sorry
  tr_le_one := by sorry

notation ρL "⊗" ρR => prod ρL ρR


end partialdensityop
