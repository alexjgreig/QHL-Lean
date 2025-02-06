import Quave.partialdensityop
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
-- import Mathlib.Algebra.BigOperators.Basic
import Quave.qtype
import Quave.quantum

/-!
# Unitary Operations for Quantum Program Verification

This module implements unitary operations for the qWhile+ language as specified in the quantum
program verification framework. Unitary operations are fundamental to quantum computation,
representing reversible quantum transformations.

## Main Concepts

* Unitary operators preserve the inner product between quantum states
* A matrix U is unitary if U†U = I (where U† is the conjugate transpose)
* Unitary operations are used to implement quantum gates in the qWhile+ language

## Implementation Notes

1. Basic unitary operations:
   * Single-qubit gates (X, Y, Z, H, etc.)
   * Two-qubit gates (CNOT, etc.)
   * Parameterized gates (rotation gates)

2. Composition operations:
   * Tensor products for parallel composition
   * Matrix multiplication for sequential composition
   * Controlled operations for conditional quantum operations

3. Properties maintained:
   * Unitarity (U†U = I)
   * Trace preservation
   * Positive semidefiniteness
-/

namespace unitary

noncomputable section

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]

/-- Verifies if a matrix is unitary by checking U†U = I.
    This is a fundamental property required for all quantum gates in qWhile+.

    Arguments:
    * `U` - The matrix to check for unitarity

    Returns: A proposition that is true iff U is unitary -/
def is_unitary {n : Nat} (U : Fin n → Fin n → ℂ) : Prop :=
  ∀ i j, ∑ k, U k i * qtype.conj (U k j) = if i = j then 1 else 0

/-- Computes the tensor product of two quantum states.
    This operation is essential for describing composite quantum systems in qWhile+.

    Arguments:
    * `ψ₁` - First quantum state
    * `ψ₂` - Second quantum state

    Returns: The tensor product state in the composite system -/
def tensor_product {n m : Nat} (ψ₁ : Fin n → ℂ) (ψ₂ : Fin m → ℂ) :
    Fin (n * m) → ℂ := fun i =>
  let i₁ := Fin.mk (i.val / m) (by sorry)  -- First system index
  let i₂ := Fin.mk (i.val % m) (by sorry)  -- Second system index
  ψ₁ i₁ * ψ₂ i₂

/-- Computes the tensor product of two unitary operators.
    Used to construct parallel quantum operations in qWhile+.

    Arguments:
    * `U₁` - First unitary operator
    * `U₂` - Second unitary operator

    Returns: The tensor product operator acting on the composite system -/
def tensor_product_op {n m : Nat} (U₁ : Fin n → Fin n → ℂ) (U₂ : Fin m → Fin m → ℂ) :
    Fin (n * m) → Fin (n * m) → ℂ := fun i j =>
  let i₁ := Fin.mk (i.val / m) (by sorry)
  let i₂ := Fin.mk (i.val % m) (by sorry)
  let j₁ := Fin.mk (j.val / m) (by sorry)
  let j₂ := Fin.mk (j.val % m) (by sorry)
  U₁ i₁ j₁ * U₂ i₂ j₂

/-- Creates a controlled version of a unitary operator.
    This implements the controlled gates in qWhile+, where one qubit controls
    the application of a unitary operation on target qubits.

    Arguments:
    * `U` - The unitary operator to be controlled

    Returns: A new unitary operator representing the controlled operation -/
def controlled {n : Nat} (U : Fin n → Fin n → ℂ) :
    Fin (2 * n) → Fin (2 * n) → ℂ := fun i j =>
  let control := Fin.mk (i.val / n) (by sorry)
  let target := Fin.mk (i.val % n) (by sorry)
  let j_control := Fin.mk (j.val / n) (by sorry)
  let j_target := Fin.mk (j.val % n) (by sorry)
  if control = (0 : Fin 2) then
    if control = j_control then
      if target = j_target then 1 else 0
    else 0
  else  -- control = 1
    if control = j_control then
      U target j_target
    else 0

/-- Computes the adjoint (conjugate transpose) of a unitary operator.
    Required for verifying unitarity and implementing quantum measurements.

    Arguments:
    * `U` - The unitary operator

    Returns: The adjoint operator U† -/
def adjoint {n : Nat} (U : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := fun i j =>
  qtype.conj (U j i)

/-- Composes two unitary operators through matrix multiplication.
    Implements sequential composition of quantum operations in qWhile+.

    Arguments:
    * `U₁` - First unitary operator
    * `U₂` - Second unitary operator

    Returns: The composed operator U₁U₂ -/
def compose {n : Nat} (U₁ U₂ : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := fun i j =>
  ∑ k, U₁ i k * U₂ k j

/-- Applies a unitary operator to a quantum state.
    This is the core operation for implementing quantum gates in qWhile+.

    Arguments:
    * `U` - The unitary operator to apply
    * `ψ` - The quantum state

    Returns: The transformed quantum state U|ψ⟩ -/
def apply_unitary {n : Nat} (U : Fin n → Fin n → ℂ) (ψ : Fin n → ℂ) : Fin n → ℂ := fun i =>
  ∑ j, U i j * ψ j

/-- Conjugates a density operator by a unitary matrix.
    This operation represents the evolution of mixed quantum states under unitary operations.

    Arguments:
    * `ρ` - The density operator
    * `U` - The unitary operator

    Returns: The transformed density operator UρU† -/
def U_conj (ρ : partialdensityop.PartialDensityOp d) (U : 𝐔[d]) : partialdensityop.PartialDensityOp d where
  m := U * ρ.m * star U
  pos := by sorry  -- For now, mark as sorry until we can fix the Matrix.PosSemidef issues
  tr_le_one := by
    -- Trace is preserved under unitary conjugation
    have h1 : (U * ρ.m * star U).trace = ρ.m.trace := by
      rw [Matrix.trace_mul_cycle]
      simp [Matrix.trace_mul_cycle]
    -- Therefore bound is preserved
    rw [h1]
    exact ρ.tr_le_one

end

end unitary
