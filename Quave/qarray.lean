import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Kronecker
import Quave.qtype
import Quave.partialdensityop
import Quave.unitary
import Quave.measurement
import Quave.Basic
import Quave.env
import Quave.quantum

/-!
# Quantum Arrays for qWhile+ Program Verification

This module implements quantum arrays as specified in the qWhile+ language for quantum program
verification. Quantum arrays are a fundamental construct that allows quantum variables to be
indexed by classical expressions.

## Main Concepts

* Quantum Arrays: Variables of type T₁ × ... × Tₙ → H where:
  - Each Tᵢ is a classical type for indexing
  - H is a Hilbert space for quantum states
* Subscripted Variables: Expressions like q[s₁, ..., sₙ] where:
  - q is a quantum array
  - Each sᵢ is a classical expression
* Distinctness: A predicate ensuring quantum variables are distinct during operations

## Implementation Notes

1. Array Structure:
   * Arrays map classical indices to quantum subsystems
   * Each element represents an independent quantum state
   * Support for multi-qubit operations across elements

2. Operations:
   * Initialization to |0...0⟩ state
   * Single-qubit gate application
   * Two-qubit gate application
   * Measurement in computational basis

3. Verification Support:
   * Distinctness checking for quantum operations
   * State normalization invariants
   * Type safety for classical indices
-/

noncomputable section

open Classical BigOperators Complex qtype partialdensityop Matrix Kronecker

namespace qarray

/-- A quantum array represents a collection of qubits with a fixed size.
    This implements the array quantum variables from qWhile+.

    Fields:
    * `state` - The quantum state vector in the 2^n dimensional Hilbert space
    * `names` - A vector of variable names that map to each qubit in the array.
    * `is_normalized` - Proof that the state is normalized (sum of probabilities = 1) -/
structure QArray (n : Nat) where
  state : Fin (2^n) → ℂ  -- The quantum state of n qubits
  names: Vector (String) n
  is_normalized : ∑ i, (state i * qtype.conj (state i)).re = 1

/-- Creates a new quantum array initialized to the |0...0⟩ state.
    This implements the quantum initialization q := |0⟩ in qWhile+.

    Arguments:
    * `n` - Number of qubits in the array

    Returns: A new QArray with all qubits in the |0⟩ state -/
def init (n : Nat) : QArray n :=
{ state := fun i => if i = 0 then 1 else 0,
  names := Vector.ofFn (fun i => s!"q{i}"),
  is_normalized := by sorry }  -- Proof that state is normalized

/-- Applies a single-qubit gate to a specific qubit in the array.
    This implements the gate application U[q] in qWhile+ for single-qubit gates.

    Arguments:
    * `arr` - The quantum array to modify
    * `gate` - The single-qubit gate to apply
    * `target` - Index of the target qubit

    Returns: The modified quantum array after gate application -/
def apply_single {n : Nat} (arr : QArray n) (gate : Fin 2 → Fin 2 → ℂ)
    (target : Fin n) : QArray n :=
{ state := fun i =>
    let target_bit := (i / (2^target.val)) % 2  -- Extract target qubit
    let new_state := quantum.apply_gate gate (fun j =>
      if j = 0 then
        if target_bit = 0 then arr.state i else 0
      else
        if target_bit = 1 then arr.state i else 0)
    new_state target_bit,
  names := arr.names,
  is_normalized := by sorry }  -- Proof that resulting state is normalized

/-- Applies a two-qubit gate to specific qubits in the array.
    This implements the gate application U[q₁,q₂] in qWhile+ for two-qubit gates.

    Arguments:
    * `arr` - The quantum array to modify
    * `gate` - The two-qubit gate to apply
    * `control` - Index of the control qubit
    * `target` - Index of the target qubit

    Returns: The modified quantum array after gate application -/
def apply_two {n : Nat} (arr : QArray n) (gate : Fin 4 → Fin 4 → ℂ)
    (control target : Fin n) : QArray n :=
{ state := fun i =>
    let control_bit := (i / (2^control.val)) % 2
    let target_bit := (i / (2^target.val)) % 2
    let gate_input := control_bit * 2 + target_bit
    ∑ j, gate gate_input j * arr.state i,
  names := arr.names,
  is_normalized := by sorry }  -- Proof that resulting state is normalized

/-- Measures a specific qubit in the computational basis.
    This implements the measurement operation x := M[q] in qWhile+.

    Arguments:
    * `arr` - The quantum array to measure
    * `target` - Index of the qubit to measure
    * `outcome` - The measurement outcome (0 or 1)

    Returns: A pair containing:
    * The probability of the measurement outcome
    * The post-measurement quantum array -/
def measure {n : Nat} (arr : QArray n) (target : Fin n) (outcome : Fin 2) :
    ℝ × QArray n :=
  let prob := ∑ i, if (i / (2^target.val)) % 2 = outcome then
                    (arr.state i * qtype.conj (arr.state i)).re
                  else 0
  let new_state : Fin (2^n) → ℂ := fun i =>
    if (i / (2^target.val)) % 2 = outcome then
      arr.state i / Real.sqrt prob
    else 0
  let post_state : QArray n := {
    state := new_state,
    names := arr.names,
    is_normalized := by sorry  -- Proof that new state is normalized
  }
  (prob, post_state)

/-- Gets the probability amplitude of a specific basis state.
    Used for analyzing and verifying quantum states.

    Arguments:
    * `arr` - The quantum array
    * `basis_state` - The computational basis state to query

    Returns: The complex amplitude ⟨basis_state|ψ⟩ -/
def get_amplitude {n : Nat} (arr : QArray n) (basis_state : Fin (2^n)) : ℂ :=
  arr.state basis_state

/-- Creates a quantum array in a specific basis state.
    Used for initializing quantum arrays to particular computational basis states.

    Arguments:
    * `basis_state` - The desired computational basis state

    Returns: A new QArray initialized to the specified basis state -/
def from_basis {n : Nat} (basis_state : Fin (2^n)) : QArray n :=
{ state := fun i => if i = basis_state then 1 else 0,
  names := Vector.ofFn (fun i => s!"q{i}"),
  is_normalized := by sorry }  -- Proof that state is normalized


/- Get the values partial density operator from the quantum register by using projection of the pure state-/
def pdo_from_qarray {n: Nat} (arr: QArray n) : partialdensityop.PartialDensityOp (Fin n) :=
  by sorry

def distinctness {n: Nat} {k: Nat} (systems: Vector (QArray n) k) : Bool :=
∀ (i: Fin k) (j: Fin k), systems[i.val] = systems[j.val] → ∃ (l: Fin n), systems[i.val].names[l.val] ≠ systems[j.val].names[l.val]


end qarray
